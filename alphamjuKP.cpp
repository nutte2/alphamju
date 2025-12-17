/*
   Alphamju - on the way to a single Dummy Solver
   Copyright (C) 2025 by Kalle Prorok

   WORK IN PROGRESS - BUT SLOW

   Based on the paper
   The alpha mju Search Algorithm for the Game of Bridge (greek letters replaced)
   Tristan Cazenave and Veronique Ventos 2019

   Uses DDS, a bridge double dummy solver 
   by Bo Haglund & Soren Hein.

   See LICENSE and README.
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "include/dll.h"
#include "hands.h"
#include <set>
#include <list>
#include <stack>
#include <chrono>
#include <map>
#include <algorithm>
#include <execution>
#include <filesystem>

#include <ppl.h>
using namespace concurrency;
#include <omp.h>
#include "hands_code.h" // To get definitions and useful functions

using namespace std;
using namespace std::chrono;
namespace fs = std::filesystem;

int WORLDSIZE = 4;// 8; // Actual dynamic number of deals
#define MWORLDSIZE MAXNOOFBOARDS // Max worldsize, same as in DDS

//#define MPREV 0 // How many M's should be shown before end; 0 = no, 1 = one at M-1, 2 gets a lot of text

char Worlds[MWORLDSIZE][130] = { // Store all the hands as PBN

"W:.765.765.8 .AJT.AJT.A .Q43.Q32.7 .K98.K98.K",
"W:.Q76.765.8 .AJT.AJT.A .432.Q32.7 .K98.K98.K",
"W:.765.Q76.8 .AJT.AJT.A .Q43.432.7 .K98.K98.K",
"W:.Q76.Q76.8 .AJT.AJT.A .432.432.7 .K98.K98.K"

//"W:4.Q.. .J..T .T..6 .K..K"      ,
//"W:4.T.. .J..T .Q..6 .K..K"      ,
//"W:4...6 .J..T .QT.. .K..K"

/* W:JT9.Q54.T.2 65.AJT9.65. 32.32.843.3 AK.K876.AK."      , // Default deals if none are given
"W:JT98.54.T.2 65.AJT9.65. 2.Q32.843.3 AK.K876.AK."      ,
"W:JT9.Q53.T.2 65.AJT9.65. 32.42.843.3 AK.K876.AK."      ,
"W:JT98.53.T.2 65.AJT9.65. 2.Q42.843.3 AK.K876.AK."      ,

"W:JT9.Q54.T.2 65.AJT9.65. 32.32.432.3 AK.K876.AK."      ,
"W:JT98.54.T.2 65.AJT9.65. 2.Q32.432.3 AK.K876.AK."      ,
"W:JT9.Q53.T.2 65.AJT9.65. 32.42.432.3 AK.K876.AK."      ,
"W:JT98.53.T.2 65.AJT9.65. 2.Q42.432.3 AK.K876.AK."      , */

//"W:JT98.Q54.JT9.JT9 765.AJT9.765.765 432.32.8432.8432 AKQ.K876.AKQ.AKQ"      ,
//"W:JT984.54.JT9.JT9 765.AJT9.765.765 32.Q32.8432.8432 AKQ.K876.AKQ.AKQ"      ,
//"W:.Q76.K.9 .AJT.A.A .543.J.8 .K98.5.5"      ,
//"W:.543.K.9 .AJT.A.A .Q76.J.8 .K98.5.5"      ,
//  "W:.Q76.. .AJT.. .543.. .K98.."      ,
//  "W:.543.. .AJT.. .Q76.. .K98.."      ,
};

unsigned int holdingsc[MWORLDSIZE][DDS_HANDS][DDS_SUITS]; // Store all the hands as BIN
// Some default values if no parameters are given
int cards = 7;// 8; // No of cards in each Deal
int contract = 7; // 8; // 12;
int trumpc = NOTRUMP; //HEARTS; //  NOTRUMP;
int M0 = 11; // Global - user setting of M to start. Default value
int L = 0; // Level of trace-prints from selected cards
#define LOPFILE "lop00.txt"
FILE* LOP; // File for logging Line of Play
#define PRETTYFILE "deal00.txt"

struct State
{
    bool Min_node;
    short declarerTricks;
    short defenseTricks;
    short handtoplay;
//    short handsplayed;
    short firstc;
    short playno;
    short playSuit[3];
    short playRank[3];
    short playedby[3];
    unsigned int mask[4][4]; // All played cards up to now
};

struct Card
{
    short suit; 
    short rank;
    short player;
};

struct Result // Store 0 or 1 if contract fail or succced in world-index. x == not possible world for a card
{
    char r[MWORLDSIZE+1]; // Result, add one extra for \0
//    char m[WORLDSIZE+1]; // Mask for possible worlds - removed and use 1x0 as r instead; maybe use?
    struct Card card; // Store card resulting in this
};

inline bool operator<(const Result& L, const Result& R)
{
    return L.r[0] < R.r[0];
}

struct Playable // Card possible to play in world
{
    short world;
    struct Card c;
};

inline bool operator<(const Card& L, const Card& R)
{
    if (L.suit < R.suit)
        return true;
    else if (L.suit > R.suit)
        return false;
    else if (L.rank < R.rank)
        return true;
    else return false;
}

void clearresult(Result& r)
{
    for (int i = 0; i < MWORLDSIZE; i++) // All of them; maybe WORLDSIZE would be enough
        r.r[i] = 'x'; // Assume everything is unknown yet
    r.r[MWORLDSIZE] = '\0'; // End of string for printing
}

inline bool operator==(const Result& L, const Result& R) // def needed for list of result
{
    for (int i = 0; i < WORLDSIZE; i++)
        if (L.r[i] != R.r[i])
            return false;
    return true;
}

set<Playable> legalMoves(short int world, State& state)
{ // Find a list of possible moves
    set<Playable> moves;
    Playable p;
    p.world = world;
    if (state.playno > 0 && (holdingsc[world][state.handtoplay][state.playSuit[0]] & ~state.mask[state.handtoplay][state.playSuit[0]]) > 0)
//        if (state.playno > 0 && holdingsc[world][state.handtoplay][state.playSuit[0]] > 0)
        { // There has been card played; if possible: Follow suit
        short int s = state.playSuit[0];
        p.c.suit = s;
        p.c.player = state.handtoplay;
        unsigned int m = RA;
        bool adjacent = false;
        for (int r = 14; r > 1; r--) // Probably can be done quicker than try&error if a card exists..
        {
            if ((holdingsc[world][state.handtoplay][s] & ~state.mask[state.handtoplay][s] ) & m)
            {
                if (!adjacent) // Skip nearby cards like T if J is already listed/tried
                {
                    p.c.rank = r;
                    p.world = world;
                    moves.insert(p);
                    adjacent = true;
                }
            }
            else adjacent = false;
            m >>= 1;
        }
    }
    else // Leading any of avalailable cards
    {
        for (short int s = 0; s < 4/*DDS_SUITS*/; s++)
            {
                p.c.suit = s;
                p.c.player = state.handtoplay;
                unsigned int m = RA;
                bool adjacent = false;
                for (int r = 14; r >1; r--)
                {
                    if ((holdingsc[world][state.handtoplay][s] & ~state.mask[state.handtoplay][s]) & m)
                    {
                        if (!adjacent)
                        {
                            p.c.rank = r; 
                            p.world = world;
                            moves.insert(p);
                            adjacent = true;
                        }
                    }
                    else adjacent = false;
                    m >>= 1;
                }
            }
    }
    return moves;
}

inline bool operator<(const Playable& L,const Playable& R)
{ // needed for Playble list/set
    if (L.c.suit < R.c.suit)
        return true;
    else if (L.c.suit > R.c.suit)
        return false;
    else if (L.c.rank < R.c.rank)
        return true;
    else if (L.c.rank > R.c.rank)
        return false;
    else if (L.world < R.world)
        return true;
    else return false;
}


int init()
{
    for (int i =0; i< WORLDSIZE; i++)
        ConvertPBN(Worlds[i], holdingsc[i]); // Translate PBN to BIN representation (from hands.cpp)
    return 0;
}

void binprint(int v)
{
    unsigned int mask = 1 << ((sizeof(int) << 3) - 1);
    while (mask) {
        printf("%d", (v & mask ? 1 : 0));
        mask >>= 1;
    }
}

void printworlds(set<short int> worlds)
{
    for (short int w : worlds)
        printf("(W%d) ", w);
}
void printresult(Result& elem)
{
    printf("[");
    for (int i=0;i<WORLDSIZE;i++)
        printf("%c", elem.r[i]);
    printf("]");
}

void printresults(list<Result>& r, const char msg[])
{
    printf("%s:<", msg);
    for (Result elem : r) printresult(elem);
    printf(">");
}

void showcard(short int suit, short int rank)
{
    printf("Play %c%c ", "SHDC"[suit], dcardRank[rank]);
}

void showcard2(short int suit, short int rank)
{
    printf("%c%c", "SHDC"[suit], dcardRank[rank]);
}

void showmove(Playable move)
{
    showcard(move.c.suit, move.c.rank);
}

int doubleDummy(short int world, const State state,int threadIndex)
{
    deal dl;
    futureTricks fut; 
    int target;
    int solutions;
    int mode;
    int res;
    char line[80];// , lin[80];
    strcpy_s(line, 80, "DD:"); //Double Dummy result
    dl.trump = trumpc;// [handno] ;
    dl.first = state.firstc; 

    dl.currentTrickSuit[0] = state.playSuit[0]; 
    dl.currentTrickSuit[1] = state.playSuit[1];  
    dl.currentTrickSuit[2] = state.playSuit[2];

    dl.currentTrickRank[0] = state.playRank[0]; 
    dl.currentTrickRank[1] = state.playRank[1]; 
    dl.currentTrickRank[2] = state.playRank[2];
   // showcard(state.playSuit[0], state.playRank[0]);
        for (int h = 0; h < DDS_HANDS; h++)
            for (int s = 0; s < DDS_SUITS; s++)
                dl.remainCards[h][s] = holdingsc[world][h][s] & ~state.mask[h][s]; // Remove played cards

    target = -1;    solutions = 1;    mode = 1;
    res = SolveBoard(dl, target, solutions, mode, &fut, threadIndex); // Call DDS.DLL
 //    if (world == 0)
  //       printf("W%d:%d!", world, fut.score[0]);

    if (res != RETURN_NO_FAULT)
    {
        ErrorMessage(res, line);
        printf("DDS error: %s\n", line);
        printf(" first:%c Wrong hand:", "NESW"[dl.first]);
        PrintHand(line, dl.remainCards);
    }
//    printf("DD in World %d: \n", world);
//    PrintFut(line, &fut);
//    PrintHand(line, dl.remainCards);
    return fut.score[0]; // Return number of tricks for hand to play
}

int cardsleft(State& state)
{
    return cards - state.declarerTricks - state.defenseTricks;
}

double score(list<Result> r)
{
    int ok = 0, fail = 0;
    double nvec = 0.0;
    for (const Result& ri : r)
    {
        for (int i = 0; i < WORLDSIZE; i++)
            if (ri.r[i] == '1')
                ok++;
            else if (ri.r[i] == '0')
                fail++;
        nvec++;
    }
    if (ok+fail > 0)
//        return ((100.0 * ok) / (WORLDSIZE * nvec)); // How to use x?
    return ((100.0 * ok) / (1.0 * ok + 1.0 * fail));//WORLDSIZE * nvec));
    else return -1;
}

struct Worldpair
{
    short w;
    int ix;
};

bool stopc(State& state, int M, set<short int>& worlds, Result& result)
{ // stop if now succeeded or failed - otherwise use DD if M =  0
    if (state.declarerTricks >= contract)
    {
        for (short int w : worlds)
        {
            result.r[w] = '1';
        }
        return true;
    }
    else if (state.defenseTricks > cards - contract)
    {
        for (short int w : worlds)
        {
            result.r[w] = '0'; // result.m[w] = '1';
        }
        return true;
    }
//    else if (M == 0)
    else if (M <= 0 || cardsleft(state) <= 1)
    {

        bool still_remain = true; // Remaining worlds to handle
        set<short int>::iterator itr;
        itr = worlds.begin();
        while (still_remain) // Split upp all into <16-chunks with threadix 0..<=15
        {
            int maxi = 0;
            list<Worldpair> worldps;

            while (still_remain && maxi < 16)
            {
                if (itr != worlds.end())
                {
                    Worldpair wp;
                    wp.w = *itr; // w real world number
                    wp.ix = maxi; // threadID 0..15
                    worldps.push_back(wp);
                    itr++;
                    maxi++;
                }
                else {
                    still_remain = false;
                }

            }
            parallel_for_each(begin(worldps), end(worldps), [&](Worldpair wi) // Run in parallel, max 16 threads
                {
                    int tricks;
                    int ns_tricks, ew_tricks;
                    //                    printf("Trying w%d? ", wi);
                    tricks = doubleDummy(wi.w, state, wi.ix);
//                                      printf(" %d:%d tricks!", wi.w, tricks);
                    if (state.Min_node)
                    {
                        ns_tricks = cardsleft(state) - tricks;
                        ew_tricks = tricks;
                    }
                    else
                    {
                        ns_tricks = tricks;
                        ew_tricks = cardsleft(state) - tricks;
                    }
                    if (state.declarerTricks + ns_tricks >= contract)
                    {
                        result.r[wi.w] = '1';
                    }
                    else
                    {
                        result.r[wi.w] = '0';
                    }
                    //            printf("DD:%d; NS took %d tricks and EW %d in W%d.\n", tricks,state.declarerTricks + ns_tricks,
                    //                state.defenseTricks+ew_tricks,w);
                });

        }
    
    
//        printworlds(worlds);
//        printresult(result);
        return true;
    }
    else return false;
}

bool dominate(const Result& L, const Result& R) // Return true if L dominate (is always >=) R
{
    bool none_yet = true; // Is no one item strictly larger yet?
    for (int i = 0; i < WORLDSIZE; i++)
    {
        if ((L.r[i] == 'x' && R.r[i] != 'x') || (L.r[i] != 'x' && R.r[i] == 'x'))
                   return false; // Not the same world-set
        if (L.r[i] == '0' && R.r[i] == '1')
        {
            return false;
        }
        else if (L.r[i] == '0' && R.r[i] == 'x')
        {
            return false;
        }
        else if (L.r[i] == 'x' && R.r[i] == '1') // If any world is better it doesn't dominate
            return false;
        else if ( none_yet &&  // 1 > x > 0
            (
            (L.r[i] == '1' && (R.r[i] == '0' || R.r[i] == 'x')) || 
            (L.r[i] == 'x' && R.r[i] == '0'))
                )
            none_yet = false; // Found a strictly larger element
    }
    if (none_yet)
        return false;
    else return true;
}

bool lte(const list<Result>& front, const list<Result> f)
{
    //TODO - not used
    return true;
}

bool notin(const list<Result>& outresult, Result r)
{
    for (const Result& f : outresult)
        if (f == r)
            return false;
    return true;
}

bool strictlylarger(const Result& L, Result& R) // L is > R
{
    bool atleastone = false;
    for (int i = 0; i < WORLDSIZE; i++)
    {
        if (L.r[i] == '0' && R.r[i] == '1')
            return false;
        else if (L.r[i] == '1' && R.r[i] == '0')
            atleastone = true;
        else if (L.r[i] == 'x' && R.r[i] != 'x') // Not equal worlds
            return true;
        else if (L.r[i] != 'x' && R.r[i] == 'x') // Not equal worlds
            return true;
    }
    if (atleastone) return true;
    else return false;
}

bool lessthanorequal(const Result& L, Result& R) // L is <= R
{
    //bool atleastone = false;
    for (int i = 0; i < WORLDSIZE; i++)
    {
        if (L.r[i] == '1' && R.r[i] == '0')
            return false;
//        else if (L.r[i] == '1' && R.r[i] == '0')
//            atleastone = true;
//        else if (L.r[i] == 'x' && R.r[i] != 'x') // Not equal worlds
//            return false;
//        else if (L.r[i] != 'x' && R.r[i] == 'x') // Not equal worlds
//            return false;
//
    }
    return true;
//    if (atleastone) return true;
//    else return false;
}

bool largerorequal(const Result& L, Result& R) // L is <= R
{

    for (int i = 0; i < WORLDSIZE; i++)
    {
        if (L.r[i] == '0' && R.r[i] == '1')
            return false;
//        else if (L.r[i] == 'x' && R.r[i] != 'x') // Not equal worlds
  //          return false;
    //    else if (L.r[i] != 'x' && R.r[i] == 'x') // Not equal worlds
      //      return false;
    }
    return true;
}

list<Result> remove_vectors_lte(list<Result>& result, Result r)
{
    list<Result>outresult;
    if (!result.empty())
        for (const Result& f : result)
        {
    //        if (!dominate(r, f))
                if (!lessthanorequal(f, r)) // Don't bring the lessthan or equal; add the others
                    outresult.push_front(f);

        }
    return outresult;
}

bool no_vectorsfrom_gte(list<Result>& result, Result& r)
{
    if (result.empty()) return true; // None to be found
    for (const Result& f : result)
    {
       if (largerorequal(f, r))
          return false;
    }
    return true;
}

list<Result> minr(list<Result> front, list<Result> f)
// Join two pareto fronts at min node
{
    list<Result> result;
    Result r;
    //clearresult(result);
    if (front.empty()) return f;

    for (const Result& vecto : front) // mod
    {
        for (const Result& v : f) // mod
        {
            r.card = v.card;
            for (int w = 0; w < WORLDSIZE; w++)
            {
                if (vecto.r[w] == '0' || v.r[w] == '0')
                    r.r[w] = '0';// vecto.r[w];
                else if (vecto.r[w] == '1')
                    r.r[w] = '1';
                else if (vecto.r[w] == 'x')
                {
                    if (v.r[w] == 'x')
                        r.r[w] = '1'; // Unknown worlds returns 1 to protect higher level results
                    else r.r[w] = v.r[w];
                }
//                if (vecto.r[w] == '0' || (vecto.r[w] == 'x' && v.r[w] == '1')) // 0 x 1 order
//                    if (vecto.r[w] == '0' || (vecto.r[w] == 'x' && v.r[w] == '1')) // 0 x 1 order
                        //                  if (vecto.r[w] == '0')//|| (vecto.r[w] == 'x' &&  v.r[w] == '1')) // 0 x 1 order
//                        r.r[w] = vecto.r[w];
//                else
//                    r.r[w] = v.r[w];
            }
            r.r[WORLDSIZE] = '\0'; // End of string
            result = remove_vectors_lte(result, r); // r dominates some in result
//            if (no_vectorsfrom_gte(result, r) && r != v) 
            if (no_vectorsfrom_gte(result, r) ) // r is not dominated by some
            {
                result.push_back(r);
            }
        }

    }
    return result;
}

list<Result> maxr(list<Result>& front, list<Result>& f)
{
    bool inserted = false;
    list<Result> result(front); // Deepcopy list elements?
    for (const Result& fi : f)
        //            for (Result fi : f)
    {
        for (const Result& fr : front)
        {
            if (dominate(fi, fr))
            {
                result.remove(fr); // Modify in result list, not loop ix
//                result.insert(result.begin(), fi);
//                inserted = true;
            }
        }
    }
    if (!inserted) // Insert if not dominated and not equal
    {
        for (const Result& fi : f)
            //                for (Result fi : f)
        {
            bool quit = false;
            for (const Result& fr : front)
            {
                if (dominate(fr, fi) || fr == fi)
                {
                    quit = true;
                    break;
                }
            }
            if (!quit)
                result.insert(result.begin(), fi);
        }
    }
    return result;
}


State evaluate_trick(Card move, State state)
{ // A complete trick with 4 cards are played - find winner; next leader
    int winner, maxc = 0;
    if (trumpc == NOTRUMP)
    {
        maxc = state.playRank[0], winner = state.playedby[0];
        if (state.playSuit[1] == state.playSuit[0] && state.playRank[1] > maxc)
        {
            maxc = state.playRank[1]; winner = state.playedby[1];
        }
        if (state.playSuit[2] == state.playSuit[0] && state.playRank[2] > maxc)
        {
            maxc = state.playRank[2]; winner = state.playedby[2];
        }
        if (move.suit == state.playSuit[0] && move.rank > maxc)
        {
            maxc = move.rank; winner = move.player;
        }
        
    }
    else // Trump contract
    {
        if (state.playSuit[0] == trumpc || // Someone played a trump
            state.playSuit[1] == trumpc ||
            state.playSuit[2] == trumpc ||
            move.suit == trumpc)
        {
            if (move.suit == trumpc)
            {
                maxc = move.rank; winner = move.player;
            }

            for (int i=0;i<3;i++)
                if (state.playSuit[i] == trumpc && state.playRank[i] > maxc)
                {
                    maxc = state.playRank[i]; winner = state.playedby[i];
                }
        } 
        else // No one played any trump, same as above
        {
            maxc = state.playRank[0], winner = state.playedby[0];

            if (state.playSuit[1] == state.playSuit[0] && state.playRank[1] > maxc)
            {
                maxc = state.playRank[1]; winner = state.playedby[1];
            }
            if (state.playSuit[2] == state.playSuit[0] && state.playRank[2] > maxc)
            {
                maxc = state.playRank[2]; winner = state.playedby[2];
            }
            if (move.suit == state.playSuit[0] && move.rank > maxc)
            {
                maxc = move.rank; winner = move.player;
            }
        }
    }
//    printf("%c wins w %c%c\n", "NESW"[winner], "SHDC"[state.playSuit[0]], dcardRank[maxc]);

    if (winner == NORTH || winner == SOUTH)
    {
        state.declarerTricks++;
        state.Min_node = false;
    }
    else
    {
        state.defenseTricks++;
        state.Min_node = true;
    }
    state.firstc = state.handtoplay = winner;

    state.playno = 0;
    for (int i = 0; i < 3; i++)
    {
        state.playSuit[i] = 0;
        state.playRank[i] = 0;
    }
    return state;
}

State playc(Card move, State state)
{
    if (state.playno >= 3) // 4 cards have now been played in the trick
    {
        state.mask[move.player][move.suit] |= (1 << (move.rank));
        state = evaluate_trick(move, state);
    }
    else
    {
        state.playSuit[state.playno] = move.suit;
        state.playRank[state.playno] = move.rank;
        state.playedby[state.playno] = move.player;
        state.mask[move.player][move.suit] |= (1 << (move.rank));
        state.playno++;
        if (state.handtoplay < WEST)
            state.handtoplay++;
        else state.handtoplay = NORTH;

        if (state.Min_node)
            state.Min_node = false;
        else state.Min_node = true;
    }

    return state;
}

void printfc(int trick,Card c, list<Result>& fbef, list<Result>& front, list<Result>& f)
{
//    printf("%d;%c:%c%c%3.0f%%/%2.0f%% ", M, "NESW"[c.player], "SHDC"[c.suit], dcardRank[c.rank], score(f), score(front));
//    printresults(f, "f"); printresults(front, "fr");
    if (L>0)
        fprintf(LOP,"\n%d %c %c%c%4.0f", trick, "NESW"[c.player], "SHDC"[c.suit], dcardRank[c.rank], score(f) );
    if (trick == 1) 
    {
        printf("\n%d %c:%c%c%3.0f%% ", trick, "NESW"[c.player], "SHDC"[c.suit], dcardRank[c.rank], score(f));
        printresults(fbef, "fb"); printresults(f, "f");  printresults(front, "fr");
    }
}


list<Result> au(State state, int M, set<short int> worlds)
{
    Result result;
    clearresult(result);
//    printf("au(%d)", M);

    if (stopc(state, M, worlds, result))
    {
       list<Result> res;
       res.push_back(result);
       return res;
    }
    map<struct Card, set<short int>> playcards;
    map<struct Card, set<short int>>::iterator it_playcards;

    struct Card card;
    list<Result> front;
    list<Result> f;
    if (M >= (M0))
        printf("\n");

    if (state.Min_node)
    {
        set<Playable> allMoves;
        for (int w : worlds)
        {
            set<Playable> l;
            l.merge(legalMoves(w, state));
            allMoves.merge(l);
        }
        for (Playable move : allMoves)
        {
            card.suit = move.c.suit;
            card.rank = move.c.rank;
            card.player = move.c.player;
            playcards[card].insert(move.world);
        }
        if (playcards.begin() == playcards.end())
        {
            printf("No play at MIN!");
        }
        for (it_playcards = playcards.begin(); it_playcards != playcards.end(); it_playcards++)
        {
//            showcard(it_playcards->first.suit, it_playcards->first.rank);
            State s = playc(it_playcards->first, state);
            f = au(s, M, it_playcards->second);
          //  printresults(f, "f min");
       //     if (M >= (M0 - 1))
//                printresults(front, "front before min");

            for (Result fc : f)
            {
                fc.card = it_playcards->first; // Store card resulting in this
            }
//            list<Result> fbef = front;
//            front = minr(front, f);
            if (M > (M0 - L))
            {
                list<Result> fbef = front;
                front = minr(front, f);
                printfc(M0-M+1, it_playcards->first, fbef, front, f);
            } else
                front = minr(front, f);
                        
        //    printresults(front, "front after min");
        }

    }
    else // Max node
    {
        set<Playable> allMoves;
        set<Playable> leMoves;

        for (int w : worlds)
        {
            set<Playable> l;
            leMoves = legalMoves(w, state);
            if (leMoves.empty())
                printf("No moves at MAX ");
            l.merge(leMoves);
            allMoves.merge(l);
        }
        for (Playable move : allMoves)
        {
            card.suit = move.c.suit;
            card.rank = move.c.rank;
            card.player = move.c.player;
            playcards[card].insert(move.world); // List of worlds w playable card
        }
        State s;
        if (playcards.begin() == playcards.end())
        {
            printf("No play at MAX ");
        }
        for(it_playcards = playcards.begin(); it_playcards != playcards.end(); it_playcards++)
        {
            //            showcard(it_playcards->first.suit, it_playcards->first.rank);
            s = playc(it_playcards->first, state);
            f = au(s, M - 1, it_playcards->second);
            for (Result fc : f)
            {
                fc.card = it_playcards->first; // Store card resulting in this
            }

      //      printresults(f, "f max");
           //printresults(front, "front before max");
            list<Result> fbef = front;
            front = maxr(front, f);
            if (M > (M0 - L))
            {
                list<Result> fbef = front;
                front = maxr(front, f);
                printfc(M0-M+1, it_playcards->first, fbef, front, f);

            } else
                front = maxr(front, f);

          //  printresults(front, "front aftermax");
        } 

    }
//    if (M >= (M0))
//        printf("\n");
    return front;
    
}

State start; // Zero-start

#include <sstream>
#include <iostream>

void doimport(char* fn)  // Read deals from .PBN-file
{
    FILE* f;
    char inlin[130];
    int e = fopen_s(&f, fn, "r");
    if (e != NULL)
    {
        printf("*Could not open %s in ", fn);
        cout << fs::current_path();
        exit(-10); // File not found
    }
    else
    {
        int deal = 0;
        while (fgets(inlin, 128, f) != NULL && deal < MWORLDSIZE)
        {
            if (strncmp(inlin, "[Deal", 5) == 0) // Assume [Deal "W: 5.23. "]
            {
                if (inlin[6] == '"')
                {
                    char* ptr = strrchr(inlin, '"'); // Find position of ending "
//                    cout << ptr;
                    __int64 chars = ptr - (inlin + 6) -1;
//                    cout << chars;
                    strncpy_s(Worlds[deal], 128, inlin+7, chars);
                    ptr = strchr(inlin+7, ' ');
                    cards = int(ptr - (inlin + 7) - 5); // Find number of cards in the hand(s)
                    deal++;
                    WORLDSIZE = deal; // Update number of deals
                }
            }
        } 
        fclose(f);
    }
}

void testminr() // Test the pareto logic in minr() and maxr()
{
    list<Result> front;
    list<Result> f;
    WORLDSIZE = 3;
    Result r1;
    strcpy_s(r1.r, "011");
    front.push_back(r1);
    Result r2;
    strcpy_s(r2.r, "110");
    front.push_back(r2);

    Result r3;
    strcpy_s(r3.r, "110");
    f.push_back(r3);

    Result r4;
    strcpy_s(r4.r, "101");
    f.push_back(r4);

    list<Result> r;
    r = minr(front, f);

    printresults(front, "front");
    printresults(f, "f");
    printresults(r, "rmin");// expected [001],[110]

    list<Result> rm;
    rm = maxr(front, f);
    printresults(rm, "rmax");

    exit(-30); // Just testing

}

void showdeal(int d)
{
    char line[80];
    sprintf_s(line, "Deal %d", d);

    PrintHand(line, holdingsc[d]);
}

void openloglopfile()
{
    int e = fopen_s(&LOP, LOPFILE, "w");
    if (e != NULL)
    {
        printf("*Could not open %s in ", LOPFILE);
        cout << fs::current_path();
        exit(-28); // File not creatable
    }
}

#define INDENT 3
typedef struct {
    char lin[128];
} LIN;

void prettyprint()
{
    char inlin[130];
    stack<LIN> st;

    int e = fopen_s(&LOP, LOPFILE, "r");
    if (e != NULL)
    {
        printf("*Could not open %s in ", LOPFILE);
        cout << fs::current_path();
        exit(-29); // File not available
    }
    LIN inlins;
    while (fgets(inlins.lin, 128, LOP) != NULL)
    {
        st.push(inlins);

/*        if (strncmp(inlin, "[Deal", 5) == 0) // Assume [Deal "W: 5.23. "]
        {
            if (inlin[6] == '"')
            {
                char* ptr = strrchr(inlin, '"'); // Find position of ending "
                //                    cout << ptr;
                __int64 chars = ptr - (inlin + 6) - 1;
                //                    cout << chars;
                strncpy_s(Worlds[deal], 128, inlin + 7, chars);
                ptr = strchr(inlin + 7, ' ');
                cards = int(ptr - (inlin + 7) - 5); // Find number of cards in the hand(s)
                deal++;
                WORLDSIZE = deal; // Update number of deals
            }
        }*/
    }
    fclose(LOP);
    FILE* PRET;
    e = fopen_s(&PRET, PRETTYFILE, "w");
    if (e != NULL)
    {
        printf("*Could not open %s in ", PRETTYFILE);
        cout << fs::current_path();
        exit(-30); // File not available
    }
    int indent = 0;
    strcpy_s(inlin, 128,st.top().lin); 
    st.pop();
    int tr, prev_tr,scor;
    char dekl, prev_dekl, last_dekl, suit, rank;
    sscanf_s(inlin, "%d %c %c%c %d", &prev_tr, &prev_dekl, 1,&suit, 1, &rank, 1, &scor);
    last_dekl = prev_dekl;
    while (!st.empty())
    {
        if (indent < 0)
            indent = 0;

        for (int i = 0; i < indent; i++)
            fprintf(PRET, " ");
        fprintf(PRET, "%d %c %c%c %d\n", prev_tr, prev_dekl, suit, rank, scor);
        strcpy_s(inlin, 128, st.top().lin);
        st.pop();
        sscanf_s(inlin, "%d %c %c%c %d", &tr, &dekl, 1, &suit, 1, &rank, 1, &scor);
        if (tr < prev_tr)
        {
            if (tr < prev_tr - 1)
                indent -= INDENT * 2;
            else
                indent -= INDENT * 3;
        }
        else if (tr > prev_tr)
        {
            indent += INDENT;
            last_dekl = prev_dekl = dekl;
        } else if (dekl == last_dekl)
            indent -= INDENT*2;

        if ((prev_dekl != dekl) )
        {
            indent += INDENT;
        }

        prev_dekl = dekl;
        prev_tr = tr;
    }
    fclose(PRET);

}

int main(int argc, char *argv[])
{
    set<short int> w;
    list<Result> r;
    auto start_time = high_resolution_clock::now();
//    testminr(); // Uncomment if testing

    State state = start;
    state.firstc = WEST; // Default West w M=3
    //M0 = 3;
    // Usage: C:\>alphamju 3 12 D file.bn W [optional cards]
    //                     M tricks trump inputfilename [leader [cards]* (up to 10)]
    if (argc > 4)
    {
        M0 = atoi(argv[1]);
        L = atoi(argv[2]);

        if (L > 0)
            openloglopfile();

        contract = atoi(argv[3]);

        if (argv[4][0] == 'H') trumpc = HEARTS;
        else if (argv[4][0] == 'S') trumpc = SPADES;
        else if (argv[4][0] == 'D') trumpc = DIAMONDS;
        else if (argv[4][0] == 'C') trumpc = CLUBS;
        else if (argv[4][0] == 'N') trumpc = NOTRUMP;
        else {
            printf("*Strange trump: %c ?[CDHSN]", argv[4][0]);
            exit(-16);
        }
        doimport(argv[5]);
        if (argc > 6)
        {
            if (argv[6][0] == 'N') state.firstc = NORTH;
            else if (argv[6][0] == 'S') state.firstc = SOUTH;
            else if (argv[6][0] == 'E') state.firstc = EAST;
            else if (argv[6][0] == 'W') state.firstc = WEST;
            else
            {
                printf("*Strange leader: %c ?[NSEW]", argv[6][0]);
                exit(-18);
            }
        }
    }
    state.handtoplay = state.firstc;
    if (state.firstc == NORTH || state.firstc == SOUTH)
        state.Min_node = false;
    else state.Min_node = true;

    printf("M=%d. %d deals w %d cards. Goal: %d tricks in %c, %c begins",
         M0, WORLDSIZE, cards, contract, "SHDCN"[trumpc], "NESW"[state.firstc]);
    for (int cc=0;cc<10;cc++)
    if (argc>7+cc) // Card(s) given
    {
         int ctrumpc = HEARTS;
         int ct = toupper(argv[7 + cc][0]);
         if (ct == 'H') ctrumpc = HEARTS;
         else if (ct == 'S') ctrumpc = SPADES;
         else if (ct == 'D') ctrumpc = DIAMONDS;
         else if (ct == 'C') ctrumpc = CLUBS;
         else if (ct == 'N') ctrumpc = NOTRUMP;
         else
         {
             printf("Strange trump card: %c ?[CDHSN]", ct);
             exit(-20);
         }
         Playable move;
         move.c.suit = ctrumpc;
         move.c.player = state.handtoplay;// state.firstc;
         for (int i = 0; i < 16; i++)
             if (dcardRank[i] == toupper(argv[7+cc][1]))
                 move.c.rank = i;
         state = playc(move.c, state);
         if (cc > 0)
             printf(" and %c", "NESW"[move.c.player]);
         printf(" with ");
         showcard2(move.c.suit,move.c.rank);
    } 
    printf(".\n");
    init();
    for (int i = 0; i < WORLDSIZE; i++)
        w.insert(i);
    for (int d = 0; d < 4 && d < WORLDSIZE; d++) // Maximum 4 deals printed
        showdeal(d);

    r = au(state, M0,w);

    printresults(r,"\nFinal");
    printf(" Score: %5.2f %%. ",score(r));
    if (L > 0)
    {
        fclose(LOP);
        prettyprint(); // Make it more understandable
    }
    auto stop_time = high_resolution_clock::now();
    auto duration = duration_cast<microseconds>(stop_time - start_time);
    printf("Time taken by function :%8.3f seconds\nPress Enter!", duration.count()/1000000.0);
    cin.get();
    return 0; // No error
}

