----------------------------- MODULE Nomination -----------------------------

(***************************************************************************)
(* This is a high-level specification of SCP focusing on the nomination    *)
(* protocol.  In this version, we do not wait on the pre-image to vote for *)
(* a txset, but only to accept it.                                         *)
(*                                                                         *)
(* In the previous version of this document even accepted without a        *)
(* pre-image.  The problem with this is that nodes that confirm then stop  *)
(* voting for new values, and this could create a situation in which not   *)
(* enough nodes can start balloting (i.e.  not a full quorum) and the      *)
(* whole system is stuck.  This is because, once a Tier-1 blocking set has *)
(* a candidate, not new values can ever become candidates.  An adversary   *)
(* could therefore carefully distributed a pre-image to a Tier-1 blocking  *)
(* set but withold it from any full quorum and halt the system.  (the      *)
(* attack wouldn't work if nodes download pre-image from their peers, but  *)
(* that's an assumption we have not made and is currently not the case).   *)
(* So accepting without a pre-image is only workable if there is some way  *)
(* to guarantee that, once a Tier-1 blocking set has a pre-image, then     *)
(* everybody in Tier-1 eventually gets it.                                 *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS
    V, \* validators
    B, \* blocks
    Bot, \* default value
    Quorum(_), \* Quorum(v) is the set of quorums of validator v
    Blocking(_), \* Blocking(v) is the set of blocking sets of validator v
    Combine(_), \* the functions that combines candidates to produce a block for balloting
    H, \* domain of hashes
    Hash(_) \* hash function
    
(*
--algorithm SCP {
    variables \* global variables (e.g. representing messages or cross-component variables like ballotingBlock):
        ballotingBlock = [v \in V |-> Bot]; \* for each validator, the nominated block for balloting
        decision = [v \in V |-> Bot];  \* for each validator, the balloting decision
        voted = [v \in V |-> {}]; \* X in the whitepaper (nomination Section)
        accepted = [v \in V |-> {}]; \* Y in the whitepaper (nomination Section)
    process (nomination \in V)
        variables \* local variables:
            round = 0; \* nothing happens in round 0; the protocol start at round 1
            candidates = {}; \* Z in the whitepaper (nomination Section)
            block = [h \in H |-> Bot]; \* a map from hash to corresponding block
            leader = Bot; \* leader for the current round
    {
ln1:    while (TRUE)
        either { \* timeout and go to next round (this also starts round 1)
            round := @ + 1;
            with (l \in V) { \* pick a leader
                leader := l;
                if (l = self) \* if the leader is the current node, pick a block hash and vote for it
                    with (h \in H)
                    voted[self] := @ \union {h}
            }
        }
        or if (candidates = {}) { \* vote for what the leader voted for, unless we have a candidate already
            when leader # Bot;
            with (hs = voted[leader]) { 
                await hs # {}; \* wait to hear from the leader 
                voted[self] := @ \union hs \* vote for what the leader has voted for
            }
        } 
        or with (Q \in Quorum(self), h \in H) { \* accept when voted or accepted by a quorum and we have the pre-image
            when block[h] # Bot; \* we must have received the block
            when \A w \in Q : h \in voted[w] \/ h \in accepted[w]; \* a quorum has voted or accepted h:
            accepted[self] := @ \union {h}; \* accept h
        }
        or with (Bl \in Blocking(self), h \in H) { \* accept when accepted by a blocking set and we have the pre-image
            when block[h] # Bot; \* we must have received the block
            when \A w \in Bl : h \in accepted[w];
            accepted[self] := @ \union {h}; \* accept h
        }
        or with (b \in B) { \* receive a block
            block[Hash(b)] := b;
        }
        or with (Q \in Quorum(self), h \in H) { \* confirm b as candidate
            when block[h] # Bot; \* we must have received the block
            when \A w \in Q : h \in accepted[w]; \* a quorum has accepted h:
            candidates := @ \union {block[h]}; \* add h to the confirmed candidates
            \* update the block used in balloting:
            ballotingBlock[self] := Combine(candidates); \* this starts the balloting protocol (see below)
        }
    } 
    \* as a first approximation, balloting just decide on one of the balloting blocks:
    \* note we cannot reuse the process ID identifiers used in nomination, so we add the "balloting" tag
    process (balloting \in {<<v, "balloting">> : v \in V}) { 
lb1:    await ballotingBlock[self[1]] # Bot; \* wait for a confirmed candidate from nomination
lb2:    with (b \in {ballotingBlock[v] : v \in V} \ {Bot}) {
            when \A w \in V : decision[w] # Bot => b = decision[w];
            decision[self[1]] := b;
        }
    }
}
*)

\* BEGIN TRANSLATION (chksum(pcal) = "843080ce" /\ chksum(tla) = "182c0f6")
VARIABLES ballotingBlock, decision, voted, accepted, pc, round, candidates, 
          block, leader

vars == << ballotingBlock, decision, voted, accepted, pc, round, candidates, 
           block, leader >>

ProcSet == (V) \cup ({<<v, "balloting">> : v \in V})

Init == (* Global variables *)
        /\ ballotingBlock = [v \in V |-> Bot]
        /\ decision = [v \in V |-> Bot]
        /\ voted = [v \in V |-> {}]
        /\ accepted = [v \in V |-> {}]
        (* Process nomination *)
        /\ round = [self \in V |-> 0]
        /\ candidates = [self \in V |-> {}]
        /\ block = [self \in V |-> [h \in H |-> Bot]]
        /\ leader = [self \in V |-> Bot]
        /\ pc = [self \in ProcSet |-> CASE self \in V -> "ln1"
                                        [] self \in {<<v, "balloting">> : v \in V} -> "lb1"]

ln1(self) == /\ pc[self] = "ln1"
             /\ \/ /\ round' = [round EXCEPT ![self] = @ + 1]
                   /\ \E l \in V:
                        /\ leader' = [leader EXCEPT ![self] = l]
                        /\ IF l = self
                              THEN /\ \E h \in H:
                                        voted' = [voted EXCEPT ![self] = @ \union {h}]
                              ELSE /\ TRUE
                                   /\ voted' = voted
                   /\ UNCHANGED <<ballotingBlock, accepted, candidates, block>>
                \/ /\ IF candidates[self] = {}
                         THEN /\ leader[self] # Bot
                              /\ LET hs == voted[leader[self]] IN
                                   /\ hs # {}
                                   /\ voted' = [voted EXCEPT ![self] = @ \union hs]
                         ELSE /\ TRUE
                              /\ voted' = voted
                   /\ UNCHANGED <<ballotingBlock, accepted, round, candidates, block, leader>>
                \/ /\ \E Q \in Quorum(self):
                        \E h \in H:
                          /\ block[self][h] # Bot
                          /\ \A w \in Q : h \in voted[w] \/ h \in accepted[w]
                          /\ accepted' = [accepted EXCEPT ![self] = @ \union {h}]
                   /\ UNCHANGED <<ballotingBlock, voted, round, candidates, block, leader>>
                \/ /\ \E Bl \in Blocking(self):
                        \E h \in H:
                          /\ block[self][h] # Bot
                          /\ \A w \in Bl : h \in accepted[w]
                          /\ accepted' = [accepted EXCEPT ![self] = @ \union {h}]
                   /\ UNCHANGED <<ballotingBlock, voted, round, candidates, block, leader>>
                \/ /\ \E b \in B:
                        block' = [block EXCEPT ![self][Hash(b)] = b]
                   /\ UNCHANGED <<ballotingBlock, voted, accepted, round, candidates, leader>>
                \/ /\ \E Q \in Quorum(self):
                        \E h \in H:
                          /\ block[self][h] # Bot
                          /\ \A w \in Q : h \in accepted[w]
                          /\ candidates' = [candidates EXCEPT ![self] = @ \union {block[self][h]}]
                          /\ ballotingBlock' = [ballotingBlock EXCEPT ![self] = Combine(candidates'[self])]
                   /\ UNCHANGED <<voted, accepted, round, block, leader>>
             /\ pc' = [pc EXCEPT ![self] = "ln1"]
             /\ UNCHANGED decision

nomination(self) == ln1(self)

lb1(self) == /\ pc[self] = "lb1"
             /\ ballotingBlock[self[1]] # Bot
             /\ pc' = [pc EXCEPT ![self] = "lb2"]
             /\ UNCHANGED << ballotingBlock, decision, voted, accepted, round, 
                             candidates, block, leader >>

lb2(self) == /\ pc[self] = "lb2"
             /\ \E b \in {ballotingBlock[v] : v \in V} \ {Bot}:
                  /\ \A w \in V : decision[w] # Bot => b = decision[w]
                  /\ decision' = [decision EXCEPT ![self[1]] = b]
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << ballotingBlock, voted, accepted, round, 
                             candidates, block, leader >>

balloting(self) == lb1(self) \/ lb2(self)

Next == (\E self \in V: nomination(self))
           \/ (\E self \in {<<v, "balloting">> : v \in V}: balloting(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
    
\* Concrete hashing for the model-checker:
TestH == 1..Cardinality(B)
TestHash(b) == 
    LET f == CHOOSE f \in [B -> H] : \A b1,b2 \in B : b1 # b2 => f[b1] # f[b2]
    IN f[b]

\* Debugging canaries:
Canary1 == \A v \in V : decision[v] = Bot
Canary2 == \A v \in V : Cardinality(candidates[v]) <= 1
Canary3 == \A v \in V : ballotingBlock[v] = Bot

TestQuorums == {Q \in SUBSET V : 2*Cardinality(Q)>Cardinality(V)}
TestBlocking == {Bl \in SUBSET V : Cardinality(Bl) > 1}

TypeOkay ==
    /\ ballotingBlock \in [V -> B \cup {Bot}]
    /\ decision \in [V -> B \cup {Bot}]
    /\ voted \in [V -> SUBSET H]
    /\ accepted \in [V -> SUBSET H]
    /\ round \in [V -> Nat]
    /\ candidates \in [V -> SUBSET B]
    /\ block \in [V -> [H -> B \cup {Bot}]]
    /\ leader \in [V -> V \cup {Bot}]
=============================================================================
\* Modification History
\* Last modified Mon Jan 23 11:10:24 PST 2023 by nano
\* Created Fri Jan 13 09:09:00 PST 2023 by nano
