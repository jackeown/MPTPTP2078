%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:30 EST 2020

% Result     : CounterSatisfiable 0.23s
% Output     : Saturation 0.23s
% Verified   : 
% Statistics : Number of formulae       :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u49,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1)) )).

tff(u48,axiom,
    ( ~ ! [X1,X0] :
          ( ~ v1_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
          | v1_xboole_0(X0) )
    | ! [X1,X0] :
        ( ~ v1_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
        | v1_xboole_0(X0) ) )).

tff(u47,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

tff(u46,negated_conjecture,
    ( ~ v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0))
    | v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:14:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.48  % (2779)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.48  % (2778)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.49  % (2777)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.49  % (2784)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.49  % (2775)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.49  % (2786)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.49  % (2776)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.23/0.49  % (2778)# SZS output start Saturation.
% 0.23/0.49  tff(u49,negated_conjecture,
% 0.23/0.49      ((~(k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1)))) | (k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1))))).
% 0.23/0.49  
% 0.23/0.49  tff(u48,axiom,
% 0.23/0.49      ((~(![X1, X0] : ((~v1_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1))) | v1_xboole_0(X0))))) | (![X1, X0] : ((~v1_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1))) | v1_xboole_0(X0)))))).
% 0.23/0.49  
% 0.23/0.49  tff(u47,axiom,
% 0.23/0.49      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 0.23/0.49  
% 0.23/0.49  tff(u46,negated_conjecture,
% 0.23/0.49      ((~v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0))) | v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0)))).
% 0.23/0.49  
% 0.23/0.49  % (2778)# SZS output end Saturation.
% 0.23/0.49  % (2778)------------------------------
% 0.23/0.49  % (2778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (2778)Termination reason: Satisfiable
% 0.23/0.49  
% 0.23/0.49  % (2778)Memory used [KB]: 6012
% 0.23/0.49  % (2778)Time elapsed: 0.055 s
% 0.23/0.49  % (2778)------------------------------
% 0.23/0.49  % (2778)------------------------------
% 0.23/0.49  % (2776)Refutation not found, incomplete strategy% (2776)------------------------------
% 0.23/0.49  % (2776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (2776)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.49  
% 0.23/0.49  % (2776)Memory used [KB]: 6140
% 0.23/0.49  % (2776)Time elapsed: 0.054 s
% 0.23/0.49  % (2776)------------------------------
% 0.23/0.49  % (2776)------------------------------
% 0.23/0.49  % (2770)Success in time 0.123 s
%------------------------------------------------------------------------------
