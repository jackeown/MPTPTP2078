%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:34 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    6 (   6 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    0
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u28,negated_conjecture,(
    sK1 != k2_xboole_0(sK0,sK1) )).

tff(u27,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

tff(u26,negated_conjecture,(
    r1_tarski(sK0,sK1) )).

tff(u25,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(X2,k2_xboole_0(X1,X0))
      | ~ r1_tarski(X2,X1) ) )).

tff(u24,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u23,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:13:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.41  % (27597)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.42  % (27601)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (27604)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.43  % (27603)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.45  % (27607)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.45  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.45  % (27607)# SZS output start Saturation.
% 0.22/0.45  tff(u28,negated_conjecture,
% 0.22/0.45      (sK1 != k2_xboole_0(sK0,sK1))).
% 0.22/0.45  
% 0.22/0.45  tff(u27,axiom,
% 0.22/0.45      (![X1, X0] : ((k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0))))).
% 0.22/0.45  
% 0.22/0.45  tff(u26,negated_conjecture,
% 0.22/0.45      r1_tarski(sK0,sK1)).
% 0.22/0.45  
% 0.22/0.45  tff(u25,axiom,
% 0.22/0.45      (![X1, X0, X2] : ((r1_tarski(X2,k2_xboole_0(X1,X0)) | ~r1_tarski(X2,X1))))).
% 0.22/0.45  
% 0.22/0.45  tff(u24,axiom,
% 0.22/0.45      (![X1, X0, X2] : ((r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))))).
% 0.22/0.45  
% 0.22/0.45  tff(u23,axiom,
% 0.22/0.45      (![X1, X0, X2] : ((r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))))).
% 0.22/0.45  
% 0.22/0.45  % (27607)# SZS output end Saturation.
% 0.22/0.45  % (27607)------------------------------
% 0.22/0.45  % (27607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (27607)Termination reason: Satisfiable
% 0.22/0.45  
% 0.22/0.45  % (27607)Memory used [KB]: 10490
% 0.22/0.45  % (27607)Time elapsed: 0.033 s
% 0.22/0.45  % (27607)------------------------------
% 0.22/0.45  % (27607)------------------------------
% 0.22/0.45  % (27595)Success in time 0.09 s
%------------------------------------------------------------------------------
