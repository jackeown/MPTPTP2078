%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:43 EST 2020

% Result     : CounterSatisfiable 1.63s
% Output     : Saturation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    0
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u121,negated_conjecture,
    ( ~ ( k2_struct_0(sK0) != sK1 )
    | k2_struct_0(sK0) != sK1 )).

tff(u120,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u119,axiom,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 )).

tff(u118,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u117,axiom,(
    ! [X1,X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) )).

tff(u116,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) )).

tff(u115,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u114,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u113,negated_conjecture,(
    ! [X1] : k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,X1)) )).

tff(u112,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) )).

tff(u111,negated_conjecture,(
    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u110,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u109,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u108,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) )).

tff(u107,negated_conjecture,
    ( ~ ~ r1_tarski(k2_struct_0(sK0),sK1)
    | ~ r1_tarski(k2_struct_0(sK0),sK1) )).

tff(u106,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u105,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) )).

tff(u104,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ l1_struct_0(X0) ) )).

tff(u103,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u102,negated_conjecture,(
    l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:38:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.39/0.54  % (11579)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.39/0.55  % (11572)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.39/0.57  % (11589)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.63/0.57  % (11571)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.63/0.57  % (11575)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.63/0.57  % (11571)Refutation not found, incomplete strategy% (11571)------------------------------
% 1.63/0.57  % (11571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (11571)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (11571)Memory used [KB]: 1663
% 1.63/0.57  % (11571)Time elapsed: 0.153 s
% 1.63/0.57  % (11571)------------------------------
% 1.63/0.57  % (11571)------------------------------
% 1.63/0.57  % (11580)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.63/0.57  % (11589)Refutation not found, incomplete strategy% (11589)------------------------------
% 1.63/0.57  % (11589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (11589)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (11589)Memory used [KB]: 1663
% 1.63/0.57  % (11589)Time elapsed: 0.149 s
% 1.63/0.57  % (11589)------------------------------
% 1.63/0.57  % (11589)------------------------------
% 1.63/0.57  % (11594)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.63/0.58  % (11578)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.63/0.58  % (11579)Refutation not found, incomplete strategy% (11579)------------------------------
% 1.63/0.58  % (11579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (11588)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.63/0.58  % (11576)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.63/0.58  % (11579)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (11579)Memory used [KB]: 1791
% 1.63/0.58  % (11579)Time elapsed: 0.157 s
% 1.63/0.58  % (11579)------------------------------
% 1.63/0.58  % (11579)------------------------------
% 1.63/0.58  % (11588)Refutation not found, incomplete strategy% (11588)------------------------------
% 1.63/0.58  % (11588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (11588)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (11588)Memory used [KB]: 1663
% 1.63/0.58  % (11588)Time elapsed: 0.156 s
% 1.63/0.58  % (11588)------------------------------
% 1.63/0.58  % (11588)------------------------------
% 1.63/0.58  % SZS status CounterSatisfiable for theBenchmark
% 1.63/0.58  % (11576)# SZS output start Saturation.
% 1.63/0.58  tff(u121,negated_conjecture,
% 1.63/0.58      ((~(k2_struct_0(sK0) != sK1)) | (k2_struct_0(sK0) != sK1))).
% 1.63/0.58  
% 1.63/0.58  tff(u120,axiom,
% 1.63/0.58      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 1.63/0.58  
% 1.63/0.58  tff(u119,axiom,
% 1.63/0.58      (![X0] : ((k2_xboole_0(X0,X0) = X0)))).
% 1.63/0.58  
% 1.63/0.58  tff(u118,axiom,
% 1.63/0.58      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 1.63/0.58  
% 1.63/0.58  tff(u117,axiom,
% 1.63/0.58      (![X1, X0] : ((k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))))))).
% 1.63/0.58  
% 1.63/0.58  tff(u116,axiom,
% 1.63/0.58      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)))))).
% 1.63/0.58  
% 1.63/0.58  tff(u115,negated_conjecture,
% 1.63/0.58      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 1.63/0.58  
% 1.63/0.58  tff(u114,negated_conjecture,
% 1.63/0.58      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 1.63/0.58  
% 1.63/0.58  tff(u113,negated_conjecture,
% 1.63/0.58      (![X1] : ((k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,X1)))))).
% 1.63/0.58  
% 1.63/0.58  tff(u112,negated_conjecture,
% 1.63/0.58      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)))))).
% 1.63/0.58  
% 1.63/0.58  tff(u111,negated_conjecture,
% 1.63/0.58      (sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))).
% 1.63/0.58  
% 1.63/0.58  tff(u110,negated_conjecture,
% 1.63/0.58      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 1.63/0.58  
% 1.63/0.58  tff(u109,axiom,
% 1.63/0.58      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 1.63/0.58  
% 1.63/0.58  tff(u108,axiom,
% 1.63/0.58      (![X1, X0] : ((~r1_tarski(X0,X1) | (k2_xboole_0(X0,X1) = X1))))).
% 1.63/0.58  
% 1.63/0.58  tff(u107,negated_conjecture,
% 1.63/0.58      ((~~r1_tarski(k2_struct_0(sK0),sK1)) | ~r1_tarski(k2_struct_0(sK0),sK1))).
% 1.63/0.58  
% 1.63/0.58  tff(u106,axiom,
% 1.63/0.58      (![X1] : (r1_tarski(X1,X1)))).
% 1.63/0.58  
% 1.63/0.58  tff(u105,axiom,
% 1.63/0.58      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))))))).
% 1.63/0.58  
% 1.63/0.58  tff(u104,axiom,
% 1.63/0.58      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) | ~l1_struct_0(X0))))).
% 1.63/0.58  
% 1.63/0.58  tff(u103,negated_conjecture,
% 1.63/0.58      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.63/0.58  
% 1.63/0.58  tff(u102,negated_conjecture,
% 1.63/0.58      l1_struct_0(sK0)).
% 1.63/0.58  
% 1.63/0.58  % (11576)# SZS output end Saturation.
% 1.63/0.58  % (11576)------------------------------
% 1.63/0.58  % (11576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (11576)Termination reason: Satisfiable
% 1.63/0.58  
% 1.63/0.58  % (11576)Memory used [KB]: 10746
% 1.63/0.58  % (11576)Time elapsed: 0.163 s
% 1.63/0.58  % (11576)------------------------------
% 1.63/0.58  % (11576)------------------------------
% 1.63/0.59  % (11573)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.63/0.59  % (11569)Success in time 0.228 s
%------------------------------------------------------------------------------
