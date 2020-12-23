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
% DateTime   : Thu Dec  3 13:08:52 EST 2020

% Result     : CounterSatisfiable 1.35s
% Output     : Saturation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   62 (  62 expanded)
%              Number of leaves         :   62 (  62 expanded)
%              Depth                    :    0
%              Number of atoms          :  107 ( 107 expanded)
%              Number of equality atoms :   80 (  80 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u522,negated_conjecture,
    ( ~ ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
    | sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u521,axiom,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) )).

tff(u520,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

tff(u519,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_subset_1(X0,X0,X0),X0) )).

tff(u518,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK1,u1_struct_0(sK0))
    | k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u517,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK2,u1_struct_0(sK0))
    | k1_xboole_0 = k4_xboole_0(sK2,u1_struct_0(sK0)) )).

tff(u516,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0))
    | k1_xboole_0 = k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0)) )).

tff(u515,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | k1_xboole_0 = k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) )).

tff(u514,axiom,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) )).

tff(u513,axiom,
    ( k1_xboole_0 != k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) )).

tff(u512,axiom,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) )).

tff(u511,negated_conjecture,
    ( k1_xboole_0 != k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k1_xboole_0 = k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) )).

tff(u510,axiom,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) )).

tff(u509,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 )).

tff(u508,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1) )).

tff(u507,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )).

tff(u506,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) )).

tff(u505,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)),X2) )).

tff(u504,axiom,(
    ! [X3,X2] : k7_subset_1(X2,X2,X3) = k4_xboole_0(X2,X3) )).

tff(u503,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),sK1)
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) )).

tff(u502,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK2) != k3_subset_1(u1_struct_0(sK0),sK2)
    | k4_xboole_0(u1_struct_0(sK0),sK2) = k3_subset_1(u1_struct_0(sK0),sK2) )).

tff(u501,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) != k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) )).

tff(u500,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK2) != k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),sK2)
    | k4_xboole_0(u1_struct_0(sK0),sK2) = k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),sK2) )).

tff(u499,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] : k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1) )).

tff(u498,axiom,(
    ! [X1,X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) )).

tff(u497,axiom,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 )).

tff(u496,axiom,(
    ! [X1] : k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 )).

tff(u495,axiom,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k4_subset_1(X0,X0,X0) )).

tff(u494,negated_conjecture,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) != k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))
    | k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

tff(u493,negated_conjecture,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) != k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))
    | k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

tff(u492,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u491,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) != k4_subset_1(sK1,sK1,sK1)
    | k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) )).

tff(u490,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) != k4_subset_1(sK2,sK2,sK2)
    | k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2) )).

tff(u489,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

tff(u488,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) != k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

tff(u487,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u486,axiom,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 )).

tff(u485,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

tff(u484,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK2,sK1)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

tff(u483,negated_conjecture,
    ( k2_struct_0(sK0) != k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k2_struct_0(sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) )).

tff(u482,negated_conjecture,
    ( sK1 != k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0)))
    | sK1 = k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) )).

tff(u481,negated_conjecture,
    ( sK1 != k4_xboole_0(sK1,sK2)
    | sK1 = k4_xboole_0(sK1,sK2) )).

tff(u480,negated_conjecture,
    ( sK1 != k4_xboole_0(k2_struct_0(sK0),sK2)
    | sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

tff(u479,negated_conjecture,
    ( sK2 != k4_xboole_0(sK2,sK1)
    | sK2 = k4_xboole_0(sK2,sK1) )).

tff(u478,negated_conjecture,
    ( sK2 != k4_xboole_0(k2_struct_0(sK0),sK1)
    | sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) )).

tff(u477,negated_conjecture,
    ( sK2 != k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0)))
    | sK2 = k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) )).

tff(u476,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) )).

tff(u475,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2) )).

tff(u474,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ) )).

tff(u473,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u472,negated_conjecture,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u471,negated_conjecture,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | r1_tarski(sK2,u1_struct_0(sK0)) )).

tff(u470,axiom,(
    ! [X3,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k4_subset_1(X3,X3,X2) = k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) ) )).

tff(u469,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) )).

tff(u468,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u467,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) )).

tff(u466,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u465,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X1)) ) )).

tff(u464,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) ) )).

tff(u463,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u462,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u461,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (25992)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.24/0.51  % (26000)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.24/0.51  % (25997)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.52  % (25998)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.24/0.52  % (26008)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.24/0.52  % (25993)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.52  % (26001)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.24/0.52  % (25987)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.52  % (26009)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.24/0.52  % (25985)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.52  % (25992)Refutation not found, incomplete strategy% (25992)------------------------------
% 1.24/0.52  % (25992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (25992)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (25992)Memory used [KB]: 6396
% 1.24/0.52  % (25992)Time elapsed: 0.110 s
% 1.24/0.52  % (25992)------------------------------
% 1.24/0.52  % (25992)------------------------------
% 1.24/0.52  % (25987)Refutation not found, incomplete strategy% (25987)------------------------------
% 1.24/0.52  % (25987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (25987)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (25987)Memory used [KB]: 10746
% 1.24/0.52  % (25987)Time elapsed: 0.115 s
% 1.24/0.52  % (25987)------------------------------
% 1.24/0.52  % (25987)------------------------------
% 1.24/0.53  % (26000)Refutation not found, incomplete strategy% (26000)------------------------------
% 1.24/0.53  % (26000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (26000)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (26000)Memory used [KB]: 6140
% 1.24/0.53  % (26000)Time elapsed: 0.003 s
% 1.24/0.53  % (26000)------------------------------
% 1.24/0.53  % (26000)------------------------------
% 1.24/0.53  % (25991)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.53  % (25986)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.53  % (26008)Refutation not found, incomplete strategy% (26008)------------------------------
% 1.35/0.53  % (26008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (26008)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (26008)Memory used [KB]: 1791
% 1.35/0.53  % (26008)Time elapsed: 0.115 s
% 1.35/0.53  % (26008)------------------------------
% 1.35/0.53  % (26008)------------------------------
% 1.35/0.53  % (25993)Refutation not found, incomplete strategy% (25993)------------------------------
% 1.35/0.53  % (25993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (25993)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (25993)Memory used [KB]: 10746
% 1.35/0.53  % (25993)Time elapsed: 0.117 s
% 1.35/0.53  % (25993)------------------------------
% 1.35/0.53  % (25993)------------------------------
% 1.35/0.53  % (26005)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.53  % (26012)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.53  % (25999)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.53  % (25988)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.35/0.53  % (25989)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.53  % (25989)Refutation not found, incomplete strategy% (25989)------------------------------
% 1.35/0.53  % (25989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (25989)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (25989)Memory used [KB]: 6268
% 1.35/0.53  % (25989)Time elapsed: 0.128 s
% 1.35/0.53  % (25989)------------------------------
% 1.35/0.53  % (25989)------------------------------
% 1.35/0.53  % (25990)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.54  % (26003)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.54  % (25990)Refutation not found, incomplete strategy% (25990)------------------------------
% 1.35/0.54  % (25990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (26010)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.54  % (25990)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (25990)Memory used [KB]: 6268
% 1.35/0.54  % (25990)Time elapsed: 0.127 s
% 1.35/0.54  % (25990)------------------------------
% 1.35/0.54  % (25990)------------------------------
% 1.35/0.54  % (25997)Refutation not found, incomplete strategy% (25997)------------------------------
% 1.35/0.54  % (25997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (25997)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (25997)Memory used [KB]: 6396
% 1.35/0.54  % (25997)Time elapsed: 0.113 s
% 1.35/0.54  % (25997)------------------------------
% 1.35/0.54  % (25997)------------------------------
% 1.35/0.54  % (25985)Refutation not found, incomplete strategy% (25985)------------------------------
% 1.35/0.54  % (25985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (25985)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (25985)Memory used [KB]: 1791
% 1.35/0.54  % (25985)Time elapsed: 0.095 s
% 1.35/0.54  % (25985)------------------------------
% 1.35/0.54  % (25985)------------------------------
% 1.35/0.54  % (26007)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.54  % (25995)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.54  % (26013)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.54  % (25995)Refutation not found, incomplete strategy% (25995)------------------------------
% 1.35/0.54  % (25995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (25995)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (25995)Memory used [KB]: 10618
% 1.35/0.54  % (25995)Time elapsed: 0.130 s
% 1.35/0.54  % (25995)------------------------------
% 1.35/0.54  % (25995)------------------------------
% 1.35/0.54  % (26007)Refutation not found, incomplete strategy% (26007)------------------------------
% 1.35/0.54  % (26007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (26007)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (26007)Memory used [KB]: 10746
% 1.35/0.54  % (26007)Time elapsed: 0.089 s
% 1.35/0.54  % (26007)------------------------------
% 1.35/0.54  % (26007)------------------------------
% 1.35/0.54  % (25994)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.54  % (26004)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.54  % SZS status CounterSatisfiable for theBenchmark
% 1.35/0.54  % (26001)# SZS output start Saturation.
% 1.35/0.54  tff(u522,negated_conjecture,
% 1.35/0.54      ((~(sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 1.35/0.54  
% 1.35/0.54  tff(u521,axiom,
% 1.35/0.54      (![X2] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2))))).
% 1.35/0.54  
% 1.35/0.54  tff(u520,axiom,
% 1.35/0.54      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u519,axiom,
% 1.35/0.54      (![X0] : ((k1_xboole_0 = k4_xboole_0(k4_subset_1(X0,X0,X0),X0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u518,negated_conjecture,
% 1.35/0.54      ((~(k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)))) | (k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u517,negated_conjecture,
% 1.35/0.54      ((~(k1_xboole_0 = k4_xboole_0(sK2,u1_struct_0(sK0)))) | (k1_xboole_0 = k4_xboole_0(sK2,u1_struct_0(sK0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u516,negated_conjecture,
% 1.35/0.54      ((~(k1_xboole_0 = k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0)))) | (k1_xboole_0 = k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u515,negated_conjecture,
% 1.35/0.54      ((~(k1_xboole_0 = k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)))) | (k1_xboole_0 = k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u514,axiom,
% 1.35/0.54      (![X0] : ((k1_xboole_0 = k3_subset_1(X0,X0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u513,axiom,
% 1.35/0.54      ((~(k1_xboole_0 = k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0))) | (k1_xboole_0 = k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)))).
% 1.35/0.54  
% 1.35/0.54  tff(u512,axiom,
% 1.35/0.54      (![X0] : ((k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)))))).
% 1.35/0.54  
% 1.35/0.54  tff(u511,negated_conjecture,
% 1.35/0.54      ((~(k1_xboole_0 = k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) | (k1_xboole_0 = k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))).
% 1.35/0.54  
% 1.35/0.54  tff(u510,axiom,
% 1.35/0.54      (![X0] : ((k1_xboole_0 = k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))))).
% 1.35/0.54  
% 1.35/0.54  tff(u509,axiom,
% 1.35/0.54      (![X1] : ((k4_xboole_0(X1,k1_xboole_0) = X1)))).
% 1.35/0.54  
% 1.35/0.54  tff(u508,axiom,
% 1.35/0.54      (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X1))))).
% 1.35/0.54  
% 1.35/0.54  tff(u507,axiom,
% 1.35/0.54      (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))))))).
% 1.35/0.54  
% 1.35/0.54  tff(u506,axiom,
% 1.35/0.54      (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))))))).
% 1.35/0.54  
% 1.35/0.54  tff(u505,axiom,
% 1.35/0.54      (![X1, X2] : ((k4_xboole_0(X1,X2) = k4_xboole_0(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)),X2))))).
% 1.35/0.54  
% 1.35/0.54  tff(u504,axiom,
% 1.35/0.54      (![X3, X2] : ((k7_subset_1(X2,X2,X3) = k4_xboole_0(X2,X3))))).
% 1.35/0.54  
% 1.35/0.54  tff(u503,negated_conjecture,
% 1.35/0.54      ((~(k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1))) | (k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1)))).
% 1.35/0.54  
% 1.35/0.54  tff(u502,negated_conjecture,
% 1.35/0.54      ((~(k4_xboole_0(u1_struct_0(sK0),sK2) = k3_subset_1(u1_struct_0(sK0),sK2))) | (k4_xboole_0(u1_struct_0(sK0),sK2) = k3_subset_1(u1_struct_0(sK0),sK2)))).
% 1.35/0.54  
% 1.35/0.54  tff(u501,negated_conjecture,
% 1.35/0.54      ((~(k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1))) | (k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)))).
% 1.35/0.54  
% 1.35/0.54  tff(u500,negated_conjecture,
% 1.35/0.54      ((~(k4_xboole_0(u1_struct_0(sK0),sK2) = k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),sK2))) | (k4_xboole_0(u1_struct_0(sK0),sK2) = k4_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),sK2)))).
% 1.35/0.54  
% 1.35/0.54  tff(u499,negated_conjecture,
% 1.35/0.54      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1)))))).
% 1.35/0.54  
% 1.35/0.54  tff(u498,axiom,
% 1.35/0.54      (![X1, X0] : ((k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u497,axiom,
% 1.35/0.54      (![X0] : ((k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0)))).
% 1.35/0.54  
% 1.35/0.54  tff(u496,axiom,
% 1.35/0.54      (![X1] : ((k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1)))).
% 1.35/0.54  
% 1.35/0.54  tff(u495,axiom,
% 1.35/0.54      (![X0] : ((k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k4_subset_1(X0,X0,X0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u494,negated_conjecture,
% 1.35/0.54      ((~(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))) | (k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u493,negated_conjecture,
% 1.35/0.54      ((~(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)))) | (k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u492,axiom,
% 1.35/0.54      (![X0] : ((k2_subset_1(X0) = X0)))).
% 1.35/0.54  
% 1.35/0.54  tff(u491,negated_conjecture,
% 1.35/0.54      ((~(k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1))) | (k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1)))).
% 1.35/0.54  
% 1.35/0.54  tff(u490,negated_conjecture,
% 1.35/0.54      ((~(k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2))) | (k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2)))).
% 1.35/0.54  
% 1.35/0.54  tff(u489,negated_conjecture,
% 1.35/0.54      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u488,negated_conjecture,
% 1.35/0.54      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u487,negated_conjecture,
% 1.35/0.54      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)))))).
% 1.35/0.54  
% 1.35/0.54  tff(u486,axiom,
% 1.35/0.54      (![X0] : ((k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0)))).
% 1.35/0.54  
% 1.35/0.54  tff(u485,negated_conjecture,
% 1.35/0.54      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)))).
% 1.35/0.54  
% 1.35/0.54  tff(u484,negated_conjecture,
% 1.35/0.54      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)))).
% 1.35/0.54  
% 1.35/0.54  tff(u483,negated_conjecture,
% 1.35/0.54      ((~(k2_struct_0(sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) | (k2_struct_0(sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))).
% 1.35/0.54  
% 1.35/0.54  tff(u482,negated_conjecture,
% 1.35/0.54      ((~(sK1 = k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))))) | (sK1 = k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0)))))).
% 1.35/0.54  
% 1.35/0.54  tff(u481,negated_conjecture,
% 1.35/0.54      ((~(sK1 = k4_xboole_0(sK1,sK2))) | (sK1 = k4_xboole_0(sK1,sK2)))).
% 1.35/0.54  
% 1.35/0.54  tff(u480,negated_conjecture,
% 1.35/0.54      ((~(sK1 = k4_xboole_0(k2_struct_0(sK0),sK2))) | (sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)))).
% 1.35/0.54  
% 1.35/0.54  tff(u479,negated_conjecture,
% 1.35/0.54      ((~(sK2 = k4_xboole_0(sK2,sK1))) | (sK2 = k4_xboole_0(sK2,sK1)))).
% 1.35/0.54  
% 1.35/0.54  tff(u478,negated_conjecture,
% 1.35/0.54      ((~(sK2 = k4_xboole_0(k2_struct_0(sK0),sK1))) | (sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)))).
% 1.35/0.54  
% 1.35/0.54  tff(u477,negated_conjecture,
% 1.35/0.54      ((~(sK2 = k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))))) | (sK2 = k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0)))))).
% 1.35/0.54  
% 1.35/0.54  tff(u476,axiom,
% 1.35/0.54      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))))).
% 1.35/0.54  
% 1.35/0.54  tff(u475,negated_conjecture,
% 1.35/0.54      ((~r1_xboole_0(sK1,sK2)) | r1_xboole_0(sK1,sK2))).
% 1.35/0.54  
% 1.35/0.54  tff(u474,axiom,
% 1.35/0.54      (![X1, X0] : ((~r1_tarski(X0,X1) | (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u473,axiom,
% 1.35/0.54      (![X0] : (r1_tarski(X0,X0)))).
% 1.35/0.54  
% 1.35/0.54  tff(u472,negated_conjecture,
% 1.35/0.54      ((~r1_tarski(sK1,u1_struct_0(sK0))) | r1_tarski(sK1,u1_struct_0(sK0)))).
% 1.35/0.54  
% 1.35/0.54  tff(u471,negated_conjecture,
% 1.35/0.54      ((~r1_tarski(sK2,u1_struct_0(sK0))) | r1_tarski(sK2,u1_struct_0(sK0)))).
% 1.35/0.54  
% 1.35/0.54  tff(u470,axiom,
% 1.35/0.54      (![X3, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X3)) | (k4_subset_1(X3,X3,X2) = k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))))))).
% 1.35/0.54  
% 1.35/0.54  tff(u469,axiom,
% 1.35/0.54      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))))).
% 1.35/0.54  
% 1.35/0.54  tff(u468,axiom,
% 1.35/0.54      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 1.35/0.54  
% 1.35/0.54  tff(u467,axiom,
% 1.35/0.54      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)))))).
% 1.35/0.54  
% 1.35/0.54  tff(u466,axiom,
% 1.35/0.54      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 1.35/0.54  
% 1.35/0.54  tff(u465,negated_conjecture,
% 1.35/0.54      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X1)))))))).
% 1.35/0.54  
% 1.35/0.54  tff(u464,negated_conjecture,
% 1.35/0.54      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)))))))).
% 1.35/0.54  
% 1.35/0.54  tff(u463,negated_conjecture,
% 1.35/0.54      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u462,negated_conjecture,
% 1.35/0.54      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.35/0.54  
% 1.35/0.54  tff(u461,axiom,
% 1.35/0.54      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 1.35/0.54  
% 1.35/0.54  % (26001)# SZS output end Saturation.
% 1.35/0.54  % (26001)------------------------------
% 1.35/0.54  % (26001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (26001)Termination reason: Satisfiable
% 1.35/0.54  
% 1.35/0.54  % (26001)Memory used [KB]: 11129
% 1.35/0.54  % (26001)Time elapsed: 0.123 s
% 1.35/0.54  % (26001)------------------------------
% 1.35/0.54  % (26001)------------------------------
% 1.35/0.54  % (25994)Refutation not found, incomplete strategy% (25994)------------------------------
% 1.35/0.54  % (25994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (25994)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (25994)Memory used [KB]: 10746
% 1.35/0.54  % (25994)Time elapsed: 0.139 s
% 1.35/0.54  % (25994)------------------------------
% 1.35/0.54  % (25994)------------------------------
% 1.35/0.54  % (25984)Success in time 0.183 s
%------------------------------------------------------------------------------
