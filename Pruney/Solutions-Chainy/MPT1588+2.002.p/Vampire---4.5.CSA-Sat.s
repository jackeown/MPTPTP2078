%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:24 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  39 expanded)
%              Number of leaves         :   39 (  39 expanded)
%              Depth                    :    0
%              Number of atoms          :   94 (  94 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u131,axiom,(
    ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) )).

tff(u130,axiom,(
    ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) )).

tff(u129,axiom,(
    ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) )).

tff(u128,axiom,(
    ! [X1,X3,X0,X2,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) )).

tff(u127,axiom,(
    ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) )).

tff(u126,axiom,(
    ! [X1,X3,X5,X0,X2,X4,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) )).

tff(u125,negated_conjecture,(
    k7_domain_1(u1_struct_0(sK1),sK2,sK2) = k2_tarski(sK2,sK2) )).

tff(u124,negated_conjecture,(
    k7_domain_1(u1_struct_0(sK1),sK3,sK2) = k2_tarski(sK3,sK2) )).

tff(u123,negated_conjecture,(
    k7_domain_1(u1_struct_0(sK1),sK2,sK3) = k2_tarski(sK2,sK3) )).

tff(u122,negated_conjecture,(
    k7_domain_1(u1_struct_0(sK1),sK3,sK3) = k2_tarski(sK3,sK3) )).

tff(u121,negated_conjecture,(
    ~ v1_xboole_0(u1_struct_0(sK1)) )).

tff(u120,axiom,(
    v1_xboole_0(k1_xboole_0) )).

tff(u119,axiom,(
    ! [X1,X0,X2] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) )).

tff(u118,axiom,(
    ! [X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u117,axiom,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) )).

tff(u116,negated_conjecture,(
    r2_hidden(k1_yellow_0(sK0,k2_tarski(sK2,sK3)),u1_struct_0(sK1)) )).

tff(u115,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k7_domain_1(u1_struct_0(sK1),X1,X0) = k2_tarski(X1,X0) ) )).

tff(u114,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | k7_domain_1(u1_struct_0(sK1),X0,sK2) = k2_tarski(X0,sK2) ) )).

tff(u113,negated_conjecture,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k7_domain_1(u1_struct_0(sK1),X1,sK3) = k2_tarski(X1,sK3) ) )).

tff(u112,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | k7_domain_1(u1_struct_0(sK1),sK2,X0) = k2_tarski(sK2,X0) ) )).

tff(u111,negated_conjecture,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k7_domain_1(u1_struct_0(sK1),sK3,X1) = k2_tarski(sK3,X1) ) )).

tff(u110,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | k7_domain_1(u1_struct_0(sK1),X0,X0) = k2_tarski(X0,X0) ) )).

tff(u109,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK1)) )).

tff(u108,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK1)) )).

tff(u107,axiom,(
    ! [X1,X3,X0,X2] :
      ( m1_subset_1(k1_enumset1(X0,X1,X2),k1_zfmisc_1(X3))
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X2,X3)
      | ~ m1_subset_1(X1,X3)
      | ~ m1_subset_1(X0,X3) ) )).

tff(u106,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(k2_tarski(X0,X1),k1_zfmisc_1(X2))
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X1,X2)
      | ~ m1_subset_1(X0,X2) ) )).

tff(u105,axiom,(
    ! [X1,X3,X0,X2,X4] :
      ( m1_subset_1(k2_enumset1(X0,X1,X2,X3),k1_zfmisc_1(X4))
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X3,X4)
      | ~ m1_subset_1(X2,X4)
      | ~ m1_subset_1(X1,X4)
      | ~ m1_subset_1(X0,X4) ) )).

tff(u104,axiom,(
    ! [X1,X3,X5,X0,X2,X4] :
      ( m1_subset_1(k3_enumset1(X0,X1,X2,X3,X4),k1_zfmisc_1(X5))
      | k1_xboole_0 = X5
      | ~ m1_subset_1(X4,X5)
      | ~ m1_subset_1(X3,X5)
      | ~ m1_subset_1(X2,X5)
      | ~ m1_subset_1(X1,X5)
      | ~ m1_subset_1(X0,X5) ) )).

tff(u103,axiom,(
    ! [X1,X3,X5,X0,X2,X4,X6] :
      ( m1_subset_1(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(X6))
      | k1_xboole_0 = X6
      | ~ m1_subset_1(X5,X6)
      | ~ m1_subset_1(X4,X6)
      | ~ m1_subset_1(X3,X6)
      | ~ m1_subset_1(X2,X6)
      | ~ m1_subset_1(X1,X6)
      | ~ m1_subset_1(X0,X6) ) )).

tff(u102,axiom,(
    ! [X1,X3,X5,X7,X0,X2,X4,X6] :
      ( m1_subset_1(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X7))
      | k1_xboole_0 = X7
      | ~ m1_subset_1(X6,X7)
      | ~ m1_subset_1(X5,X7)
      | ~ m1_subset_1(X4,X7)
      | ~ m1_subset_1(X3,X7)
      | ~ m1_subset_1(X2,X7)
      | ~ m1_subset_1(X1,X7)
      | ~ m1_subset_1(X0,X7) ) )).

tff(u101,axiom,(
    ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] :
      ( m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X8,X0)
      | ~ m1_subset_1(X7,X0)
      | ~ m1_subset_1(X6,X0)
      | ~ m1_subset_1(X5,X0)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0) ) )).

tff(u100,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u99,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u98,negated_conjecture,(
    v4_orders_2(sK0) )).

tff(u97,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u96,negated_conjecture,(
    v4_yellow_0(sK1,sK0) )).

tff(u95,negated_conjecture,(
    m1_yellow_0(sK1,sK0) )).

tff(u94,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))
    | ~ r1_yellow_0(sK1,k2_tarski(sK2,sK3)) )).

tff(u93,negated_conjecture,(
    r1_yellow_0(sK0,k2_tarski(sK2,sK3)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.41  % (4515)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (4520)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (4516)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (4518)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (4520)Refutation not found, incomplete strategy% (4520)------------------------------
% 0.21/0.47  % (4520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (4520)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (4520)Memory used [KB]: 6268
% 0.21/0.47  % (4520)Time elapsed: 0.042 s
% 0.21/0.47  % (4520)------------------------------
% 0.21/0.47  % (4520)------------------------------
% 0.21/0.47  % (4518)Refutation not found, incomplete strategy% (4518)------------------------------
% 0.21/0.47  % (4518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (4518)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (4518)Memory used [KB]: 1663
% 0.21/0.47  % (4518)Time elapsed: 0.051 s
% 0.21/0.47  % (4518)------------------------------
% 0.21/0.47  % (4518)------------------------------
% 0.21/0.47  % (4523)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (4526)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (4521)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (4531)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (4528)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (4526)Refutation not found, incomplete strategy% (4526)------------------------------
% 0.21/0.48  % (4526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4526)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (4526)Memory used [KB]: 10618
% 0.21/0.48  % (4526)Time elapsed: 0.063 s
% 0.21/0.48  % (4526)------------------------------
% 0.21/0.48  % (4526)------------------------------
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (4531)# SZS output start Saturation.
% 0.21/0.48  tff(u131,axiom,
% 0.21/0.48      (![X1, X0] : ((k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u130,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u129,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u128,axiom,
% 0.21/0.48      (![X1, X3, X0, X2, X4] : ((k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4))))).
% 0.21/0.48  
% 0.21/0.48  tff(u127,axiom,
% 0.21/0.48      (![X1, X3, X5, X0, X2, X4] : ((k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5))))).
% 0.21/0.48  
% 0.21/0.48  tff(u126,axiom,
% 0.21/0.48      (![X1, X3, X5, X0, X2, X4, X6] : ((k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))).
% 0.21/0.48  
% 0.21/0.48  tff(u125,negated_conjecture,
% 0.21/0.48      (k7_domain_1(u1_struct_0(sK1),sK2,sK2) = k2_tarski(sK2,sK2))).
% 0.21/0.48  
% 0.21/0.48  tff(u124,negated_conjecture,
% 0.21/0.48      (k7_domain_1(u1_struct_0(sK1),sK3,sK2) = k2_tarski(sK3,sK2))).
% 0.21/0.48  
% 0.21/0.48  tff(u123,negated_conjecture,
% 0.21/0.48      (k7_domain_1(u1_struct_0(sK1),sK2,sK3) = k2_tarski(sK2,sK3))).
% 0.21/0.48  
% 0.21/0.48  tff(u122,negated_conjecture,
% 0.21/0.48      (k7_domain_1(u1_struct_0(sK1),sK3,sK3) = k2_tarski(sK3,sK3))).
% 0.21/0.48  
% 0.21/0.48  tff(u121,negated_conjecture,
% 0.21/0.48      ~v1_xboole_0(u1_struct_0(sK1))).
% 0.21/0.48  
% 0.21/0.48  tff(u120,axiom,
% 0.21/0.48      v1_xboole_0(k1_xboole_0)).
% 0.21/0.48  
% 0.21/0.48  tff(u119,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((v1_xboole_0(X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | (k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u118,axiom,
% 0.21/0.48      (![X0, X2] : ((~r2_hidden(X2,X0) | ~v1_xboole_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u117,axiom,
% 0.21/0.48      (![X0] : ((r2_hidden(sK4(X0),X0) | v1_xboole_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u116,negated_conjecture,
% 0.21/0.48      r2_hidden(k1_yellow_0(sK0,k2_tarski(sK2,sK3)),u1_struct_0(sK1))).
% 0.21/0.48  
% 0.21/0.48  tff(u115,negated_conjecture,
% 0.21/0.48      (![X1, X0] : ((~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X1,X0) = k2_tarski(X1,X0)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u114,negated_conjecture,
% 0.21/0.48      (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X0,sK2) = k2_tarski(X0,sK2)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u113,negated_conjecture,
% 0.21/0.48      (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X1,sK3) = k2_tarski(X1,sK3)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u112,negated_conjecture,
% 0.21/0.48      (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),sK2,X0) = k2_tarski(sK2,X0)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u111,negated_conjecture,
% 0.21/0.48      (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),sK3,X1) = k2_tarski(sK3,X1)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u110,negated_conjecture,
% 0.21/0.48      (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK1)) | (k7_domain_1(u1_struct_0(sK1),X0,X0) = k2_tarski(X0,X0)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u109,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.21/0.48  
% 0.21/0.48  tff(u108,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK3,u1_struct_0(sK1))).
% 0.21/0.48  
% 0.21/0.48  tff(u107,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((m1_subset_1(k1_enumset1(X0,X1,X2),k1_zfmisc_1(X3)) | (k1_xboole_0 = X3) | ~m1_subset_1(X2,X3) | ~m1_subset_1(X1,X3) | ~m1_subset_1(X0,X3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u106,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((m1_subset_1(k2_tarski(X0,X1),k1_zfmisc_1(X2)) | (k1_xboole_0 = X2) | ~m1_subset_1(X1,X2) | ~m1_subset_1(X0,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u105,axiom,
% 0.21/0.48      (![X1, X3, X0, X2, X4] : ((m1_subset_1(k2_enumset1(X0,X1,X2,X3),k1_zfmisc_1(X4)) | (k1_xboole_0 = X4) | ~m1_subset_1(X3,X4) | ~m1_subset_1(X2,X4) | ~m1_subset_1(X1,X4) | ~m1_subset_1(X0,X4))))).
% 0.21/0.48  
% 0.21/0.48  tff(u104,axiom,
% 0.21/0.48      (![X1, X3, X5, X0, X2, X4] : ((m1_subset_1(k3_enumset1(X0,X1,X2,X3,X4),k1_zfmisc_1(X5)) | (k1_xboole_0 = X5) | ~m1_subset_1(X4,X5) | ~m1_subset_1(X3,X5) | ~m1_subset_1(X2,X5) | ~m1_subset_1(X1,X5) | ~m1_subset_1(X0,X5))))).
% 0.21/0.48  
% 0.21/0.48  tff(u103,axiom,
% 0.21/0.48      (![X1, X3, X5, X0, X2, X4, X6] : ((m1_subset_1(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(X6)) | (k1_xboole_0 = X6) | ~m1_subset_1(X5,X6) | ~m1_subset_1(X4,X6) | ~m1_subset_1(X3,X6) | ~m1_subset_1(X2,X6) | ~m1_subset_1(X1,X6) | ~m1_subset_1(X0,X6))))).
% 0.21/0.48  
% 0.21/0.48  tff(u102,axiom,
% 0.21/0.48      (![X1, X3, X5, X7, X0, X2, X4, X6] : ((m1_subset_1(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_zfmisc_1(X7)) | (k1_xboole_0 = X7) | ~m1_subset_1(X6,X7) | ~m1_subset_1(X5,X7) | ~m1_subset_1(X4,X7) | ~m1_subset_1(X3,X7) | ~m1_subset_1(X2,X7) | ~m1_subset_1(X1,X7) | ~m1_subset_1(X0,X7))))).
% 0.21/0.48  
% 0.21/0.48  tff(u101,axiom,
% 0.21/0.48      (![X1, X3, X5, X7, X8, X0, X2, X4, X6] : ((m1_subset_1(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X0)) | (k1_xboole_0 = X0) | ~m1_subset_1(X8,X0) | ~m1_subset_1(X7,X0) | ~m1_subset_1(X6,X0) | ~m1_subset_1(X5,X0) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u100,negated_conjecture,
% 0.21/0.48      ~v2_struct_0(sK0)).
% 0.21/0.48  
% 0.21/0.48  tff(u99,negated_conjecture,
% 0.21/0.48      ~v2_struct_0(sK1)).
% 0.21/0.48  
% 0.21/0.48  tff(u98,negated_conjecture,
% 0.21/0.48      v4_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  tff(u97,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  tff(u96,negated_conjecture,
% 0.21/0.48      v4_yellow_0(sK1,sK0)).
% 0.21/0.48  
% 0.21/0.48  tff(u95,negated_conjecture,
% 0.21/0.48      m1_yellow_0(sK1,sK0)).
% 0.21/0.48  
% 0.21/0.48  tff(u94,negated_conjecture,
% 0.21/0.48      ((~~r1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),sK2,sK3))) | ~r1_yellow_0(sK1,k2_tarski(sK2,sK3)))).
% 0.21/0.48  
% 0.21/0.48  tff(u93,negated_conjecture,
% 0.21/0.48      r1_yellow_0(sK0,k2_tarski(sK2,sK3))).
% 0.21/0.48  
% 0.21/0.48  % (4531)# SZS output end Saturation.
% 0.21/0.48  % (4531)------------------------------
% 0.21/0.48  % (4531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4531)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (4531)Memory used [KB]: 6140
% 0.21/0.48  % (4531)Time elapsed: 0.063 s
% 0.21/0.48  % (4531)------------------------------
% 0.21/0.48  % (4531)------------------------------
% 0.21/0.48  % (4514)Success in time 0.123 s
%------------------------------------------------------------------------------
