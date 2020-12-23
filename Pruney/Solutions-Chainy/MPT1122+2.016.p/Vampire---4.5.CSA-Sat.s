%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:19 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  36 expanded)
%              Number of leaves         :   36 (  36 expanded)
%              Depth                    :    0
%              Number of atoms          :   66 (  66 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u158,negated_conjecture,
    ( ~ ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

tff(u157,axiom,(
    ! [X1,X0] :
      ( k2_pre_topc(X0,X1) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) )).

tff(u156,axiom,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 )).

tff(u155,axiom,(
    ! [X3,X2] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) )).

tff(u154,negated_conjecture,(
    k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) )).

tff(u153,axiom,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) )).

tff(u152,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1)) )).

tff(u151,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) )).

tff(u150,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

tff(u149,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u148,axiom,(
    ! [X0] : k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0 )).

tff(u147,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u146,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) )).

tff(u145,negated_conjecture,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

tff(u144,negated_conjecture,(
    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

tff(u143,axiom,(
    ! [X3,X5,X4] :
      ( ~ r1_tarski(X4,X3)
      | k7_subset_1(X3,X4,X5) = k4_xboole_0(X4,X5) ) )).

tff(u142,axiom,(
    ! [X1,X2] :
      ( ~ r1_tarski(X2,X1)
      | k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) )).

tff(u141,axiom,(
    ! [X1,X2] :
      ( ~ r1_tarski(X2,X1)
      | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2) ) )).

tff(u140,axiom,(
    ! [X1,X2] :
      ( ~ r1_tarski(X2,u1_struct_0(X1))
      | ~ v4_pre_topc(X2,X1)
      | k2_pre_topc(X1,X2) = X2
      | ~ l1_pre_topc(X1) ) )).

tff(u139,axiom,(
    ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) )).

tff(u138,negated_conjecture,(
    r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u137,axiom,(
    ! [X5] : r1_tarski(X5,X5) )).

tff(u136,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u135,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) )).

tff(u134,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) )).

tff(u133,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) )).

tff(u132,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u131,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u130,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u129,negated_conjecture,(
    l1_pre_topc(sK0) )).

tff(u128,negated_conjecture,
    ( ~ ~ v4_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(sK1,sK0) )).

tff(u127,axiom,(
    ! [X0] :
      ( ~ v4_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0)) ) )).

tff(u126,axiom,(
    ! [X1,X0] :
      ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(X0),X1),X0)
      | k4_xboole_0(u1_struct_0(X0),X1) = k2_pre_topc(X0,k4_xboole_0(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0) ) )).

tff(u125,axiom,(
    ! [X1,X0] :
      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) )).

tff(u124,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | v3_pre_topc(sK1,sK0) )).

tff(u123,axiom,(
    ! [X1,X0] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (19094)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.45  % (19102)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.45  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.45  % (19094)# SZS output start Saturation.
% 0.21/0.45  tff(u158,negated_conjecture,
% 0.21/0.45      ((~(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))))).
% 0.21/0.45  
% 0.21/0.45  tff(u157,axiom,
% 0.21/0.45      (![X1, X0] : (((k2_pre_topc(X0,X1) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u156,axiom,
% 0.21/0.45      (![X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0)))).
% 0.21/0.45  
% 0.21/0.45  tff(u155,axiom,
% 0.21/0.45      (![X3, X2] : ((k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))))))).
% 0.21/0.45  
% 0.21/0.45  tff(u154,negated_conjecture,
% 0.21/0.45      (k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.45  
% 0.21/0.45  tff(u153,axiom,
% 0.21/0.45      (![X0] : ((k4_xboole_0(X0,X0) = k3_subset_1(X0,X0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u152,axiom,
% 0.21/0.45      (![X1, X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u151,axiom,
% 0.21/0.45      (![X1, X0] : ((k4_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))))).
% 0.21/0.45  
% 0.21/0.45  tff(u150,axiom,
% 0.21/0.45      (![X1, X2] : ((k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2))))).
% 0.21/0.45  
% 0.21/0.45  tff(u149,axiom,
% 0.21/0.45      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.21/0.45  
% 0.21/0.45  tff(u148,axiom,
% 0.21/0.45      (![X0] : ((k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0)))).
% 0.21/0.45  
% 0.21/0.45  tff(u147,negated_conjecture,
% 0.21/0.45      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u146,axiom,
% 0.21/0.45      (![X1, X0, X2] : ((k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2))))).
% 0.21/0.45  
% 0.21/0.45  tff(u145,negated_conjecture,
% 0.21/0.45      (sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)))).
% 0.21/0.45  
% 0.21/0.45  tff(u144,negated_conjecture,
% 0.21/0.45      (sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)))).
% 0.21/0.45  
% 0.21/0.45  tff(u143,axiom,
% 0.21/0.45      (![X3, X5, X4] : ((~r1_tarski(X4,X3) | (k7_subset_1(X3,X4,X5) = k4_xboole_0(X4,X5)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u142,axiom,
% 0.21/0.45      (![X1, X2] : ((~r1_tarski(X2,X1) | (k3_subset_1(X1,k3_subset_1(X1,X2)) = X2))))).
% 0.21/0.45  
% 0.21/0.45  tff(u141,axiom,
% 0.21/0.45      (![X1, X2] : ((~r1_tarski(X2,X1) | (k4_xboole_0(X1,X2) = k3_subset_1(X1,X2)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u140,axiom,
% 0.21/0.45      (![X1, X2] : ((~r1_tarski(X2,u1_struct_0(X1)) | ~v4_pre_topc(X2,X1) | (k2_pre_topc(X1,X2) = X2) | ~l1_pre_topc(X1))))).
% 0.21/0.45  
% 0.21/0.45  tff(u139,axiom,
% 0.21/0.45      (![X1, X0] : (r1_tarski(k4_xboole_0(X0,X1),X0)))).
% 0.21/0.45  
% 0.21/0.45  tff(u138,negated_conjecture,
% 0.21/0.45      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.45  
% 0.21/0.45  tff(u137,axiom,
% 0.21/0.45      (![X5] : (r1_tarski(X5,X5)))).
% 0.21/0.45  
% 0.21/0.45  tff(u136,axiom,
% 0.21/0.45      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u135,axiom,
% 0.21/0.45      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1))))).
% 0.21/0.45  
% 0.21/0.45  tff(u134,axiom,
% 0.21/0.45      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u133,axiom,
% 0.21/0.45      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) = X1))))).
% 0.21/0.45  
% 0.21/0.45  tff(u132,negated_conjecture,
% 0.21/0.45      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.45  
% 0.21/0.45  tff(u131,axiom,
% 0.21/0.45      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u130,axiom,
% 0.21/0.45      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 0.21/0.45  
% 0.21/0.45  tff(u129,negated_conjecture,
% 0.21/0.45      l1_pre_topc(sK0)).
% 0.21/0.45  
% 0.21/0.45  tff(u128,negated_conjecture,
% 0.21/0.45      ((~~v4_pre_topc(sK1,sK0)) | ~v4_pre_topc(sK1,sK0))).
% 0.21/0.45  
% 0.21/0.45  tff(u127,axiom,
% 0.21/0.45      (![X0] : ((~v4_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | (u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0))))))).
% 0.21/0.45  
% 0.21/0.45  tff(u126,axiom,
% 0.21/0.45      (![X1, X0] : ((~v4_pre_topc(k4_xboole_0(u1_struct_0(X0),X1),X0) | (k4_xboole_0(u1_struct_0(X0),X1) = k2_pre_topc(X0,k4_xboole_0(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u125,axiom,
% 0.21/0.45      (![X1, X0] : ((~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u124,negated_conjecture,
% 0.21/0.45      ((~v3_pre_topc(sK1,sK0)) | v3_pre_topc(sK1,sK0))).
% 0.21/0.45  
% 0.21/0.45  tff(u123,axiom,
% 0.21/0.45      (![X1, X0] : ((v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0))))).
% 0.21/0.45  
% 0.21/0.45  % (19094)# SZS output end Saturation.
% 0.21/0.45  % (19094)------------------------------
% 0.21/0.45  % (19094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (19094)Termination reason: Satisfiable
% 0.21/0.45  
% 0.21/0.45  % (19094)Memory used [KB]: 10618
% 0.21/0.45  % (19094)Time elapsed: 0.042 s
% 0.21/0.45  % (19094)------------------------------
% 0.21/0.45  % (19094)------------------------------
% 0.21/0.45  % (19081)Success in time 0.092 s
%------------------------------------------------------------------------------
