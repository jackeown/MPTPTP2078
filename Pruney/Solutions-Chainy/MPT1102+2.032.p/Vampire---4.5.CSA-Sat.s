%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:32 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    0
%              Number of atoms          :   44 (  44 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u113,negated_conjecture,(
    sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

tff(u112,negated_conjecture,
    ( ~ ( sK1 != u1_struct_0(sK0) )
    | sK1 != u1_struct_0(sK0) )).

tff(u111,negated_conjecture,
    ( ~ ( u1_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),sK1) )
    | u1_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),sK1) )).

tff(u110,negated_conjecture,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) )).

tff(u109,axiom,(
    ! [X3] : k3_subset_1(X3,X3) = k4_xboole_0(X3,X3) )).

tff(u108,axiom,(
    ! [X2] : k3_subset_1(X2,k3_subset_1(X2,X2)) = X2 )).

tff(u107,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

tff(u106,axiom,(
    ! [X3] : k4_xboole_0(X3,k3_subset_1(X3,X3)) = X3 )).

tff(u105,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u104,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) = k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0) )).

tff(u103,axiom,(
    ! [X1,X0] : k7_subset_1(X0,k3_subset_1(X0,X0),X1) = k4_xboole_0(k3_subset_1(X0,X0),X1) )).

tff(u102,negated_conjecture,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

tff(u101,negated_conjecture,(
    sK1 = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

tff(u100,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u99,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u98,axiom,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_subset_1(X0,X0))
      | k3_subset_1(X0,X0) = X0 ) )).

tff(u97,negated_conjecture,
    ( ~ ~ r1_tarski(u1_struct_0(sK0),sK1)
    | ~ r1_tarski(u1_struct_0(sK0),sK1) )).

tff(u96,negated_conjecture,
    ( ~ ~ r1_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ r1_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

tff(u95,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u94,negated_conjecture,(
    r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u93,negated_conjecture,(
    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

tff(u92,axiom,(
    ! [X5] : r1_tarski(k3_subset_1(X5,X5),X5) )).

tff(u91,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u90,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) )).

tff(u89,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) )).

tff(u88,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) )).

tff(u87,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u86,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u85,negated_conjecture,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u84,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u83,axiom,(
    ! [X4] : m1_subset_1(k3_subset_1(X4,X4),k1_zfmisc_1(X4)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:19:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (21551)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.48  % (21543)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.48  % (21551)Refutation not found, incomplete strategy% (21551)------------------------------
% 0.21/0.48  % (21551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (21551)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (21551)Memory used [KB]: 1663
% 0.21/0.49  % (21551)Time elapsed: 0.075 s
% 0.21/0.49  % (21551)------------------------------
% 0.21/0.49  % (21551)------------------------------
% 0.21/0.49  % (21543)# SZS output start Saturation.
% 0.21/0.49  tff(u113,negated_conjecture,
% 0.21/0.49      (sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.21/0.49  
% 0.21/0.49  tff(u112,negated_conjecture,
% 0.21/0.49      ((~(sK1 != u1_struct_0(sK0))) | (sK1 != u1_struct_0(sK0)))).
% 0.21/0.49  
% 0.21/0.49  tff(u111,negated_conjecture,
% 0.21/0.49      ((~(u1_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),sK1))) | (u1_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),sK1)))).
% 0.21/0.49  
% 0.21/0.49  tff(u110,negated_conjecture,
% 0.21/0.49      (k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.21/0.49  
% 0.21/0.49  tff(u109,axiom,
% 0.21/0.49      (![X3] : ((k3_subset_1(X3,X3) = k4_xboole_0(X3,X3))))).
% 0.21/0.49  
% 0.21/0.49  tff(u108,axiom,
% 0.21/0.49      (![X2] : ((k3_subset_1(X2,k3_subset_1(X2,X2)) = X2)))).
% 0.21/0.49  
% 0.21/0.49  tff(u107,axiom,
% 0.21/0.49      (![X1, X0] : ((k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u106,axiom,
% 0.21/0.49      (![X3] : ((k4_xboole_0(X3,k3_subset_1(X3,X3)) = X3)))).
% 0.21/0.49  
% 0.21/0.49  tff(u105,negated_conjecture,
% 0.21/0.49      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u104,negated_conjecture,
% 0.21/0.49      (![X0] : ((k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) = k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u103,axiom,
% 0.21/0.49      (![X1, X0] : ((k7_subset_1(X0,k3_subset_1(X0,X0),X1) = k4_xboole_0(k3_subset_1(X0,X0),X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u102,negated_conjecture,
% 0.21/0.49      (sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))).
% 0.21/0.49  
% 0.21/0.49  tff(u101,negated_conjecture,
% 0.21/0.49      (sK1 = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))).
% 0.21/0.49  
% 0.21/0.49  tff(u100,axiom,
% 0.21/0.49      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u99,axiom,
% 0.21/0.49      (![X1, X0] : ((~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u98,axiom,
% 0.21/0.49      (![X0] : ((~r1_tarski(X0,k3_subset_1(X0,X0)) | (k3_subset_1(X0,X0) = X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u97,negated_conjecture,
% 0.21/0.49      ((~~r1_tarski(u1_struct_0(sK0),sK1)) | ~r1_tarski(u1_struct_0(sK0),sK1))).
% 0.21/0.49  
% 0.21/0.49  tff(u96,negated_conjecture,
% 0.21/0.49      ((~~r1_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) | ~r1_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))).
% 0.21/0.49  
% 0.21/0.49  tff(u95,axiom,
% 0.21/0.49      (![X1] : (r1_tarski(X1,X1)))).
% 0.21/0.49  
% 0.21/0.49  tff(u94,negated_conjecture,
% 0.21/0.49      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  tff(u93,negated_conjecture,
% 0.21/0.49      r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  tff(u92,axiom,
% 0.21/0.49      (![X5] : (r1_tarski(k3_subset_1(X5,X5),X5)))).
% 0.21/0.49  
% 0.21/0.49  tff(u91,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u90,axiom,
% 0.21/0.49      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u89,axiom,
% 0.21/0.49      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u88,axiom,
% 0.21/0.49      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u87,axiom,
% 0.21/0.49      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u86,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.49  
% 0.21/0.49  tff(u85,negated_conjecture,
% 0.21/0.49      m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.49  
% 0.21/0.49  tff(u84,axiom,
% 0.21/0.49      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u83,axiom,
% 0.21/0.49      (![X4] : (m1_subset_1(k3_subset_1(X4,X4),k1_zfmisc_1(X4))))).
% 0.21/0.49  
% 0.21/0.49  % (21543)# SZS output end Saturation.
% 0.21/0.49  % (21543)------------------------------
% 0.21/0.49  % (21543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21543)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (21543)Memory used [KB]: 10618
% 0.21/0.49  % (21543)Time elapsed: 0.076 s
% 0.21/0.49  % (21543)------------------------------
% 0.21/0.49  % (21543)------------------------------
% 0.21/0.49  % (21532)Success in time 0.126 s
%------------------------------------------------------------------------------
