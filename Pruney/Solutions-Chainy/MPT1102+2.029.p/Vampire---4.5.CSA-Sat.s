%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:32 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  40 expanded)
%              Number of leaves         :   40 (  40 expanded)
%              Depth                    :    0
%              Number of atoms          :   60 (  60 expanded)
%              Number of equality atoms :   44 (  44 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u188,negated_conjecture,(
    sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

tff(u187,axiom,(
    ! [X1,X0,X2] :
      ( k1_xboole_0 != k4_xboole_0(X2,X0)
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) )).

tff(u186,axiom,(
    ! [X1,X0,X2] :
      ( k1_xboole_0 != k4_xboole_0(X1,X0)
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u185,axiom,(
    ! [X1,X0,X2] :
      ( k1_xboole_0 != k4_xboole_0(X2,X0)
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) )).

tff(u184,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 != X0
      | k9_subset_1(k1_xboole_0,X1,X0) = k9_subset_1(k1_xboole_0,X0,X1) ) )).

tff(u183,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 != X0
      | k4_xboole_0(X0,X1) = k7_subset_1(k1_xboole_0,X0,X1) ) )).

tff(u182,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 != X0
      | k3_xboole_0(X1,X0) = k9_subset_1(k1_xboole_0,X1,X0) ) )).

tff(u181,axiom,(
    ! [X3,X2,X4] :
      ( k1_xboole_0 != k3_xboole_0(X2,X3)
      | k9_subset_1(k4_xboole_0(X2,X3),X4,X2) = k9_subset_1(k4_xboole_0(X2,X3),X2,X4) ) )).

tff(u180,axiom,(
    ! [X3,X2,X4] :
      ( k1_xboole_0 != k3_xboole_0(X2,X3)
      | k7_subset_1(k4_xboole_0(X2,X3),X2,X4) = k4_xboole_0(X2,X4) ) )).

tff(u179,axiom,(
    ! [X3,X2,X4] :
      ( k1_xboole_0 != k3_xboole_0(X2,X3)
      | k9_subset_1(k4_xboole_0(X2,X3),X4,X2) = k3_xboole_0(X4,X2) ) )).

tff(u178,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u177,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u176,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u175,negated_conjecture,(
    k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u174,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

tff(u173,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) )).

tff(u172,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u171,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) )).

tff(u170,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u169,negated_conjecture,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) )).

tff(u168,axiom,(
    ! [X1,X2] : k9_subset_1(X1,X2,X1) = k3_xboole_0(X2,X1) )).

tff(u167,negated_conjecture,(
    sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u166,negated_conjecture,(
    sK1 = k3_xboole_0(u1_struct_0(sK0),sK1) )).

tff(u165,negated_conjecture,(
    ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0) )).

tff(u164,axiom,(
    ! [X1,X2] : k3_xboole_0(X2,X1) = k9_subset_1(X1,X1,X2) )).

tff(u163,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

tff(u162,axiom,(
    ! [X3,X5,X4] :
      ( ~ r1_tarski(X5,X3)
      | k9_subset_1(X3,X4,X5) = k9_subset_1(X3,X5,X4) ) )).

tff(u161,axiom,(
    ! [X3,X5,X4] :
      ( ~ r1_tarski(X4,X3)
      | k7_subset_1(X3,X4,X5) = k4_xboole_0(X4,X5) ) )).

tff(u160,axiom,(
    ! [X3,X5,X4] :
      ( ~ r1_tarski(X5,X3)
      | k9_subset_1(X3,X4,X5) = k3_xboole_0(X4,X5) ) )).

tff(u159,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) )).

tff(u158,axiom,(
    ! [X1,X0] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) )).

tff(u157,axiom,(
    ! [X1,X0] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u156,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) )).

tff(u155,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u154,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) )).

tff(u153,axiom,(
    ! [X3,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k1_xboole_0 = k4_xboole_0(X2,X3) ) )).

tff(u152,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u151,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u150,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u149,negated_conjecture,(
    l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:46:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (30648)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.44  % (30648)Refutation not found, incomplete strategy% (30648)------------------------------
% 0.21/0.44  % (30648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (30648)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (30648)Memory used [KB]: 10618
% 0.21/0.44  % (30648)Time elapsed: 0.004 s
% 0.21/0.44  % (30648)------------------------------
% 0.21/0.44  % (30648)------------------------------
% 0.21/0.44  % (30653)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.44  % (30654)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.45  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.45  % (30653)# SZS output start Saturation.
% 0.21/0.45  tff(u188,negated_conjecture,
% 0.21/0.45      (sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.21/0.45  
% 0.21/0.45  tff(u187,axiom,
% 0.21/0.45      (![X1, X0, X2] : (((k1_xboole_0 != k4_xboole_0(X2,X0)) | (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u186,axiom,
% 0.21/0.45      (![X1, X0, X2] : (((k1_xboole_0 != k4_xboole_0(X1,X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u185,axiom,
% 0.21/0.45      (![X1, X0, X2] : (((k1_xboole_0 != k4_xboole_0(X2,X0)) | (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u184,axiom,
% 0.21/0.45      (![X1, X0] : (((k1_xboole_0 != X0) | (k9_subset_1(k1_xboole_0,X1,X0) = k9_subset_1(k1_xboole_0,X0,X1)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u183,axiom,
% 0.21/0.45      (![X1, X0] : (((k1_xboole_0 != X0) | (k4_xboole_0(X0,X1) = k7_subset_1(k1_xboole_0,X0,X1)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u182,axiom,
% 0.21/0.45      (![X1, X0] : (((k1_xboole_0 != X0) | (k3_xboole_0(X1,X0) = k9_subset_1(k1_xboole_0,X1,X0)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u181,axiom,
% 0.21/0.45      (![X3, X2, X4] : (((k1_xboole_0 != k3_xboole_0(X2,X3)) | (k9_subset_1(k4_xboole_0(X2,X3),X4,X2) = k9_subset_1(k4_xboole_0(X2,X3),X2,X4)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u180,axiom,
% 0.21/0.45      (![X3, X2, X4] : (((k1_xboole_0 != k3_xboole_0(X2,X3)) | (k7_subset_1(k4_xboole_0(X2,X3),X2,X4) = k4_xboole_0(X2,X4)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u179,axiom,
% 0.21/0.45      (![X3, X2, X4] : (((k1_xboole_0 != k3_xboole_0(X2,X3)) | (k9_subset_1(k4_xboole_0(X2,X3),X4,X2) = k3_xboole_0(X4,X2)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u178,axiom,
% 0.21/0.45      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.21/0.45  
% 0.21/0.45  tff(u177,axiom,
% 0.21/0.45      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.21/0.45  
% 0.21/0.45  tff(u176,axiom,
% 0.21/0.45      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 0.21/0.45  
% 0.21/0.45  tff(u175,negated_conjecture,
% 0.21/0.45      (k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)))).
% 0.21/0.45  
% 0.21/0.45  tff(u174,axiom,
% 0.21/0.45      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u173,axiom,
% 0.21/0.45      (![X1, X2] : ((k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u172,negated_conjecture,
% 0.21/0.45      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u171,axiom,
% 0.21/0.45      (![X1, X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1))))).
% 0.21/0.45  
% 0.21/0.45  tff(u170,axiom,
% 0.21/0.45      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u169,negated_conjecture,
% 0.21/0.45      (![X0] : ((k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1))))).
% 0.21/0.45  
% 0.21/0.45  tff(u168,axiom,
% 0.21/0.45      (![X1, X2] : ((k9_subset_1(X1,X2,X1) = k3_xboole_0(X2,X1))))).
% 0.21/0.45  
% 0.21/0.45  tff(u167,negated_conjecture,
% 0.21/0.45      (sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)))).
% 0.21/0.45  
% 0.21/0.45  tff(u166,negated_conjecture,
% 0.21/0.45      (sK1 = k3_xboole_0(u1_struct_0(sK0),sK1))).
% 0.21/0.45  
% 0.21/0.45  tff(u165,negated_conjecture,
% 0.21/0.45      (![X0] : ((k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u164,axiom,
% 0.21/0.45      (![X1, X2] : ((k3_xboole_0(X2,X1) = k9_subset_1(X1,X1,X2))))).
% 0.21/0.45  
% 0.21/0.45  tff(u163,axiom,
% 0.21/0.45      (![X1, X2] : ((k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2))))).
% 0.21/0.45  
% 0.21/0.45  tff(u162,axiom,
% 0.21/0.45      (![X3, X5, X4] : ((~r1_tarski(X5,X3) | (k9_subset_1(X3,X4,X5) = k9_subset_1(X3,X5,X4)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u161,axiom,
% 0.21/0.45      (![X3, X5, X4] : ((~r1_tarski(X4,X3) | (k7_subset_1(X3,X4,X5) = k4_xboole_0(X4,X5)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u160,axiom,
% 0.21/0.45      (![X3, X5, X4] : ((~r1_tarski(X5,X3) | (k9_subset_1(X3,X4,X5) = k3_xboole_0(X4,X5)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u159,axiom,
% 0.21/0.45      (![X1, X0] : ((~r1_tarski(X0,X1) | (k4_xboole_0(X0,X1) = k1_xboole_0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u158,axiom,
% 0.21/0.45      (![X1, X0] : ((r1_tarski(X0,X1) | (k4_xboole_0(X0,X1) != k1_xboole_0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u157,axiom,
% 0.21/0.45      (![X1, X0] : ((r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u156,axiom,
% 0.21/0.45      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u155,axiom,
% 0.21/0.45      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u154,axiom,
% 0.21/0.45      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u153,axiom,
% 0.21/0.45      (![X3, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X3)) | (k1_xboole_0 = k4_xboole_0(X2,X3)))))).
% 0.21/0.45  
% 0.21/0.45  tff(u152,negated_conjecture,
% 0.21/0.45      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.45  
% 0.21/0.45  tff(u151,axiom,
% 0.21/0.45      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u150,axiom,
% 0.21/0.45      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 0.21/0.45  
% 0.21/0.45  tff(u149,negated_conjecture,
% 0.21/0.45      l1_struct_0(sK0)).
% 0.21/0.45  
% 0.21/0.45  % (30653)# SZS output end Saturation.
% 0.21/0.45  % (30653)------------------------------
% 0.21/0.45  % (30653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (30653)Termination reason: Satisfiable
% 0.21/0.45  
% 0.21/0.45  % (30653)Memory used [KB]: 6140
% 0.21/0.45  % (30653)Time elapsed: 0.050 s
% 0.21/0.45  % (30653)------------------------------
% 0.21/0.45  % (30653)------------------------------
% 0.21/0.45  % (30636)Success in time 0.084 s
%------------------------------------------------------------------------------
