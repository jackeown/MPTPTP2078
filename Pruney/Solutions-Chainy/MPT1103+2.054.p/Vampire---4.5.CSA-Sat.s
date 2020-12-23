%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:41 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  42 expanded)
%              Number of leaves         :   42 (  42 expanded)
%              Depth                    :    0
%              Number of atoms          :   59 (  59 expanded)
%              Number of equality atoms :   38 (  38 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u429,negated_conjecture,
    ( ~ ( k2_struct_0(sK0) != sK1 )
    | k2_struct_0(sK0) != sK1 )).

tff(u428,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u427,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

tff(u426,axiom,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

tff(u425,axiom,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )).

tff(u424,axiom,(
    ! [X1] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,k7_subset_1(k1_xboole_0,k1_xboole_0,X1))) )).

tff(u423,axiom,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(k1_xboole_0,X1)) )).

tff(u422,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) )).

tff(u421,axiom,(
    ! [X1] : k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

tff(u420,axiom,(
    ! [X3,X2] : k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

tff(u419,axiom,(
    ! [X2] : k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,k5_xboole_0(k1_xboole_0,X2)) )).

tff(u418,axiom,(
    ! [X0] : k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,k7_subset_1(k1_xboole_0,k1_xboole_0,X0)) )).

tff(u417,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u416,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u415,negated_conjecture,(
    ! [X1] : k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k7_subset_1(X1,X1,sK1))) )).

tff(u414,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(sK1,sK1,sK1) )).

tff(u413,negated_conjecture,(
    ! [X1] : k1_xboole_0 = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k7_subset_1(X1,X1,sK1))) )).

tff(u412,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u411,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u410,axiom,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u409,axiom,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

tff(u408,axiom,(
    ! [X1,X0] : k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))) = X0 )).

tff(u407,negated_conjecture,(
    u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u406,negated_conjecture,(
    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u405,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u404,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) )).

tff(u403,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u402,negated_conjecture,
    ( ~ ~ r1_tarski(k5_xboole_0(k5_xboole_0(sK1,sK1),sK1),k5_xboole_0(sK1,sK1))
    | ~ r1_tarski(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0) )).

tff(u401,axiom,(
    ! [X1] :
      ( ~ r1_tarski(k5_xboole_0(k1_xboole_0,X1),k1_xboole_0)
      | k1_xboole_0 = k5_xboole_0(k1_xboole_0,X1) ) )).

tff(u400,axiom,(
    ! [X3,X2] :
      ( ~ r1_tarski(k5_xboole_0(X2,k7_subset_1(X3,X3,X2)),X2)
      | k5_xboole_0(X2,k7_subset_1(X3,X3,X2)) = X2 ) )).

tff(u399,axiom,(
    ! [X1] :
      ( ~ r1_tarski(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k1_xboole_0)
      | k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1) ) )).

tff(u398,negated_conjecture,
    ( ~ ~ r1_tarski(k2_struct_0(sK0),sK1)
    | ~ r1_tarski(k2_struct_0(sK0),sK1) )).

tff(u397,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u396,axiom,(
    ! [X1,X0] : r1_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) )).

tff(u395,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) )).

tff(u394,axiom,(
    ! [X2] : r1_tarski(k1_xboole_0,k7_subset_1(k1_xboole_0,k1_xboole_0,X2)) )).

tff(u393,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ l1_struct_0(X0) ) )).

tff(u392,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u391,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u390,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u389,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) ) )).

tff(u388,negated_conjecture,(
    l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (11547)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (11546)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (11565)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (11549)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (11557)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (11550)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (11557)Refutation not found, incomplete strategy% (11557)------------------------------
% 0.21/0.52  % (11557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11548)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (11557)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11557)Memory used [KB]: 1663
% 0.21/0.52  % (11557)Time elapsed: 0.057 s
% 0.21/0.52  % (11557)------------------------------
% 0.21/0.52  % (11557)------------------------------
% 0.21/0.52  % (11565)Refutation not found, incomplete strategy% (11565)------------------------------
% 0.21/0.52  % (11565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11565)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11565)Memory used [KB]: 6268
% 0.21/0.52  % (11565)Time elapsed: 0.060 s
% 0.21/0.52  % (11565)------------------------------
% 0.21/0.52  % (11565)------------------------------
% 0.21/0.52  % (11553)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (11554)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (11554)Refutation not found, incomplete strategy% (11554)------------------------------
% 0.21/0.53  % (11554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11554)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11554)Memory used [KB]: 10618
% 0.21/0.53  % (11554)Time elapsed: 0.109 s
% 0.21/0.53  % (11554)------------------------------
% 0.21/0.53  % (11554)------------------------------
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (11548)# SZS output start Saturation.
% 0.21/0.53  tff(u429,negated_conjecture,
% 0.21/0.53      ((~(k2_struct_0(sK0) != sK1)) | (k2_struct_0(sK0) != sK1))).
% 0.21/0.53  
% 0.21/0.53  tff(u428,axiom,
% 0.21/0.53      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.21/0.53  
% 0.21/0.53  tff(u427,axiom,
% 0.21/0.53      (![X1, X2] : ((k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2))))).
% 0.21/0.53  
% 0.21/0.53  tff(u426,axiom,
% 0.21/0.53      (![X0] : ((k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u425,axiom,
% 0.21/0.53      (![X0] : ((k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u424,axiom,
% 0.21/0.53      (![X1] : ((k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,k7_subset_1(k1_xboole_0,k1_xboole_0,X1))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u423,axiom,
% 0.21/0.53      (![X1] : ((k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(k1_xboole_0,X1)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u422,axiom,
% 0.21/0.53      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,X0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u421,axiom,
% 0.21/0.53      (![X1] : ((k1_xboole_0 = k7_subset_1(X1,X1,X1))))).
% 0.21/0.53  
% 0.21/0.53  tff(u420,axiom,
% 0.21/0.53      (![X3, X2] : ((k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u419,axiom,
% 0.21/0.53      (![X2] : ((k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,k5_xboole_0(k1_xboole_0,X2)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u418,axiom,
% 0.21/0.53      (![X0] : ((k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,k7_subset_1(k1_xboole_0,k1_xboole_0,X0)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u417,negated_conjecture,
% 0.21/0.53      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.21/0.53  
% 0.21/0.53  tff(u416,negated_conjecture,
% 0.21/0.53      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.21/0.53  
% 0.21/0.53  tff(u415,negated_conjecture,
% 0.21/0.53      (![X1] : ((k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k7_subset_1(X1,X1,sK1))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u414,negated_conjecture,
% 0.21/0.53      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(sK1,sK1,sK1)))).
% 0.21/0.53  
% 0.21/0.53  tff(u413,negated_conjecture,
% 0.21/0.53      (![X1] : ((k1_xboole_0 = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k7_subset_1(X1,X1,sK1))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u412,axiom,
% 0.21/0.53      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.21/0.53  
% 0.21/0.53  tff(u411,negated_conjecture,
% 0.21/0.53      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u410,axiom,
% 0.21/0.53      (![X0] : ((k7_subset_1(X0,X0,k1_xboole_0) = X0)))).
% 0.21/0.53  
% 0.21/0.53  tff(u409,axiom,
% 0.21/0.53      (![X0] : ((k1_setfam_1(k2_tarski(X0,X0)) = X0)))).
% 0.21/0.53  
% 0.21/0.53  tff(u408,axiom,
% 0.21/0.53      (![X1, X0] : ((k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))) = X0)))).
% 0.21/0.53  
% 0.21/0.53  tff(u407,negated_conjecture,
% 0.21/0.53      (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u406,negated_conjecture,
% 0.21/0.53      (sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))).
% 0.21/0.53  
% 0.21/0.53  tff(u405,negated_conjecture,
% 0.21/0.53      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 0.21/0.53  
% 0.21/0.53  tff(u404,axiom,
% 0.21/0.53      (![X1, X0] : ((~r1_tarski(X0,X1) | (k1_setfam_1(k2_tarski(X0,X1)) = X0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u403,axiom,
% 0.21/0.53      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 0.21/0.53  
% 0.21/0.53  tff(u402,negated_conjecture,
% 0.21/0.53      ((~~r1_tarski(k5_xboole_0(k5_xboole_0(sK1,sK1),sK1),k5_xboole_0(sK1,sK1))) | ~r1_tarski(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0))).
% 0.21/0.53  
% 0.21/0.53  tff(u401,axiom,
% 0.21/0.53      (![X1] : ((~r1_tarski(k5_xboole_0(k1_xboole_0,X1),k1_xboole_0) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,X1)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u400,axiom,
% 0.21/0.53      (![X3, X2] : ((~r1_tarski(k5_xboole_0(X2,k7_subset_1(X3,X3,X2)),X2) | (k5_xboole_0(X2,k7_subset_1(X3,X3,X2)) = X2))))).
% 0.21/0.53  
% 0.21/0.53  tff(u399,axiom,
% 0.21/0.53      (![X1] : ((~r1_tarski(k7_subset_1(k1_xboole_0,k1_xboole_0,X1),k1_xboole_0) | (k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u398,negated_conjecture,
% 0.21/0.53      ((~~r1_tarski(k2_struct_0(sK0),sK1)) | ~r1_tarski(k2_struct_0(sK0),sK1))).
% 0.21/0.53  
% 0.21/0.53  tff(u397,axiom,
% 0.21/0.53      (![X1] : (r1_tarski(X1,X1)))).
% 0.21/0.53  
% 0.21/0.53  tff(u396,axiom,
% 0.21/0.53      (![X1, X0] : (r1_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u395,axiom,
% 0.21/0.53      (![X0] : (r1_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u394,axiom,
% 0.21/0.53      (![X2] : (r1_tarski(k1_xboole_0,k7_subset_1(k1_xboole_0,k1_xboole_0,X2))))).
% 0.21/0.53  
% 0.21/0.53  tff(u393,axiom,
% 0.21/0.53      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) | ~l1_struct_0(X0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u392,axiom,
% 0.21/0.53      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.21/0.53  
% 0.21/0.53  tff(u391,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.53  
% 0.21/0.53  tff(u390,axiom,
% 0.21/0.53      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u389,axiom,
% 0.21/0.53      (![X0] : ((~l1_struct_0(X0) | (u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u388,negated_conjecture,
% 0.21/0.53      l1_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  % (11548)# SZS output end Saturation.
% 0.21/0.53  % (11548)------------------------------
% 0.21/0.53  % (11548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11548)Termination reason: Satisfiable
% 0.21/0.53  
% 0.21/0.53  % (11548)Memory used [KB]: 10874
% 0.21/0.53  % (11548)Time elapsed: 0.077 s
% 0.21/0.53  % (11548)------------------------------
% 0.21/0.53  % (11548)------------------------------
% 0.21/0.53  % (11538)Success in time 0.171 s
%------------------------------------------------------------------------------
