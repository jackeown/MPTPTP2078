%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:42 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   32 (  32 expanded)
%              Depth                    :    0
%              Number of atoms          :   49 (  49 expanded)
%              Number of equality atoms :   28 (  28 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u177,negated_conjecture,
    ( ~ ( k2_struct_0(sK0) != sK1 )
    | k2_struct_0(sK0) != sK1 )).

tff(u176,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u175,axiom,(
    ! [X1,X0] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) )).

tff(u174,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u173,axiom,(
    ! [X1,X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) )).

tff(u172,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) )).

tff(u171,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u170,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u169,negated_conjecture,(
    ! [X1] : k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,X1)) )).

tff(u168,axiom,(
    ! [X2] : k1_xboole_0 = k7_subset_1(X2,X2,X2) )).

tff(u167,axiom,(
    ! [X1,X0] : k1_xboole_0 = k7_subset_1(X0,X0,k2_xboole_0(X0,X1)) )).

tff(u166,negated_conjecture,(
    ! [X1] : k1_xboole_0 = k7_subset_1(sK1,sK1,k2_xboole_0(sK1,X1)) )).

tff(u165,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u164,axiom,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u163,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u162,negated_conjecture,(
    u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u161,negated_conjecture,(
    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u160,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u159,axiom,(
    ! [X1,X3,X2] :
      ( ~ r1_tarski(X2,X1)
      | k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3) ) )).

tff(u158,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u157,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u156,negated_conjecture,
    ( ~ ~ r1_tarski(u1_struct_0(sK0),sK1)
    | ~ r1_tarski(u1_struct_0(sK0),sK1) )).

tff(u155,negated_conjecture,
    ( ~ ~ r1_tarski(k2_struct_0(sK0),sK1)
    | ~ r1_tarski(k2_struct_0(sK0),sK1) )).

tff(u154,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u153,negated_conjecture,(
    r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u152,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u151,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u150,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ l1_struct_0(X0) ) )).

tff(u149,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u148,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u147,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) ) )).

tff(u146,negated_conjecture,(
    l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:39:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (16514)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (16518)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (16510)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.50  % (16518)Refutation not found, incomplete strategy% (16518)------------------------------
% 0.20/0.50  % (16518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16518)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16518)Memory used [KB]: 10746
% 0.20/0.50  % (16518)Time elapsed: 0.109 s
% 0.20/0.50  % (16518)------------------------------
% 0.20/0.50  % (16518)------------------------------
% 0.20/0.50  % (16530)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.50  % (16537)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (16537)Refutation not found, incomplete strategy% (16537)------------------------------
% 0.20/0.51  % (16537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16530)Refutation not found, incomplete strategy% (16530)------------------------------
% 0.20/0.51  % (16530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16537)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (16530)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (16537)Memory used [KB]: 1663
% 0.20/0.51  % (16537)Time elapsed: 0.001 s
% 0.20/0.51  % (16530)Memory used [KB]: 6268
% 0.20/0.51  % (16537)------------------------------
% 0.20/0.51  % (16537)------------------------------
% 0.20/0.51  % (16530)Time elapsed: 0.109 s
% 0.20/0.51  % (16530)------------------------------
% 0.20/0.51  % (16530)------------------------------
% 0.20/0.51  % (16519)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.51  % (16519)Refutation not found, incomplete strategy% (16519)------------------------------
% 0.20/0.51  % (16519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16519)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (16519)Memory used [KB]: 6268
% 0.20/0.51  % (16519)Time elapsed: 0.119 s
% 0.20/0.51  % (16519)------------------------------
% 0.20/0.51  % (16519)------------------------------
% 0.20/0.51  % (16512)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (16522)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (16522)Refutation not found, incomplete strategy% (16522)------------------------------
% 0.20/0.51  % (16522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16522)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (16522)Memory used [KB]: 1663
% 0.20/0.51  % (16522)Time elapsed: 0.117 s
% 0.20/0.51  % (16522)------------------------------
% 0.20/0.51  % (16522)------------------------------
% 0.20/0.51  % (16534)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (16514)# SZS output start Saturation.
% 0.20/0.51  tff(u177,negated_conjecture,
% 0.20/0.51      ((~(k2_struct_0(sK0) != sK1)) | (k2_struct_0(sK0) != sK1))).
% 0.20/0.51  
% 0.20/0.51  tff(u176,axiom,
% 0.20/0.51      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.20/0.51  
% 0.20/0.51  tff(u175,axiom,
% 0.20/0.51      (![X1, X0] : ((k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1))))).
% 0.20/0.51  
% 0.20/0.51  tff(u174,axiom,
% 0.20/0.51      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u173,axiom,
% 0.20/0.51      (![X1, X0] : ((k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))))))).
% 0.20/0.51  
% 0.20/0.51  tff(u172,axiom,
% 0.20/0.51      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)))))).
% 0.20/0.51  
% 0.20/0.51  tff(u171,negated_conjecture,
% 0.20/0.51      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.20/0.51  
% 0.20/0.51  tff(u170,negated_conjecture,
% 0.20/0.51      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.20/0.51  
% 0.20/0.51  tff(u169,negated_conjecture,
% 0.20/0.51      (![X1] : ((k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,X1)))))).
% 0.20/0.51  
% 0.20/0.51  tff(u168,axiom,
% 0.20/0.51      (![X2] : ((k1_xboole_0 = k7_subset_1(X2,X2,X2))))).
% 0.20/0.51  
% 0.20/0.51  tff(u167,axiom,
% 0.20/0.51      (![X1, X0] : ((k1_xboole_0 = k7_subset_1(X0,X0,k2_xboole_0(X0,X1)))))).
% 0.20/0.51  
% 0.20/0.51  tff(u166,negated_conjecture,
% 0.20/0.51      (![X1] : ((k1_xboole_0 = k7_subset_1(sK1,sK1,k2_xboole_0(sK1,X1)))))).
% 0.20/0.51  
% 0.20/0.51  tff(u165,axiom,
% 0.20/0.51      (![X0] : ((k2_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.20/0.51  
% 0.20/0.51  tff(u164,axiom,
% 0.20/0.51      (![X0] : ((k7_subset_1(X0,X0,k1_xboole_0) = X0)))).
% 0.20/0.51  
% 0.20/0.51  tff(u163,negated_conjecture,
% 0.20/0.51      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u162,negated_conjecture,
% 0.20/0.51      (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u161,negated_conjecture,
% 0.20/0.51      (sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))).
% 0.20/0.51  
% 0.20/0.51  tff(u160,negated_conjecture,
% 0.20/0.51      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 0.20/0.51  
% 0.20/0.51  tff(u159,axiom,
% 0.20/0.51      (![X1, X3, X2] : ((~r1_tarski(X2,X1) | (k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)))))).
% 0.20/0.51  
% 0.20/0.51  tff(u158,axiom,
% 0.20/0.51      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 0.20/0.51  
% 0.20/0.51  tff(u157,axiom,
% 0.20/0.51      (![X1, X0] : ((~r1_tarski(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 0.20/0.51  
% 0.20/0.51  tff(u156,negated_conjecture,
% 0.20/0.51      ((~~r1_tarski(u1_struct_0(sK0),sK1)) | ~r1_tarski(u1_struct_0(sK0),sK1))).
% 0.20/0.51  
% 0.20/0.51  tff(u155,negated_conjecture,
% 0.20/0.51      ((~~r1_tarski(k2_struct_0(sK0),sK1)) | ~r1_tarski(k2_struct_0(sK0),sK1))).
% 0.20/0.51  
% 0.20/0.51  tff(u154,axiom,
% 0.20/0.51      (![X1] : (r1_tarski(X1,X1)))).
% 0.20/0.51  
% 0.20/0.51  tff(u153,negated_conjecture,
% 0.20/0.51      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  tff(u152,axiom,
% 0.20/0.51      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.20/0.51  
% 0.20/0.51  tff(u151,axiom,
% 0.20/0.51      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.20/0.51  
% 0.20/0.51  tff(u150,axiom,
% 0.20/0.51      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) | ~l1_struct_0(X0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u149,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  tff(u148,axiom,
% 0.20/0.51      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 0.20/0.51  
% 0.20/0.51  tff(u147,axiom,
% 0.20/0.51      (![X0] : ((~l1_struct_0(X0) | (u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))))))).
% 0.20/0.51  
% 0.20/0.51  tff(u146,negated_conjecture,
% 0.20/0.51      l1_struct_0(sK0)).
% 0.20/0.51  
% 0.20/0.51  % (16514)# SZS output end Saturation.
% 0.20/0.51  % (16514)------------------------------
% 0.20/0.51  % (16514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16514)Termination reason: Satisfiable
% 0.20/0.51  
% 0.20/0.51  % (16514)Memory used [KB]: 10746
% 0.20/0.51  % (16514)Time elapsed: 0.119 s
% 0.20/0.51  % (16514)------------------------------
% 0.20/0.51  % (16514)------------------------------
% 0.20/0.51  % (16536)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (16507)Success in time 0.162 s
%------------------------------------------------------------------------------
