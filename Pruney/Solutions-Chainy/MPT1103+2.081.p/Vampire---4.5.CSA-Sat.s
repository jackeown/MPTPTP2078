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
% DateTime   : Thu Dec  3 13:08:44 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   35 (  35 expanded)
%              Number of leaves         :   35 (  35 expanded)
%              Depth                    :    0
%              Number of atoms          :   47 (  47 expanded)
%              Number of equality atoms :   34 (  34 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u24,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u30,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u43,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u27,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u81,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u73,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k9_subset_1(X0,X1,X2) = k1_setfam_1(k1_enumset1(X1,X1,X2)) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) )).

cnf(u76,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k9_subset_1(X2,X1,X2) = k7_subset_1(X2,X1,k1_xboole_0) )).

cnf(u75,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | k7_subset_1(X4,X3,X4) = k9_subset_1(X4,X3,k3_subset_1(X4,X4)) )).

cnf(u82,axiom,
    ( k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X3)) = k7_subset_1(X3,k1_xboole_0,k1_xboole_0) )).

cnf(u46,axiom,
    ( k9_subset_1(X3,X4,X3) = k1_setfam_1(k1_enumset1(X4,X4,X3)) )).

cnf(u45,axiom,
    ( k9_subset_1(X1,X2,k1_xboole_0) = k1_setfam_1(k1_enumset1(X2,X2,k1_xboole_0)) )).

cnf(u97,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u94,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u96,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u77,negated_conjecture,
    ( k9_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

cnf(u78,axiom,
    ( k9_subset_1(X0,k1_xboole_0,X0) = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

cnf(u95,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) )).

cnf(u21,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u104,axiom,
    ( k7_subset_1(X1,X1,X1) = k9_subset_1(X1,X1,k3_subset_1(X1,X1)) )).

cnf(u103,axiom,
    ( k7_subset_1(X0,k1_xboole_0,X0) = k9_subset_1(X0,k1_xboole_0,k3_subset_1(X0,X0)) )).

cnf(u102,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u101,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u100,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = k9_subset_1(u1_struct_0(sK0),k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) )).

% (15024)Refutation not found, incomplete strategy% (15024)------------------------------
% (15024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
cnf(u99,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u49,axiom,
    ( k1_xboole_0 = k9_subset_1(X3,k1_xboole_0,k1_xboole_0) )).

% (15024)Termination reason: Refutation not found, incomplete strategy

cnf(u48,axiom,
    ( k9_subset_1(X1,X0,k1_xboole_0) = k9_subset_1(X2,X0,k1_xboole_0) )).

% (15024)Memory used [KB]: 10618
cnf(u47,negated_conjecture,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(sK1,X0,sK1) )).

% (15024)Time elapsed: 0.107 s
cnf(u40,axiom,
    ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 )).

% (15024)------------------------------
% (15024)------------------------------
cnf(u80,axiom,
    ( k7_subset_1(X1,X1,k1_xboole_0) = X1 )).

cnf(u38,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u65,axiom,
    ( k9_subset_1(X0,X0,X0) = X0 )).

cnf(u42,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (15033)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.50  % (15018)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (15018)Refutation not found, incomplete strategy% (15018)------------------------------
% 0.21/0.50  % (15018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15033)Refutation not found, incomplete strategy% (15033)------------------------------
% 0.21/0.51  % (15033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15041)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (15018)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15018)Memory used [KB]: 6268
% 0.21/0.51  % (15018)Time elapsed: 0.088 s
% 0.21/0.51  % (15018)------------------------------
% 0.21/0.51  % (15018)------------------------------
% 0.21/0.52  % (15020)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (15033)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15033)Memory used [KB]: 10874
% 0.21/0.52  % (15033)Time elapsed: 0.106 s
% 0.21/0.52  % (15033)------------------------------
% 0.21/0.52  % (15033)------------------------------
% 0.21/0.52  % (15025)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (15024)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (15025)Refutation not found, incomplete strategy% (15025)------------------------------
% 0.21/0.52  % (15025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15025)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15025)Memory used [KB]: 10618
% 0.21/0.52  % (15025)Time elapsed: 0.109 s
% 0.21/0.52  % (15025)------------------------------
% 0.21/0.52  % (15025)------------------------------
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (15020)# SZS output start Saturation.
% 0.21/0.52  cnf(u24,negated_conjecture,
% 0.21/0.52      l1_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u30,axiom,
% 0.21/0.52      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.52  
% 0.21/0.52  cnf(u43,axiom,
% 0.21/0.52      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u27,axiom,
% 0.21/0.52      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u23,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u81,negated_conjecture,
% 0.21/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u73,negated_conjecture,
% 0.21/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u41,axiom,
% 0.21/0.52      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k1_enumset1(X1,X1,X2))).
% 0.21/0.52  
% 0.21/0.52  cnf(u34,axiom,
% 0.21/0.52      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))).
% 0.21/0.52  
% 0.21/0.52  cnf(u76,axiom,
% 0.21/0.52      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | k9_subset_1(X2,X1,X2) = k7_subset_1(X2,X1,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u75,axiom,
% 0.21/0.52      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | k7_subset_1(X4,X3,X4) = k9_subset_1(X4,X3,k3_subset_1(X4,X4))).
% 0.21/0.52  
% 0.21/0.52  cnf(u82,axiom,
% 0.21/0.52      k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X3)) = k7_subset_1(X3,k1_xboole_0,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u46,axiom,
% 0.21/0.52      k9_subset_1(X3,X4,X3) = k1_setfam_1(k1_enumset1(X4,X4,X3))).
% 0.21/0.52  
% 0.21/0.52  cnf(u45,axiom,
% 0.21/0.52      k9_subset_1(X1,X2,k1_xboole_0) = k1_setfam_1(k1_enumset1(X2,X2,k1_xboole_0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u97,negated_conjecture,
% 0.21/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u94,negated_conjecture,
% 0.21/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u96,negated_conjecture,
% 0.21/0.52      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u77,negated_conjecture,
% 0.21/0.52      k9_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u78,axiom,
% 0.21/0.52      k9_subset_1(X0,k1_xboole_0,X0) = k7_subset_1(X0,k1_xboole_0,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u95,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u21,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u104,axiom,
% 0.21/0.52      k7_subset_1(X1,X1,X1) = k9_subset_1(X1,X1,k3_subset_1(X1,X1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u103,axiom,
% 0.21/0.52      k7_subset_1(X0,k1_xboole_0,X0) = k9_subset_1(X0,k1_xboole_0,k3_subset_1(X0,X0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u102,negated_conjecture,
% 0.21/0.52      k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u101,negated_conjecture,
% 0.21/0.52      k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u100,negated_conjecture,
% 0.21/0.52      k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = k9_subset_1(u1_struct_0(sK0),k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.52  
% 0.21/0.52  % (15024)Refutation not found, incomplete strategy% (15024)------------------------------
% 0.21/0.52  % (15024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  cnf(u99,negated_conjecture,
% 0.21/0.52      k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u49,axiom,
% 0.21/0.52      k1_xboole_0 = k9_subset_1(X3,k1_xboole_0,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  % (15024)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  cnf(u48,axiom,
% 0.21/0.52      k9_subset_1(X1,X0,k1_xboole_0) = k9_subset_1(X2,X0,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  % (15024)Memory used [KB]: 10618
% 0.21/0.52  cnf(u47,negated_conjecture,
% 0.21/0.52      k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(sK1,X0,sK1)).
% 0.21/0.52  
% 0.21/0.52  % (15024)Time elapsed: 0.107 s
% 0.21/0.52  cnf(u40,axiom,
% 0.21/0.52      k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0).
% 0.21/0.52  
% 0.21/0.52  % (15024)------------------------------
% 0.21/0.52  % (15024)------------------------------
% 0.21/0.52  cnf(u80,axiom,
% 0.21/0.52      k7_subset_1(X1,X1,k1_xboole_0) = X1).
% 0.21/0.52  
% 0.21/0.52  cnf(u38,axiom,
% 0.21/0.52      k3_subset_1(X0,k1_xboole_0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u65,axiom,
% 0.21/0.52      k9_subset_1(X0,X0,X0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u42,negated_conjecture,
% 0.21/0.52      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.52  
% 0.21/0.52  % (15020)# SZS output end Saturation.
% 0.21/0.52  % (15020)------------------------------
% 0.21/0.52  % (15020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15020)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (15020)Memory used [KB]: 6268
% 0.21/0.52  % (15020)Time elapsed: 0.110 s
% 0.21/0.52  % (15020)------------------------------
% 0.21/0.52  % (15020)------------------------------
% 0.21/0.52  % (15014)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (15014)Refutation not found, incomplete strategy% (15014)------------------------------
% 0.21/0.52  % (15014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15014)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15014)Memory used [KB]: 1663
% 0.21/0.52  % (15014)Time elapsed: 0.106 s
% 0.21/0.52  % (15014)------------------------------
% 0.21/0.52  % (15014)------------------------------
% 0.21/0.53  % (15040)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (15023)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (15019)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (15015)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (15031)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (15032)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (15026)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (15019)Refutation not found, incomplete strategy% (15019)------------------------------
% 0.21/0.53  % (15019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15019)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15019)Memory used [KB]: 6268
% 0.21/0.53  % (15019)Time elapsed: 0.122 s
% 0.21/0.53  % (15019)------------------------------
% 0.21/0.53  % (15019)------------------------------
% 0.21/0.53  % (15031)Refutation not found, incomplete strategy% (15031)------------------------------
% 0.21/0.53  % (15031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15031)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15031)Memory used [KB]: 10618
% 0.21/0.53  % (15031)Time elapsed: 0.134 s
% 0.21/0.53  % (15031)------------------------------
% 0.21/0.53  % (15031)------------------------------
% 0.21/0.54  % (15017)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (15016)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (15043)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (15013)Success in time 0.174 s
%------------------------------------------------------------------------------
