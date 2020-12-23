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
% DateTime   : Thu Dec  3 13:08:39 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   25 (  25 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    0
%              Number of atoms          :   32 (  32 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u19,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u24,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u34,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u116,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u71,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

% (32740)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
cnf(u119,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u117,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u118,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u83,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u73,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u20,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u72,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))) )).

cnf(u51,axiom,
    ( k1_xboole_0 = k5_xboole_0(X5,k3_xboole_0(X5,X5)) )).

cnf(u86,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) )).

cnf(u79,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,X2) )).

cnf(u85,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X5) )).

cnf(u16,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u35,axiom,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

cnf(u21,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u75,axiom,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k7_subset_1(X1,X1,X2) )).

cnf(u70,axiom,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2) )).

cnf(u22,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u26,axiom,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

cnf(u33,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:04:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (32743)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (303)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (32742)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (32743)Refutation not found, incomplete strategy% (32743)------------------------------
% 0.21/0.51  % (32743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32743)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32743)Memory used [KB]: 6268
% 0.21/0.51  % (32743)Time elapsed: 0.107 s
% 0.21/0.51  % (32743)------------------------------
% 0.21/0.51  % (32743)------------------------------
% 0.21/0.52  % (32746)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (32746)# SZS output start Saturation.
% 0.21/0.52  cnf(u19,negated_conjecture,
% 0.21/0.52      l1_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u24,axiom,
% 0.21/0.52      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.52  
% 0.21/0.52  cnf(u34,axiom,
% 0.21/0.52      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u18,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u116,negated_conjecture,
% 0.21/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u71,axiom,
% 0.21/0.52      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.52  
% 0.21/0.52  % (32740)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  cnf(u119,negated_conjecture,
% 0.21/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u117,negated_conjecture,
% 0.21/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u118,negated_conjecture,
% 0.21/0.52      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u83,axiom,
% 0.21/0.52      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u73,negated_conjecture,
% 0.21/0.52      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u20,axiom,
% 0.21/0.52      k2_subset_1(X0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u72,axiom,
% 0.21/0.52      k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))).
% 0.21/0.52  
% 0.21/0.52  cnf(u51,axiom,
% 0.21/0.52      k1_xboole_0 = k5_xboole_0(X5,k3_xboole_0(X5,X5))).
% 0.21/0.52  
% 0.21/0.52  cnf(u86,axiom,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u79,axiom,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(X2,X2,X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u85,axiom,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X5)).
% 0.21/0.52  
% 0.21/0.52  cnf(u16,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u35,axiom,
% 0.21/0.52      k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u21,axiom,
% 0.21/0.52      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u75,axiom,
% 0.21/0.52      k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k7_subset_1(X1,X1,X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u70,axiom,
% 0.21/0.52      k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u22,axiom,
% 0.21/0.52      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u26,axiom,
% 0.21/0.52      k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u33,negated_conjecture,
% 0.21/0.52      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.52  
% 0.21/0.52  % (32746)# SZS output end Saturation.
% 0.21/0.52  % (32746)------------------------------
% 0.21/0.52  % (32746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32746)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (32746)Memory used [KB]: 6268
% 0.21/0.52  % (32746)Time elapsed: 0.071 s
% 0.21/0.52  % (32746)------------------------------
% 0.21/0.52  % (32746)------------------------------
% 0.21/0.52  % (32737)Success in time 0.151 s
%------------------------------------------------------------------------------
