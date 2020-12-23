%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:46 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u28,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u41,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u57,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u46,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u60,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u58,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u59,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u52,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u47,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u24,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u37,axiom,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 )).

cnf(u43,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u38,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )).

cnf(u50,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) )).

cnf(u53,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u20,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u25,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u45,axiom,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2) )).

cnf(u26,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u30,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

cnf(u40,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (29844)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (29848)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (29850)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (29849)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (29844)Refutation not found, incomplete strategy% (29844)------------------------------
% 0.21/0.50  % (29844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29844)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29844)Memory used [KB]: 1663
% 0.21/0.50  % (29844)Time elapsed: 0.093 s
% 0.21/0.50  % (29844)------------------------------
% 0.21/0.50  % (29844)------------------------------
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (29846)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (29858)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (29850)# SZS output start Saturation.
% 0.21/0.51  cnf(u23,negated_conjecture,
% 0.21/0.51      l1_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u28,axiom,
% 0.21/0.51      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.51  
% 0.21/0.51  cnf(u41,axiom,
% 0.21/0.51      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u22,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u57,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u46,axiom,
% 0.21/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u60,negated_conjecture,
% 0.21/0.51      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u58,negated_conjecture,
% 0.21/0.51      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u59,negated_conjecture,
% 0.21/0.51      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u52,axiom,
% 0.21/0.51      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u47,negated_conjecture,
% 0.21/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u24,axiom,
% 0.21/0.51      k2_subset_1(X0) = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u37,axiom,
% 0.21/0.51      k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u43,axiom,
% 0.21/0.51      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u38,axiom,
% 0.21/0.51      k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))))).
% 0.21/0.51  
% 0.21/0.51  cnf(u50,axiom,
% 0.21/0.51      k1_xboole_0 = k7_subset_1(X0,X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u53,axiom,
% 0.21/0.51      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u20,negated_conjecture,
% 0.21/0.51      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u25,axiom,
% 0.21/0.51      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u45,axiom,
% 0.21/0.51      k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u26,axiom,
% 0.21/0.51      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u30,axiom,
% 0.21/0.51      k3_xboole_0(X0,X0) = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u40,negated_conjecture,
% 0.21/0.51      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.51  
% 0.21/0.51  % (29850)# SZS output end Saturation.
% 0.21/0.51  % (29850)------------------------------
% 0.21/0.51  % (29850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29850)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (29850)Memory used [KB]: 6268
% 0.21/0.51  % (29850)Time elapsed: 0.100 s
% 0.21/0.51  % (29850)------------------------------
% 0.21/0.51  % (29850)------------------------------
% 0.21/0.51  % (29843)Success in time 0.155 s
%------------------------------------------------------------------------------
