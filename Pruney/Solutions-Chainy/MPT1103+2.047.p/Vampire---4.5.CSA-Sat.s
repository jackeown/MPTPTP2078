%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:40 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    0
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u19,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u28,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u44,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u35,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u33,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_xboole_0 = k4_xboole_0(X0,X1) )).

cnf(u31,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u47,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | k2_struct_0(sK0) = sK1 )).

cnf(u45,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u43,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u26,axiom,
    ( k1_zfmisc_1(X0) = k9_setfam_1(X0) )).

cnf(u27,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u39,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u25,axiom,
    ( k1_xboole_0 = o_0_0_xboole_0 )).

cnf(u24,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) = sK1 )).

cnf(u38,axiom,
    ( k1_xboole_0 != X0
    | r1_tarski(X0,k1_xboole_0) )).

cnf(u32,axiom,
    ( k1_xboole_0 != k4_xboole_0(X0,X1)
    | r1_tarski(X0,X1) )).

cnf(u21,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) != sK1 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n021.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:12:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (26056)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (26056)Refutation not found, incomplete strategy% (26056)------------------------------
% 0.22/0.48  % (26056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (26056)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (26056)Memory used [KB]: 1663
% 0.22/0.48  % (26056)Time elapsed: 0.085 s
% 0.22/0.48  % (26056)------------------------------
% 0.22/0.48  % (26056)------------------------------
% 0.22/0.49  % (26080)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (26072)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.49  % (26064)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.49  % (26080)Refutation not found, incomplete strategy% (26080)------------------------------
% 0.22/0.49  % (26080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (26080)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (26080)Memory used [KB]: 1663
% 0.22/0.49  % (26080)Time elapsed: 0.005 s
% 0.22/0.49  % (26080)------------------------------
% 0.22/0.49  % (26080)------------------------------
% 0.22/0.50  % (26051)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.50  % (26064)Refutation not found, incomplete strategy% (26064)------------------------------
% 0.22/0.50  % (26064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26072)Refutation not found, incomplete strategy% (26072)------------------------------
% 0.22/0.50  % (26072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26072)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (26072)Memory used [KB]: 6268
% 0.22/0.50  % (26072)Time elapsed: 0.112 s
% 0.22/0.50  % (26072)------------------------------
% 0.22/0.50  % (26072)------------------------------
% 0.22/0.50  % (26064)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (26064)Memory used [KB]: 6268
% 0.22/0.50  % (26064)Time elapsed: 0.110 s
% 0.22/0.50  % (26064)------------------------------
% 0.22/0.50  % (26064)------------------------------
% 0.22/0.51  % (26058)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (26055)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (26075)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.51  % (26066)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.51  % (26058)# SZS output start Saturation.
% 0.22/0.51  cnf(u19,negated_conjecture,
% 0.22/0.51      l1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u28,axiom,
% 0.22/0.51      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.22/0.51  
% 0.22/0.51  cnf(u20,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.51  
% 0.22/0.51  cnf(u44,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u34,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u35,axiom,
% 0.22/0.51      r1_tarski(X1,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u33,axiom,
% 0.22/0.51      ~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u31,axiom,
% 0.22/0.51      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u47,negated_conjecture,
% 0.22/0.51      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | k2_struct_0(sK0) = sK1).
% 0.22/0.51  
% 0.22/0.51  cnf(u45,negated_conjecture,
% 0.22/0.51      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u43,negated_conjecture,
% 0.22/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u26,axiom,
% 0.22/0.51      k1_zfmisc_1(X0) = k9_setfam_1(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u27,axiom,
% 0.22/0.51      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u39,axiom,
% 0.22/0.51      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u25,axiom,
% 0.22/0.51      k1_xboole_0 = o_0_0_xboole_0).
% 0.22/0.51  
% 0.22/0.51  cnf(u24,negated_conjecture,
% 0.22/0.51      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) = sK1).
% 0.22/0.51  
% 0.22/0.51  cnf(u38,axiom,
% 0.22/0.51      k1_xboole_0 != X0 | r1_tarski(X0,k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u32,axiom,
% 0.22/0.51      k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u21,negated_conjecture,
% 0.22/0.51      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) != sK1).
% 0.22/0.51  
% 0.22/0.51  % (26058)# SZS output end Saturation.
% 0.22/0.51  % (26058)------------------------------
% 0.22/0.51  % (26058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26058)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (26058)Memory used [KB]: 1663
% 0.22/0.51  % (26058)Time elapsed: 0.094 s
% 0.22/0.51  % (26058)------------------------------
% 0.22/0.51  % (26058)------------------------------
% 0.22/0.52  % (26050)Success in time 0.152 s
%------------------------------------------------------------------------------
