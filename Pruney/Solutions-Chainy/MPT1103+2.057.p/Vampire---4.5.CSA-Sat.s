%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:41 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   29 (  29 expanded)
%              Number of leaves         :   29 (  29 expanded)
%              Depth                    :    0
%              Number of atoms          :   44 (  44 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u22,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u31,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u38,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) )).

cnf(u42,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u57,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u37,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u43,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u40,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u51,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | u1_struct_0(sK0) = sK1 )).

cnf(u60,negated_conjecture,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u33,axiom,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 )).

cnf(u36,axiom,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 )).

cnf(u54,axiom,
    ( ~ r1_tarski(X4,X3)
    | k7_subset_1(X3,X4,X5) = k4_xboole_0(X4,X5) )).

cnf(u61,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | k2_struct_0(sK0) = sK1 )).

cnf(u58,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u59,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u53,axiom,
    ( k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u27,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) = sK1 )).

cnf(u52,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u49,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u48,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u32,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) )).

cnf(u47,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u46,axiom,
    ( k2_xboole_0(X0,X0) = X0 )).

cnf(u29,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u28,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u24,negated_conjecture,
    ( k2_struct_0(sK0) != sK1
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:52:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (3444)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (3444)Refutation not found, incomplete strategy% (3444)------------------------------
% 0.21/0.50  % (3444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3444)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3444)Memory used [KB]: 10618
% 0.21/0.50  % (3444)Time elapsed: 0.080 s
% 0.21/0.50  % (3444)------------------------------
% 0.21/0.50  % (3444)------------------------------
% 0.21/0.50  % (3450)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (3433)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (3446)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (3433)Refutation not found, incomplete strategy% (3433)------------------------------
% 0.21/0.52  % (3433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3433)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3433)Memory used [KB]: 10618
% 0.21/0.52  % (3433)Time elapsed: 0.075 s
% 0.21/0.52  % (3433)------------------------------
% 0.21/0.52  % (3433)------------------------------
% 0.21/0.52  % (3455)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (3454)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (3439)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (3440)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (3454)# SZS output start Saturation.
% 0.21/0.53  cnf(u22,negated_conjecture,
% 0.21/0.53      l1_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u31,axiom,
% 0.21/0.53      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.53  
% 0.21/0.53  cnf(u38,axiom,
% 0.21/0.53      m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u42,axiom,
% 0.21/0.53      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u23,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.53  
% 0.21/0.53  cnf(u57,negated_conjecture,
% 0.21/0.53      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u37,axiom,
% 0.21/0.53      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u39,axiom,
% 0.21/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u43,negated_conjecture,
% 0.21/0.53      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u40,axiom,
% 0.21/0.53      r1_tarski(X1,X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u51,negated_conjecture,
% 0.21/0.53      ~r1_tarski(u1_struct_0(sK0),sK1) | u1_struct_0(sK0) = sK1).
% 0.21/0.53  
% 0.21/0.53  cnf(u60,negated_conjecture,
% 0.21/0.53      ~r1_tarski(X0,u1_struct_0(sK0)) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u33,axiom,
% 0.21/0.53      ~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1).
% 0.21/0.53  
% 0.21/0.53  cnf(u36,axiom,
% 0.21/0.53      ~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1).
% 0.21/0.53  
% 0.21/0.53  cnf(u54,axiom,
% 0.21/0.53      ~r1_tarski(X4,X3) | k7_subset_1(X3,X4,X5) = k4_xboole_0(X4,X5)).
% 0.21/0.53  
% 0.21/0.53  cnf(u61,negated_conjecture,
% 0.21/0.53      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | k2_struct_0(sK0) = sK1).
% 0.21/0.53  
% 0.21/0.53  cnf(u58,negated_conjecture,
% 0.21/0.53      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.53  
% 0.21/0.53  cnf(u59,negated_conjecture,
% 0.21/0.53      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.53  
% 0.21/0.53  cnf(u53,axiom,
% 0.21/0.53      k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u27,negated_conjecture,
% 0.21/0.53      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) = sK1).
% 0.21/0.53  
% 0.21/0.53  cnf(u52,negated_conjecture,
% 0.21/0.53      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u49,negated_conjecture,
% 0.21/0.53      k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u48,axiom,
% 0.21/0.53      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u32,axiom,
% 0.21/0.53      k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))).
% 0.21/0.53  
% 0.21/0.53  cnf(u47,negated_conjecture,
% 0.21/0.53      u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u46,axiom,
% 0.21/0.53      k2_xboole_0(X0,X0) = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u29,axiom,
% 0.21/0.53      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u28,axiom,
% 0.21/0.53      k2_subset_1(X0) = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u24,negated_conjecture,
% 0.21/0.53      k2_struct_0(sK0) != sK1 | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.53  
% 0.21/0.53  % (3454)# SZS output end Saturation.
% 0.21/0.53  % (3454)------------------------------
% 0.21/0.53  % (3454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3454)Termination reason: Satisfiable
% 0.21/0.53  
% 0.21/0.53  % (3454)Memory used [KB]: 6140
% 0.21/0.53  % (3454)Time elapsed: 0.095 s
% 0.21/0.53  % (3454)------------------------------
% 0.21/0.53  % (3454)------------------------------
% 0.21/0.53  % (3432)Success in time 0.17 s
%------------------------------------------------------------------------------
