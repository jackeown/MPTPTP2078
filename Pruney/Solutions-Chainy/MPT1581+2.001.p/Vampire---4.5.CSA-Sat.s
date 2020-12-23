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
% DateTime   : Thu Dec  3 13:16:22 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   45 (  45 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u31,negated_conjecture,
    ( m1_yellow_0(sK1,sK0) )).

cnf(u50,negated_conjecture,
    ( r1_orders_2(sK1,sK2,sK3) )).

cnf(u39,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK3) )).

cnf(u30,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u47,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u52,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) )).

cnf(u51,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) )).

cnf(u33,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u32,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | r2_hidden(X0,X1) )).

cnf(u46,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u48,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2)
    | ~ r2_hidden(X0,X1) )).

cnf(u44,axiom,
    ( r2_hidden(sK6(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u55,negated_conjecture,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u54,negated_conjecture,
    ( r2_hidden(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u56,negated_conjecture,
    ( r2_hidden(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u53,negated_conjecture,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u40,axiom,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u41,axiom,
    ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u43,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ r2_hidden(X2,X0) )).

% (1734)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
cnf(u42,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | v1_xboole_0(X1) )).

cnf(u37,negated_conjecture,
    ( sK3 = sK5 )).

cnf(u36,negated_conjecture,
    ( sK2 = sK4 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:35:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (1730)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.52  % (1739)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.52  % (1738)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.52  % (1739)Refutation not found, incomplete strategy% (1739)------------------------------
% 0.20/0.52  % (1739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (1739)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (1739)Memory used [KB]: 10490
% 0.20/0.52  % (1739)Time elapsed: 0.105 s
% 0.20/0.52  % (1739)------------------------------
% 0.20/0.52  % (1739)------------------------------
% 0.20/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.52  % (1738)# SZS output start Saturation.
% 0.20/0.52  cnf(u31,negated_conjecture,
% 0.20/0.52      m1_yellow_0(sK1,sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u50,negated_conjecture,
% 0.20/0.52      r1_orders_2(sK1,sK2,sK3)).
% 0.20/0.52  
% 0.20/0.52  cnf(u39,negated_conjecture,
% 0.20/0.52      ~r1_orders_2(sK0,sK2,sK3)).
% 0.20/0.52  
% 0.20/0.52  cnf(u30,negated_conjecture,
% 0.20/0.52      l1_orders_2(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u47,axiom,
% 0.20/0.52      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.20/0.52  
% 0.20/0.52  cnf(u52,negated_conjecture,
% 0.20/0.52      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.20/0.52  
% 0.20/0.52  cnf(u51,negated_conjecture,
% 0.20/0.52      m1_subset_1(sK3,u1_struct_0(sK1))).
% 0.20/0.52  
% 0.20/0.52  cnf(u33,negated_conjecture,
% 0.20/0.52      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u32,negated_conjecture,
% 0.20/0.52      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u45,axiom,
% 0.20/0.52      ~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u46,axiom,
% 0.20/0.52      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u48,axiom,
% 0.20/0.52      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u44,axiom,
% 0.20/0.52      r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u55,negated_conjecture,
% 0.20/0.52      r2_hidden(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))).
% 0.20/0.52  
% 0.20/0.52  cnf(u54,negated_conjecture,
% 0.20/0.52      r2_hidden(sK3,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u56,negated_conjecture,
% 0.20/0.52      r2_hidden(sK2,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))).
% 0.20/0.52  
% 0.20/0.52  cnf(u53,negated_conjecture,
% 0.20/0.52      r2_hidden(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u40,axiom,
% 0.20/0.52      r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u41,axiom,
% 0.20/0.52      ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u43,axiom,
% 0.20/0.52      ~v1_xboole_0(X0) | ~r2_hidden(X2,X0)).
% 0.20/0.52  
% 0.20/0.52  % (1734)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.52  cnf(u42,axiom,
% 0.20/0.52      ~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u37,negated_conjecture,
% 0.20/0.52      sK3 = sK5).
% 0.20/0.52  
% 0.20/0.52  cnf(u36,negated_conjecture,
% 0.20/0.52      sK2 = sK4).
% 0.20/0.52  
% 0.20/0.52  % (1738)# SZS output end Saturation.
% 0.20/0.52  % (1738)------------------------------
% 0.20/0.52  % (1738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (1738)Termination reason: Satisfiable
% 0.20/0.52  
% 0.20/0.52  % (1738)Memory used [KB]: 1663
% 0.20/0.52  % (1738)Time elapsed: 0.099 s
% 0.20/0.52  % (1738)------------------------------
% 0.20/0.52  % (1738)------------------------------
% 0.20/0.52  % (1728)Success in time 0.161 s
%------------------------------------------------------------------------------
