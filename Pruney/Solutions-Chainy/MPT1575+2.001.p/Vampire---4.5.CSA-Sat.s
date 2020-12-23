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
% DateTime   : Thu Dec  3 13:16:20 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    0
%              Number of atoms          :   42 (  42 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u47,negated_conjecture,
    ( r1_yellow_0(sK0,k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0)))) )).

cnf(u43,negated_conjecture,
    ( r1_yellow_0(sK0,k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0))) )).

cnf(u21,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u30,axiom,
    ( ~ r1_orders_2(X0,X2,sK2(X0,X2))
    | v3_lattice3(X0)
    | ~ r2_lattice3(X0,sK1(X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u28,axiom,
    ( ~ r2_lattice3(X0,sK1(X0),X2)
    | m1_subset_1(sK2(X0,X2),u1_struct_0(X0))
    | v3_lattice3(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u29,axiom,
    ( ~ r2_lattice3(X0,sK1(X0),X2)
    | r2_lattice3(X0,sK1(X0),sK2(X0,X2))
    | v3_lattice3(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u27,axiom,
    ( ~ r2_lattice3(X0,X4,X6)
    | r1_orders_2(X0,sK3(X0,X4),X6)
    | ~ m1_subset_1(X6,u1_struct_0(X0))
    | ~ v3_lattice3(X0)
    | ~ l1_orders_2(X0) )).

cnf(u25,axiom,
    ( ~ v3_lattice3(X0)
    | m1_subset_1(sK3(X0,X4),u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u26,axiom,
    ( ~ v3_lattice3(X0)
    | r2_lattice3(X0,X4,sK3(X0,X4))
    | ~ l1_orders_2(X0) )).

cnf(u24,negated_conjecture,
    ( ~ v3_lattice3(sK0) )).

cnf(u22,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u42,axiom,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X2,X3)),k1_zfmisc_1(X3)) )).

cnf(u41,axiom,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X0)) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u23,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_yellow_0(sK0,X1) )).

cnf(u37,axiom,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) )).

cnf(u36,axiom,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) )).

cnf(u35,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u32,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:31:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (17011)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (17011)Refutation not found, incomplete strategy% (17011)------------------------------
% 0.21/0.46  % (17011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (17011)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (17011)Memory used [KB]: 6012
% 0.21/0.46  % (17011)Time elapsed: 0.054 s
% 0.21/0.46  % (17011)------------------------------
% 0.21/0.46  % (17011)------------------------------
% 0.21/0.47  % (17020)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (17021)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.47  % (17008)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (17013)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (17012)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (17020)# SZS output start Saturation.
% 0.21/0.47  cnf(u47,negated_conjecture,
% 0.21/0.47      r1_yellow_0(sK0,k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0))))).
% 0.21/0.47  
% 0.21/0.47  cnf(u43,negated_conjecture,
% 0.21/0.47      r1_yellow_0(sK0,k1_setfam_1(k2_tarski(u1_struct_0(sK0),X0)))).
% 0.21/0.47  
% 0.21/0.47  cnf(u21,negated_conjecture,
% 0.21/0.47      ~v2_struct_0(sK0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u30,axiom,
% 0.21/0.47      ~r1_orders_2(X0,X2,sK2(X0,X2)) | v3_lattice3(X0) | ~r2_lattice3(X0,sK1(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u28,axiom,
% 0.21/0.47      ~r2_lattice3(X0,sK1(X0),X2) | m1_subset_1(sK2(X0,X2),u1_struct_0(X0)) | v3_lattice3(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u29,axiom,
% 0.21/0.47      ~r2_lattice3(X0,sK1(X0),X2) | r2_lattice3(X0,sK1(X0),sK2(X0,X2)) | v3_lattice3(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u27,axiom,
% 0.21/0.47      ~r2_lattice3(X0,X4,X6) | r1_orders_2(X0,sK3(X0,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~v3_lattice3(X0) | ~l1_orders_2(X0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u25,axiom,
% 0.21/0.47      ~v3_lattice3(X0) | m1_subset_1(sK3(X0,X4),u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u26,axiom,
% 0.21/0.47      ~v3_lattice3(X0) | r2_lattice3(X0,X4,sK3(X0,X4)) | ~l1_orders_2(X0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u24,negated_conjecture,
% 0.21/0.47      ~v3_lattice3(sK0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u22,negated_conjecture,
% 0.21/0.47      l1_orders_2(sK0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u42,axiom,
% 0.21/0.47      m1_subset_1(k1_setfam_1(k2_tarski(X2,X3)),k1_zfmisc_1(X3))).
% 0.21/0.47  
% 0.21/0.47  cnf(u41,axiom,
% 0.21/0.47      m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X0))).
% 0.21/0.47  
% 0.21/0.47  cnf(u34,axiom,
% 0.21/0.47      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.47  
% 0.21/0.47  cnf(u23,negated_conjecture,
% 0.21/0.47      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_yellow_0(sK0,X1)).
% 0.21/0.47  
% 0.21/0.47  cnf(u37,axiom,
% 0.21/0.47      r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u36,axiom,
% 0.21/0.47      r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u35,axiom,
% 0.21/0.47      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.21/0.47  
% 0.21/0.47  cnf(u32,axiom,
% 0.21/0.47      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 0.21/0.47  
% 0.21/0.47  % (17020)# SZS output end Saturation.
% 0.21/0.47  % (17020)------------------------------
% 0.21/0.47  % (17020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (17020)Termination reason: Satisfiable
% 0.21/0.47  
% 0.21/0.47  % (17020)Memory used [KB]: 1663
% 0.21/0.47  % (17020)Time elapsed: 0.055 s
% 0.21/0.47  % (17020)------------------------------
% 0.21/0.47  % (17020)------------------------------
% 0.21/0.47  % (17006)Success in time 0.112 s
%------------------------------------------------------------------------------
