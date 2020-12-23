%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:15 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    0
%              Number of atoms          :   74 (  74 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( v15_waybel_0(sK1,sK0)
    | sK1 = k6_waybel_0(sK0,sK2) )).

cnf(u28,axiom,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r1_orders_2(X0,X2,X3)
    | ~ l1_orders_2(X0) )).

cnf(u58,negated_conjecture,
    ( r1_orders_2(sK0,sK3(sK0,X1,X0),sK3(sK0,X1,X0))
    | r1_lattice3(sK0,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u52,negated_conjecture,
    ( r1_orders_2(sK0,X0,X0)
    | ~ r2_hidden(X0,sK1) )).

cnf(u51,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK2)
    | v15_waybel_0(sK1,sK0) )).

cnf(u31,axiom,
    ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u27,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u32,axiom,
    ( ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X1) )).

cnf(u30,axiom,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | r1_lattice3(X0,X1,X2) )).

cnf(u26,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u25,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u29,axiom,
    ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | v15_waybel_0(sK1,sK0) )).

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u46,negated_conjecture,
    ( m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_hidden(X0,sK1) )).

cnf(u50,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X0) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2) )).

cnf(u54,negated_conjecture,
    ( r2_hidden(sK3(sK0,X1,X0),X2)
    | r1_lattice3(sK0,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X1,X2) )).

cnf(u53,negated_conjecture,
    ( r2_hidden(sK3(sK0,X1,X0),X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_lattice3(sK0,X1,X0) )).

cnf(u37,axiom,
    ( r2_hidden(sK4(X0,X1),X0)
    | r1_tarski(X0,X1) )).

cnf(u36,axiom,
    ( ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1)
    | ~ r1_tarski(X0,X1) )).

cnf(u38,axiom,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | r1_tarski(X0,X1) )).

cnf(u40,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u35,axiom,
    ( ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 )).

cnf(u45,axiom,
    ( ~ r1_tarski(X0,X2)
    | r2_hidden(sK4(X0,X1),X2)
    | r1_tarski(X0,X1) )).

cnf(u55,negated_conjecture,
    ( ~ r1_tarski(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_tarski(X0,X2)
    | r2_hidden(sK3(sK0,X0,X1),X3)
    | r1_lattice3(sK0,X0,X1) )).

cnf(u21,negated_conjecture,
    ( sK1 != k6_waybel_0(sK0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ v15_waybel_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (31935)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (31944)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.50  % (31937)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (31929)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (31947)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (31923)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (31925)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (31921)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (31925)# SZS output start Saturation.
% 0.21/0.51  cnf(u23,negated_conjecture,
% 0.21/0.51      v15_waybel_0(sK1,sK0) | sK1 = k6_waybel_0(sK0,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u28,axiom,
% 0.21/0.51      ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X2,X3) | ~l1_orders_2(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u58,negated_conjecture,
% 0.21/0.51      r1_orders_2(sK0,sK3(sK0,X1,X0),sK3(sK0,X1,X0)) | r1_lattice3(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u52,negated_conjecture,
% 0.21/0.51      r1_orders_2(sK0,X0,X0) | ~r2_hidden(X0,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u51,negated_conjecture,
% 0.21/0.51      r1_orders_2(sK0,sK2,sK2) | v15_waybel_0(sK1,sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u31,axiom,
% 0.21/0.51      ~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u27,negated_conjecture,
% 0.21/0.51      l1_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u32,axiom,
% 0.21/0.51      ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u30,axiom,
% 0.21/0.51      ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK3(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u26,negated_conjecture,
% 0.21/0.51      v3_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u25,negated_conjecture,
% 0.21/0.51      ~v2_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u29,axiom,
% 0.21/0.51      m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u22,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK2,u1_struct_0(sK0)) | v15_waybel_0(sK1,sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u24,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u46,negated_conjecture,
% 0.21/0.51      m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u50,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u39,axiom,
% 0.21/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u54,negated_conjecture,
% 0.21/0.51      r2_hidden(sK3(sK0,X1,X0),X2) | r1_lattice3(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_tarski(X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u53,negated_conjecture,
% 0.21/0.51      r2_hidden(sK3(sK0,X1,X0),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u37,axiom,
% 0.21/0.51      r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u36,axiom,
% 0.21/0.51      ~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u38,axiom,
% 0.21/0.51      ~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u40,axiom,
% 0.21/0.51      r1_tarski(X1,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u35,axiom,
% 0.21/0.51      ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1).
% 0.21/0.51  
% 0.21/0.51  cnf(u45,axiom,
% 0.21/0.51      ~r1_tarski(X0,X2) | r2_hidden(sK4(X0,X1),X2) | r1_tarski(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u55,negated_conjecture,
% 0.21/0.51      ~r1_tarski(X2,X3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_tarski(X0,X2) | r2_hidden(sK3(sK0,X0,X1),X3) | r1_lattice3(sK0,X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u21,negated_conjecture,
% 0.21/0.51      sK1 != k6_waybel_0(sK0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v15_waybel_0(sK1,sK0)).
% 0.21/0.51  
% 0.21/0.51  % (31925)# SZS output end Saturation.
% 0.21/0.51  % (31925)------------------------------
% 0.21/0.51  % (31925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31925)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (31925)Memory used [KB]: 6268
% 0.21/0.51  % (31925)Time elapsed: 0.110 s
% 0.21/0.51  % (31925)------------------------------
% 0.21/0.51  % (31925)------------------------------
% 0.21/0.51  % (31929)Refutation not found, incomplete strategy% (31929)------------------------------
% 0.21/0.51  % (31929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31929)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31929)Memory used [KB]: 10618
% 0.21/0.51  % (31929)Time elapsed: 0.074 s
% 0.21/0.51  % (31929)------------------------------
% 0.21/0.51  % (31929)------------------------------
% 0.21/0.51  % (31948)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (31934)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (31941)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (31921)Refutation not found, incomplete strategy% (31921)------------------------------
% 0.21/0.51  % (31921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31936)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (31945)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (31936)Refutation not found, incomplete strategy% (31936)------------------------------
% 0.21/0.52  % (31936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31921)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31921)Memory used [KB]: 10618
% 0.21/0.52  % (31921)Time elapsed: 0.082 s
% 0.21/0.52  % (31921)------------------------------
% 0.21/0.52  % (31921)------------------------------
% 0.21/0.52  % (31920)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (31924)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (31943)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (31930)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (31939)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (31933)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (31922)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (31928)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (31942)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (31940)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (31919)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (31940)Refutation not found, incomplete strategy% (31940)------------------------------
% 0.21/0.52  % (31940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31940)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31940)Memory used [KB]: 1663
% 0.21/0.52  % (31940)Time elapsed: 0.126 s
% 0.21/0.52  % (31940)------------------------------
% 0.21/0.52  % (31940)------------------------------
% 0.21/0.52  % (31928)Refutation not found, incomplete strategy% (31928)------------------------------
% 0.21/0.52  % (31928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31928)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31931)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (31928)Memory used [KB]: 10618
% 0.21/0.52  % (31928)Time elapsed: 0.122 s
% 0.21/0.52  % (31928)------------------------------
% 0.21/0.52  % (31928)------------------------------
% 0.21/0.53  % (31919)Refutation not found, incomplete strategy% (31919)------------------------------
% 0.21/0.53  % (31919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31918)Success in time 0.162 s
%------------------------------------------------------------------------------
