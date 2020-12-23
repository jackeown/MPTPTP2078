%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:19 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   84 (  84 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u27,negated_conjecture,
    ( ~ r2_hidden(X4,sK2)
    | v1_finset_1(sK3(X4))
    | ~ m1_subset_1(X4,u1_struct_0(sK0)) )).

cnf(u30,negated_conjecture,
    ( ~ r2_hidden(X4,sK2)
    | k2_yellow_0(sK0,sK3(X4)) = X4
    | ~ m1_subset_1(X4,u1_struct_0(sK0)) )).

cnf(u39,negated_conjecture,
    ( ~ r2_hidden(X2,sK2)
    | r1_lattice3(sK0,sK3(X2),sK4(sK0,sK3(X2),X1))
    | r2_yellow_0(sK0,X1)
    | v2_struct_0(sK0)
    | r1_lattice3(sK0,X1,sK4(sK0,sK3(X2),X1))
    | ~ m1_subset_1(X2,u1_struct_0(sK0)) )).

cnf(u26,negated_conjecture,
    ( ~ v1_finset_1(X6)
    | k1_xboole_0 = X6
    | ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
    | r2_yellow_0(sK0,X6) )).

% (12737)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
cnf(u31,negated_conjecture,
    ( ~ v1_finset_1(X3)
    | k1_xboole_0 = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
    | r2_hidden(k2_yellow_0(sK0,X3),sK2) )).

cnf(u22,negated_conjecture,
    ( v4_orders_2(sK0) )).

cnf(u21,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u29,negated_conjecture,
    ( r2_yellow_0(sK0,sK3(X4))
    | ~ r2_hidden(X4,sK2)
    | ~ m1_subset_1(X4,u1_struct_0(sK0)) )).

cnf(u32,negated_conjecture,
    ( r2_yellow_0(sK0,sK2)
    | r2_yellow_0(sK0,sK1) )).

cnf(u37,negated_conjecture,
    ( ~ r2_yellow_0(sK0,X0)
    | r1_lattice3(sK0,X1,sK4(sK0,X0,X1))
    | r1_lattice3(sK0,X0,sK4(sK0,X0,X1))
    | r2_yellow_0(sK0,X1)
    | v2_struct_0(sK0) )).

cnf(u41,negated_conjecture,
    ( ~ r2_yellow_0(sK0,X0)
    | ~ r1_lattice3(sK0,X1,sK4(sK0,X0,X1))
    | ~ r1_lattice3(sK0,X0,sK4(sK0,X0,X1))
    | r2_yellow_0(sK0,X1)
    | v2_struct_0(sK0) )).

cnf(u33,negated_conjecture,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ r2_yellow_0(sK0,sK2) )).

cnf(u38,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK4(sK0,sK2,X0))
    | r1_lattice3(sK0,sK2,sK4(sK0,sK2,X0))
    | r2_yellow_0(sK0,X0)
    | v2_struct_0(sK0)
    | r2_yellow_0(sK0,sK1) )).

cnf(u38_001,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK4(sK0,sK2,X0))
    | r1_lattice3(sK0,sK2,sK4(sK0,sK2,X0))
    | r2_yellow_0(sK0,X0)
    | v2_struct_0(sK0)
    | r2_yellow_0(sK0,sK1) )).

cnf(u43,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK3(X2),sK4(sK0,sK3(X2),X1))
    | ~ r1_lattice3(sK0,X1,sK4(sK0,sK3(X2),X1))
    | r2_yellow_0(sK0,X1)
    | v2_struct_0(sK0)
    | ~ r2_hidden(X2,sK2)
    | ~ m1_subset_1(X2,u1_struct_0(sK0)) )).

cnf(u42,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK2,sK4(sK0,sK2,X0))
    | ~ r1_lattice3(sK0,X0,sK4(sK0,sK2,X0))
    | r2_yellow_0(sK0,X0)
    | v2_struct_0(sK0)
    | r2_yellow_0(sK0,sK1) )).

cnf(u34,axiom,
    ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
    | ~ r2_yellow_0(X0,X1)
    | r2_yellow_0(X0,X2)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u28,negated_conjecture,
    ( m1_subset_1(sK3(X4),k1_zfmisc_1(sK1))
    | ~ r2_hidden(X4,sK2)
    | ~ m1_subset_1(X4,u1_struct_0(sK0)) )).

cnf(u25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u23,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u35,axiom,
    ( ~ l1_orders_2(X0)
    | ~ r2_yellow_0(X0,X1)
    | r1_lattice3(X0,X2,sK4(X0,X1,X2))
    | r1_lattice3(X0,X1,sK4(X0,X1,X2))
    | r2_yellow_0(X0,X2)
    | v2_struct_0(X0) )).

cnf(u36,axiom,
    ( ~ l1_orders_2(X0)
    | ~ r2_yellow_0(X0,X1)
    | ~ r1_lattice3(X0,X2,sK4(X0,X1,X2))
    | ~ r1_lattice3(X0,X1,sK4(X0,X1,X2))
    | r2_yellow_0(X0,X2)
    | v2_struct_0(X0) )).

cnf(u20,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:06:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (12730)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.48  % (12738)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.48  % (12738)Refutation not found, incomplete strategy% (12738)------------------------------
% 0.21/0.48  % (12738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12738)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (12738)Memory used [KB]: 10618
% 0.21/0.48  % (12738)Time elapsed: 0.074 s
% 0.21/0.48  % (12738)------------------------------
% 0.21/0.48  % (12738)------------------------------
% 0.21/0.49  % (12719)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % (12722)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (12722)Refutation not found, incomplete strategy% (12722)------------------------------
% 0.21/0.49  % (12722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12722)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (12722)Memory used [KB]: 6140
% 0.21/0.49  % (12722)Time elapsed: 0.084 s
% 0.21/0.49  % (12722)------------------------------
% 0.21/0.49  % (12722)------------------------------
% 0.21/0.49  % (12720)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (12726)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (12715)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (12736)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (12732)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.50  % (12734)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (12732)Refutation not found, incomplete strategy% (12732)------------------------------
% 0.21/0.50  % (12732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12732)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12732)Memory used [KB]: 1663
% 0.21/0.50  % (12732)Time elapsed: 0.095 s
% 0.21/0.50  % (12732)------------------------------
% 0.21/0.50  % (12732)------------------------------
% 0.21/0.50  % (12734)Refutation not found, incomplete strategy% (12734)------------------------------
% 0.21/0.50  % (12734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12734)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12734)Memory used [KB]: 6140
% 0.21/0.50  % (12734)Time elapsed: 0.096 s
% 0.21/0.50  % (12734)------------------------------
% 0.21/0.50  % (12734)------------------------------
% 0.21/0.50  % (12725)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (12717)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (12729)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (12717)Refutation not found, incomplete strategy% (12717)------------------------------
% 0.21/0.51  % (12717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12717)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12717)Memory used [KB]: 10618
% 0.21/0.51  % (12717)Time elapsed: 0.093 s
% 0.21/0.51  % (12717)------------------------------
% 0.21/0.51  % (12717)------------------------------
% 0.21/0.51  % (12716)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (12724)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (12735)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (12721)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (12724)# SZS output start Saturation.
% 0.21/0.51  cnf(u27,negated_conjecture,
% 0.21/0.51      ~r2_hidden(X4,sK2) | v1_finset_1(sK3(X4)) | ~m1_subset_1(X4,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u30,negated_conjecture,
% 0.21/0.51      ~r2_hidden(X4,sK2) | k2_yellow_0(sK0,sK3(X4)) = X4 | ~m1_subset_1(X4,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u39,negated_conjecture,
% 0.21/0.51      ~r2_hidden(X2,sK2) | r1_lattice3(sK0,sK3(X2),sK4(sK0,sK3(X2),X1)) | r2_yellow_0(sK0,X1) | v2_struct_0(sK0) | r1_lattice3(sK0,X1,sK4(sK0,sK3(X2),X1)) | ~m1_subset_1(X2,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u26,negated_conjecture,
% 0.21/0.51      ~v1_finset_1(X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(sK1)) | r2_yellow_0(sK0,X6)).
% 0.21/0.51  
% 0.21/0.51  % (12737)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  cnf(u31,negated_conjecture,
% 0.21/0.51      ~v1_finset_1(X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(sK1)) | r2_hidden(k2_yellow_0(sK0,X3),sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u22,negated_conjecture,
% 0.21/0.51      v4_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u21,negated_conjecture,
% 0.21/0.51      v3_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u29,negated_conjecture,
% 0.21/0.51      r2_yellow_0(sK0,sK3(X4)) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u32,negated_conjecture,
% 0.21/0.51      r2_yellow_0(sK0,sK2) | r2_yellow_0(sK0,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u37,negated_conjecture,
% 0.21/0.51      ~r2_yellow_0(sK0,X0) | r1_lattice3(sK0,X1,sK4(sK0,X0,X1)) | r1_lattice3(sK0,X0,sK4(sK0,X0,X1)) | r2_yellow_0(sK0,X1) | v2_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u41,negated_conjecture,
% 0.21/0.51      ~r2_yellow_0(sK0,X0) | ~r1_lattice3(sK0,X1,sK4(sK0,X0,X1)) | ~r1_lattice3(sK0,X0,sK4(sK0,X0,X1)) | r2_yellow_0(sK0,X1) | v2_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u33,negated_conjecture,
% 0.21/0.51      ~r2_yellow_0(sK0,sK1) | ~r2_yellow_0(sK0,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u38,negated_conjecture,
% 0.21/0.51      r1_lattice3(sK0,X0,sK4(sK0,sK2,X0)) | r1_lattice3(sK0,sK2,sK4(sK0,sK2,X0)) | r2_yellow_0(sK0,X0) | v2_struct_0(sK0) | r2_yellow_0(sK0,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u38,negated_conjecture,
% 0.21/0.51      r1_lattice3(sK0,X0,sK4(sK0,sK2,X0)) | r1_lattice3(sK0,sK2,sK4(sK0,sK2,X0)) | r2_yellow_0(sK0,X0) | v2_struct_0(sK0) | r2_yellow_0(sK0,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u43,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK0,sK3(X2),sK4(sK0,sK3(X2),X1)) | ~r1_lattice3(sK0,X1,sK4(sK0,sK3(X2),X1)) | r2_yellow_0(sK0,X1) | v2_struct_0(sK0) | ~r2_hidden(X2,sK2) | ~m1_subset_1(X2,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u42,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK0,sK2,sK4(sK0,sK2,X0)) | ~r1_lattice3(sK0,X0,sK4(sK0,sK2,X0)) | r2_yellow_0(sK0,X0) | v2_struct_0(sK0) | r2_yellow_0(sK0,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u34,axiom,
% 0.21/0.51      m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | r2_yellow_0(X0,X2) | ~l1_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u28,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK3(X4),k1_zfmisc_1(sK1)) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u25,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u24,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u23,negated_conjecture,
% 0.21/0.51      l1_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u35,axiom,
% 0.21/0.51      ~l1_orders_2(X0) | ~r2_yellow_0(X0,X1) | r1_lattice3(X0,X2,sK4(X0,X1,X2)) | r1_lattice3(X0,X1,sK4(X0,X1,X2)) | r2_yellow_0(X0,X2) | v2_struct_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u36,axiom,
% 0.21/0.51      ~l1_orders_2(X0) | ~r2_yellow_0(X0,X1) | ~r1_lattice3(X0,X2,sK4(X0,X1,X2)) | ~r1_lattice3(X0,X1,sK4(X0,X1,X2)) | r2_yellow_0(X0,X2) | v2_struct_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u20,negated_conjecture,
% 0.21/0.51      ~v2_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  % (12724)# SZS output end Saturation.
% 0.21/0.51  % (12724)------------------------------
% 0.21/0.51  % (12724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12724)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (12724)Memory used [KB]: 1663
% 0.21/0.51  % (12724)Time elapsed: 0.108 s
% 0.21/0.51  % (12724)------------------------------
% 0.21/0.51  % (12724)------------------------------
% 0.21/0.51  % (12721)Refutation not found, incomplete strategy% (12721)------------------------------
% 0.21/0.51  % (12721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12721)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12721)Memory used [KB]: 10618
% 0.21/0.51  % (12721)Time elapsed: 0.080 s
% 0.21/0.51  % (12721)------------------------------
% 0.21/0.51  % (12721)------------------------------
% 0.21/0.51  % (12714)Success in time 0.154 s
%------------------------------------------------------------------------------
