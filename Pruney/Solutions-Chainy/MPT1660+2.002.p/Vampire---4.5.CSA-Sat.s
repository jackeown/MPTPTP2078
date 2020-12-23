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
% DateTime   : Thu Dec  3 13:17:14 EST 2020

% Result     : CounterSatisfiable 1.67s
% Output     : Saturation 1.67s
% Verified   : 
% Statistics : Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    0
%              Number of atoms          :   87 (  87 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u16,negated_conjecture,
    ( ~ r2_hidden(k13_lattice3(sK0,sK2,sK3),sK1)
    | ~ v1_waybel_0(sK1,sK0) )).

cnf(u14,negated_conjecture,
    ( ~ v1_waybel_0(sK1,sK0)
    | r2_hidden(sK2,sK1) )).

cnf(u15,negated_conjecture,
    ( ~ v1_waybel_0(sK1,sK0)
    | r2_hidden(sK3,sK1) )).

cnf(u13,negated_conjecture,
    ( ~ v1_waybel_0(sK1,sK0)
    | m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u17,negated_conjecture,
    ( ~ v1_waybel_0(sK1,sK0)
    | m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u25,axiom,
    ( ~ r1_orders_2(X0,X3,sK4(X0,X1,X2,X3))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ v5_orders_2(X0)
    | k13_lattice3(X0,X1,X2) = X3 )).

cnf(u33,axiom,
    ( ~ r1_orders_2(X0,X1,X4)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X4)
    | r1_orders_2(X0,k13_lattice3(X0,X1,X2),X4) )).

cnf(u22,axiom,
    ( ~ r1_orders_2(X0,X1,X3)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X3)
    | m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))
    | k13_lattice3(X0,X1,X2) = X3 )).

cnf(u23,axiom,
    ( ~ r1_orders_2(X0,X1,X3)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,sK4(X0,X1,X2,X3))
    | k13_lattice3(X0,X1,X2) = X3 )).

cnf(u24,axiom,
    ( ~ r1_orders_2(X0,X1,X3)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X2,sK4(X0,X1,X2,X3))
    | k13_lattice3(X0,X1,X2) = X3 )).

cnf(u18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2)) )).

cnf(u35,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2)) )).

cnf(u12,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | ~ r2_hidden(X2,sK1)
    | ~ r2_hidden(X3,sK1)
    | r2_hidden(k13_lattice3(sK0,X2,X3),sK1)
    | v1_waybel_0(sK1,sK0) )).

cnf(u21,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u20,negated_conjecture,
    ( v1_lattice3(sK0) )).

cnf(u19,negated_conjecture,
    ( v5_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:09:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (19483)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (19482)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (19482)Refutation not found, incomplete strategy% (19482)------------------------------
% 0.22/0.49  % (19482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (19482)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (19482)Memory used [KB]: 1663
% 0.22/0.49  % (19482)Time elapsed: 0.064 s
% 0.22/0.49  % (19482)------------------------------
% 0.22/0.49  % (19482)------------------------------
% 0.22/0.50  % (19483)Refutation not found, incomplete strategy% (19483)------------------------------
% 0.22/0.50  % (19483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (19483)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (19483)Memory used [KB]: 10618
% 0.22/0.50  % (19483)Time elapsed: 0.066 s
% 0.22/0.50  % (19483)------------------------------
% 0.22/0.50  % (19483)------------------------------
% 0.22/0.50  % (19484)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (19474)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (19475)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (19476)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (19470)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (19471)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.54  % (19472)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (19469)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.49/0.55  % (19473)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.49/0.56  % (19470)Refutation not found, incomplete strategy% (19470)------------------------------
% 1.49/0.56  % (19470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (19470)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (19470)Memory used [KB]: 10618
% 1.49/0.56  % (19470)Time elapsed: 0.126 s
% 1.49/0.56  % (19470)------------------------------
% 1.49/0.56  % (19470)------------------------------
% 1.49/0.56  % (19488)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.49/0.56  % (19485)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.49/0.56  % (19469)Refutation not found, incomplete strategy% (19469)------------------------------
% 1.49/0.56  % (19469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (19469)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (19469)Memory used [KB]: 6140
% 1.49/0.56  % (19469)Time elapsed: 0.128 s
% 1.49/0.56  % (19469)------------------------------
% 1.49/0.56  % (19469)------------------------------
% 1.49/0.56  % (19478)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.49/0.56  % (19489)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.49/0.57  % (19477)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.67/0.57  % (19489)Refutation not found, incomplete strategy% (19489)------------------------------
% 1.67/0.57  % (19489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.57  % (19489)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.57  
% 1.67/0.57  % (19489)Memory used [KB]: 10618
% 1.67/0.57  % (19489)Time elapsed: 0.126 s
% 1.67/0.57  % (19489)------------------------------
% 1.67/0.57  % (19489)------------------------------
% 1.67/0.57  % (19486)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.67/0.57  % (19487)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.67/0.57  % SZS status CounterSatisfiable for theBenchmark
% 1.67/0.57  % (19486)# SZS output start Saturation.
% 1.67/0.57  cnf(u16,negated_conjecture,
% 1.67/0.57      ~r2_hidden(k13_lattice3(sK0,sK2,sK3),sK1) | ~v1_waybel_0(sK1,sK0)).
% 1.67/0.57  
% 1.67/0.57  cnf(u14,negated_conjecture,
% 1.67/0.57      ~v1_waybel_0(sK1,sK0) | r2_hidden(sK2,sK1)).
% 1.67/0.57  
% 1.67/0.57  cnf(u15,negated_conjecture,
% 1.67/0.57      ~v1_waybel_0(sK1,sK0) | r2_hidden(sK3,sK1)).
% 1.67/0.57  
% 1.67/0.57  cnf(u13,negated_conjecture,
% 1.67/0.57      ~v1_waybel_0(sK1,sK0) | m1_subset_1(sK3,u1_struct_0(sK0))).
% 1.67/0.57  
% 1.67/0.57  cnf(u17,negated_conjecture,
% 1.67/0.57      ~v1_waybel_0(sK1,sK0) | m1_subset_1(sK2,u1_struct_0(sK0))).
% 1.67/0.57  
% 1.67/0.57  cnf(u25,axiom,
% 1.67/0.57      ~r1_orders_2(X0,X3,sK4(X0,X1,X2,X3)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~v5_orders_2(X0) | k13_lattice3(X0,X1,X2) = X3).
% 1.67/0.57  
% 1.67/0.57  cnf(u33,axiom,
% 1.67/0.57      ~r1_orders_2(X0,X1,X4) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X4) | r1_orders_2(X0,k13_lattice3(X0,X1,X2),X4)).
% 1.67/0.57  
% 1.67/0.57  cnf(u22,axiom,
% 1.67/0.57      ~r1_orders_2(X0,X1,X3) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) | k13_lattice3(X0,X1,X2) = X3).
% 1.67/0.57  
% 1.67/0.57  cnf(u23,axiom,
% 1.67/0.57      ~r1_orders_2(X0,X1,X3) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,sK4(X0,X1,X2,X3)) | k13_lattice3(X0,X1,X2) = X3).
% 1.67/0.57  
% 1.67/0.57  cnf(u24,axiom,
% 1.67/0.57      ~r1_orders_2(X0,X1,X3) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X2,sK4(X0,X1,X2,X3)) | k13_lattice3(X0,X1,X2) = X3).
% 1.67/0.57  
% 1.67/0.57  cnf(u18,negated_conjecture,
% 1.67/0.57      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.67/0.57  
% 1.67/0.57  cnf(u29,axiom,
% 1.67/0.57      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))).
% 1.67/0.57  
% 1.67/0.57  cnf(u34,axiom,
% 1.67/0.57      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))).
% 1.67/0.57  
% 1.67/0.57  cnf(u35,axiom,
% 1.67/0.57      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))).
% 1.67/0.57  
% 1.67/0.57  cnf(u12,negated_conjecture,
% 1.67/0.57      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | ~r2_hidden(X3,sK1) | r2_hidden(k13_lattice3(sK0,X2,X3),sK1) | v1_waybel_0(sK1,sK0)).
% 1.67/0.57  
% 1.67/0.57  cnf(u21,negated_conjecture,
% 1.67/0.57      l1_orders_2(sK0)).
% 1.67/0.57  
% 1.67/0.57  cnf(u20,negated_conjecture,
% 1.67/0.57      v1_lattice3(sK0)).
% 1.67/0.57  
% 1.67/0.57  cnf(u19,negated_conjecture,
% 1.67/0.57      v5_orders_2(sK0)).
% 1.67/0.57  
% 1.67/0.57  % (19486)# SZS output end Saturation.
% 1.67/0.57  % (19486)------------------------------
% 1.67/0.57  % (19486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.57  % (19486)Termination reason: Satisfiable
% 1.67/0.57  
% 1.67/0.57  % (19486)Memory used [KB]: 1663
% 1.67/0.57  % (19486)Time elapsed: 0.144 s
% 1.67/0.57  % (19486)------------------------------
% 1.67/0.57  % (19486)------------------------------
% 1.67/0.57  % (19468)Success in time 0.205 s
%------------------------------------------------------------------------------
