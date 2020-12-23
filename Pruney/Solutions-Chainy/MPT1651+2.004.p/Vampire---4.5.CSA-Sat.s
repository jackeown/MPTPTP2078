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
% DateTime   : Thu Dec  3 13:17:06 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    0
%              Number of atoms          :  101 ( 101 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u47,negated_conjecture,
    ( r2_hidden(sK3(sK0,X1,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),X1)
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | r2_lattice3(sK0,X1,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)) )).

cnf(u38,negated_conjecture,
    ( r2_hidden(sK3(sK0,X0,sK2),X0)
    | r2_lattice3(sK0,X0,sK2) )).

cnf(u31,axiom,
    ( ~ r2_hidden(X4,X1)
    | r1_orders_2(X0,X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u46,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) )).

cnf(u40,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK2)
    | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0)) )).

cnf(u29,negated_conjecture,
    ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | r2_lattice3(sK0,sK1,sK2) )).

cnf(u49,negated_conjecture,
    ( ~ r2_lattice3(sK0,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3(sK0,X0,sK2),X1)
    | r2_lattice3(sK0,X0,sK2) )).

cnf(u61,negated_conjecture,
    ( ~ r2_lattice3(sK0,X0,X1)
    | r1_orders_2(sK0,sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),X1)
    | r2_lattice3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) )).

cnf(u42,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK1,sK2)
    | m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0)) )).

cnf(u30,negated_conjecture,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ~ r2_lattice3(sK0,sK1,sK2) )).

cnf(u66,negated_conjecture,
    ( r1_orders_2(sK0,sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),sK2)
    | r2_lattice3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0)) )).

cnf(u54,negated_conjecture,
    ( r1_orders_2(sK0,sK3(sK0,X0,sK2),sK3(sK0,k3_waybel_0(sK0,sK1),sK2))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
    | r2_lattice3(sK0,X0,sK2) )).

cnf(u69,negated_conjecture,
    ( ~ r1_orders_2(sK0,X1,sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0))
    | r2_lattice3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,X1,sK2) )).

cnf(u57,negated_conjecture,
    ( ~ r1_orders_2(sK0,X1,sK3(sK0,X0,sK2))
    | m1_subset_1(sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
    | r2_lattice3(sK0,X0,sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,X1,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)) )).

cnf(u44,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | r1_orders_2(sK0,X2,X1) )).

cnf(u34,axiom,
    ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u45,negated_conjecture,
    ( m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) )).

cnf(u28,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u37,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(sK3(sK0,X0,X1),X0)
    | r2_lattice3(sK0,X0,X1) )).

cnf(u39,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
    | r2_lattice3(sK0,X0,X1) )).

cnf(u26,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u33,axiom,
    ( ~ l1_orders_2(X0)
    | r2_hidden(sK3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2) )).

cnf(u32,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2) )).

cnf(u41,negated_conjecture,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(sK3(sK0,X1,sK2),u1_struct_0(X0))
    | ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,sK3(sK0,X1,sK2),X2)
    | r2_lattice3(sK0,X1,sK2) )).

cnf(u52,negated_conjecture,
    ( ~ l1_orders_2(X1)
    | r2_lattice3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2))
    | r1_orders_2(X1,sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),X2)
    | ~ m1_subset_1(sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),u1_struct_0(X1))
    | ~ r2_lattice3(X1,X0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) )).

cnf(u25,negated_conjecture,
    ( v4_orders_2(sK0) )).

cnf(u35,axiom,
    ( ~ v4_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,X1,X3) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (5689)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.45  % (5697)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.46  % (5692)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.20/0.46  % (5700)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.20/0.47  % (5697)Refutation not found, incomplete strategy% (5697)------------------------------
% 0.20/0.47  % (5697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5697)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (5697)Memory used [KB]: 5373
% 0.20/0.47  % (5697)Time elapsed: 0.070 s
% 0.20/0.47  % (5697)------------------------------
% 0.20/0.47  % (5697)------------------------------
% 0.20/0.47  % (5692)Refutation not found, incomplete strategy% (5692)------------------------------
% 0.20/0.47  % (5692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5692)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (5692)Memory used [KB]: 9850
% 0.20/0.47  % (5692)Time elapsed: 0.054 s
% 0.20/0.47  % (5692)------------------------------
% 0.20/0.47  % (5692)------------------------------
% 0.20/0.47  % (5694)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.20/0.47  % (5700)Refutation not found, incomplete strategy% (5700)------------------------------
% 0.20/0.47  % (5700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5700)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (5700)Memory used [KB]: 9850
% 0.20/0.47  % (5700)Time elapsed: 0.063 s
% 0.20/0.47  % (5700)------------------------------
% 0.20/0.47  % (5700)------------------------------
% 0.20/0.48  % (5696)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.48  % (5685)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.20/0.48  % (5688)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.49  % (5688)Refutation not found, incomplete strategy% (5688)------------------------------
% 0.20/0.49  % (5688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (5688)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (5688)Memory used [KB]: 895
% 0.20/0.49  % (5688)Time elapsed: 0.036 s
% 0.20/0.49  % (5688)------------------------------
% 0.20/0.49  % (5688)------------------------------
% 0.20/0.49  % (5695)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.20/0.49  % (5693)WARNING: option uwaf not known.
% 0.20/0.49  % (5686)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.20/0.49  % (5686)Refutation not found, incomplete strategy% (5686)------------------------------
% 0.20/0.49  % (5686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (5686)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (5686)Memory used [KB]: 9850
% 0.20/0.49  % (5686)Time elapsed: 0.085 s
% 0.20/0.49  % (5686)------------------------------
% 0.20/0.49  % (5686)------------------------------
% 0.20/0.49  % (5703)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.20/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.49  % (5703)# SZS output start Saturation.
% 0.20/0.49  cnf(u47,negated_conjecture,
% 0.20/0.49      r2_hidden(sK3(sK0,X1,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),X1) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | r2_lattice3(sK0,X1,sK3(sK0,k3_waybel_0(sK0,sK1),sK2))).
% 0.20/0.49  
% 0.20/0.49  cnf(u38,negated_conjecture,
% 0.20/0.49      r2_hidden(sK3(sK0,X0,sK2),X0) | r2_lattice3(sK0,X0,sK2)).
% 0.20/0.49  
% 0.20/0.49  cnf(u31,axiom,
% 0.20/0.49      ~r2_hidden(X4,X1) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u46,negated_conjecture,
% 0.20/0.49      r2_lattice3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))).
% 0.20/0.49  
% 0.20/0.49  cnf(u40,negated_conjecture,
% 0.20/0.49      r2_lattice3(sK0,X0,sK2) | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0))).
% 0.20/0.49  
% 0.20/0.49  cnf(u29,negated_conjecture,
% 0.20/0.49      r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2) | r2_lattice3(sK0,sK1,sK2)).
% 0.20/0.49  
% 0.20/0.49  cnf(u49,negated_conjecture,
% 0.20/0.49      ~r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK3(sK0,X0,sK2),X1) | r2_lattice3(sK0,X0,sK2)).
% 0.20/0.49  
% 0.20/0.49  cnf(u61,negated_conjecture,
% 0.20/0.49      ~r2_lattice3(sK0,X0,X1) | r1_orders_2(sK0,sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),X1) | r2_lattice3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))).
% 0.20/0.49  
% 0.20/0.49  cnf(u42,negated_conjecture,
% 0.20/0.49      ~r2_lattice3(sK0,sK1,sK2) | m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0))).
% 0.20/0.49  
% 0.20/0.49  cnf(u30,negated_conjecture,
% 0.20/0.49      ~r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2) | ~r2_lattice3(sK0,sK1,sK2)).
% 0.20/0.49  
% 0.20/0.49  cnf(u66,negated_conjecture,
% 0.20/0.49      r1_orders_2(sK0,sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),sK2) | r2_lattice3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0))).
% 0.20/0.49  
% 0.20/0.49  cnf(u54,negated_conjecture,
% 0.20/0.49      r1_orders_2(sK0,sK3(sK0,X0,sK2),sK3(sK0,k3_waybel_0(sK0,sK1),sK2)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0)) | r2_lattice3(sK0,X0,sK2)).
% 0.20/0.49  
% 0.20/0.49  cnf(u69,negated_conjecture,
% 0.20/0.49      ~r1_orders_2(sK0,X1,sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2))) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0)) | r2_lattice3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK2)).
% 0.20/0.49  
% 0.20/0.49  cnf(u57,negated_conjecture,
% 0.20/0.49      ~r1_orders_2(sK0,X1,sK3(sK0,X0,sK2)) | m1_subset_1(sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0)) | r2_lattice3(sK0,X0,sK2) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK3(sK0,k3_waybel_0(sK0,sK1),sK2))).
% 0.20/0.49  
% 0.20/0.49  cnf(u44,negated_conjecture,
% 0.20/0.49      ~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_orders_2(sK0,X2,X1)).
% 0.20/0.49  
% 0.20/0.49  cnf(u34,axiom,
% 0.20/0.49      ~r1_orders_2(X0,sK3(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u45,negated_conjecture,
% 0.20/0.49      m1_subset_1(sK3(sK0,k3_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))).
% 0.20/0.49  
% 0.20/0.49  cnf(u28,negated_conjecture,
% 0.20/0.49      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.49  
% 0.20/0.49  cnf(u37,negated_conjecture,
% 0.20/0.49      ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK3(sK0,X0,X1),X0) | r2_lattice3(sK0,X0,X1)).
% 0.20/0.49  
% 0.20/0.49  cnf(u39,negated_conjecture,
% 0.20/0.49      ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)).
% 0.20/0.49  
% 0.20/0.49  cnf(u26,negated_conjecture,
% 0.20/0.49      l1_orders_2(sK0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u33,axiom,
% 0.20/0.49      ~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)).
% 0.20/0.49  
% 0.20/0.49  cnf(u32,axiom,
% 0.20/0.49      ~l1_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)).
% 0.20/0.49  
% 0.20/0.49  cnf(u41,negated_conjecture,
% 0.20/0.49      ~l1_orders_2(X0) | ~m1_subset_1(sK3(sK0,X1,sK2),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,sK3(sK0,X1,sK2),X2) | r2_lattice3(sK0,X1,sK2)).
% 0.20/0.49  
% 0.20/0.49  cnf(u52,negated_conjecture,
% 0.20/0.49      ~l1_orders_2(X1) | r2_lattice3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)) | r1_orders_2(X1,sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),X2) | ~m1_subset_1(sK3(sK0,X0,sK3(sK0,k3_waybel_0(sK0,sK1),sK2)),u1_struct_0(X1)) | ~r2_lattice3(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))).
% 0.20/0.49  
% 0.20/0.49  cnf(u25,negated_conjecture,
% 0.20/0.49      v4_orders_2(sK0)).
% 0.20/0.49  
% 0.20/0.49  cnf(u35,axiom,
% 0.20/0.49      ~v4_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X3)).
% 0.20/0.49  
% 0.20/0.49  % (5703)# SZS output end Saturation.
% 0.20/0.49  % (5703)------------------------------
% 0.20/0.49  % (5703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (5703)Termination reason: Satisfiable
% 0.20/0.49  
% 0.20/0.49  % (5703)Memory used [KB]: 5373
% 0.20/0.49  % (5703)Time elapsed: 0.091 s
% 0.20/0.49  % (5703)------------------------------
% 0.20/0.49  % (5703)------------------------------
% 0.20/0.49  % (5682)Success in time 0.139 s
%------------------------------------------------------------------------------
