%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:14 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    0
%              Number of atoms          :  146 ( 146 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal clause size      :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( ~ r2_hidden(k12_lattice3(sK0,sK2,sK3),sK1)
    | ~ v2_waybel_0(sK1,sK0) )).

cnf(u21,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | r2_hidden(sK2,sK1) )).

cnf(u22,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | r2_hidden(sK3,sK1) )).

cnf(u20,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u24,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u37,axiom,
    ( ~ r1_orders_2(X0,sK6(X0,X1,X2,X3),X3)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ v5_orders_2(X0)
    | r2_yellow_0(X0,k2_tarski(X1,X2)) )).

cnf(u41,axiom,
    ( ~ r1_orders_2(X0,sK6(X0,X1,X2,X3),X3)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ v5_orders_2(X0)
    | k11_lattice3(X0,X1,X2) = X3 )).

cnf(u34,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))
    | r2_yellow_0(X0,k2_tarski(X1,X2)) )).

cnf(u35,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK6(X0,X1,X2,X3),X1)
    | r2_yellow_0(X0,k2_tarski(X1,X2)) )).

cnf(u36,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK6(X0,X1,X2,X3),X2)
    | r2_yellow_0(X0,k2_tarski(X1,X2)) )).

cnf(u38,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))
    | k11_lattice3(X0,X1,X2) = X3 )).

cnf(u39,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK6(X0,X1,X2,X3),X1)
    | k11_lattice3(X0,X1,X2) = X3 )).

cnf(u40,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK6(X0,X1,X2,X3),X2)
    | k11_lattice3(X0,X1,X2) = X3 )).

cnf(u30,axiom,
    ( ~ r2_yellow_0(X0,k2_tarski(sK4(X0),sK5(X0)))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | v2_lattice3(X0) )).

cnf(u25,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u46,axiom,
    ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) )).

cnf(u47,axiom,
    ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1) )).

cnf(u48,axiom,
    ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X5,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X5,X1)
    | ~ r1_orders_2(X0,X5,X2)
    | r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2)) )).

cnf(u19,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | ~ r2_hidden(X2,sK1)
    | ~ r2_hidden(X3,sK1)
    | r2_hidden(k12_lattice3(sK0,X2,X3),sK1)
    | v2_waybel_0(sK1,sK0) )).

cnf(u31,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_yellow_0(X0,k2_tarski(X1,X2))
    | ~ v2_lattice3(X0) )).

cnf(u44,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) )).

cnf(u28,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u29,axiom,
    ( ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | m1_subset_1(sK5(X0),u1_struct_0(X0))
    | v2_lattice3(X0) )).

cnf(u32,axiom,
    ( ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | m1_subset_1(sK4(X0),u1_struct_0(X0))
    | v2_lattice3(X0) )).

cnf(u27,negated_conjecture,
    ( v2_lattice3(sK0) )).

cnf(u26,negated_conjecture,
    ( v5_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:22:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (25731)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (25727)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (25739)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (25725)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (25739)Refutation not found, incomplete strategy% (25739)------------------------------
% 0.21/0.49  % (25739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (25745)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (25726)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (25745)Refutation not found, incomplete strategy% (25745)------------------------------
% 0.21/0.49  % (25745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (25745)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (25745)Memory used [KB]: 10618
% 0.21/0.49  % (25745)Time elapsed: 0.074 s
% 0.21/0.49  % (25745)------------------------------
% 0.21/0.49  % (25745)------------------------------
% 0.21/0.49  % (25726)Refutation not found, incomplete strategy% (25726)------------------------------
% 0.21/0.49  % (25726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (25726)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (25726)Memory used [KB]: 10618
% 0.21/0.49  % (25726)Time elapsed: 0.071 s
% 0.21/0.49  % (25726)------------------------------
% 0.21/0.49  % (25726)------------------------------
% 0.21/0.49  % (25725)Refutation not found, incomplete strategy% (25725)------------------------------
% 0.21/0.49  % (25725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (25725)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (25725)Memory used [KB]: 6140
% 0.21/0.49  % (25725)Time elapsed: 0.066 s
% 0.21/0.49  % (25725)------------------------------
% 0.21/0.49  % (25725)------------------------------
% 0.21/0.50  % (25738)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (25734)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (25738)Refutation not found, incomplete strategy% (25738)------------------------------
% 0.21/0.50  % (25738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25738)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (25738)Memory used [KB]: 1663
% 0.21/0.50  % (25738)Time elapsed: 0.049 s
% 0.21/0.50  % (25738)------------------------------
% 0.21/0.50  % (25738)------------------------------
% 0.21/0.50  % (25742)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (25742)# SZS output start Saturation.
% 0.21/0.50  cnf(u23,negated_conjecture,
% 0.21/0.50      ~r2_hidden(k12_lattice3(sK0,sK2,sK3),sK1) | ~v2_waybel_0(sK1,sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u21,negated_conjecture,
% 0.21/0.50      ~v2_waybel_0(sK1,sK0) | r2_hidden(sK2,sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u22,negated_conjecture,
% 0.21/0.50      ~v2_waybel_0(sK1,sK0) | r2_hidden(sK3,sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u20,negated_conjecture,
% 0.21/0.50      ~v2_waybel_0(sK1,sK0) | m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u24,negated_conjecture,
% 0.21/0.50      ~v2_waybel_0(sK1,sK0) | m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u37,axiom,
% 0.21/0.50      ~r1_orders_2(X0,sK6(X0,X1,X2,X3),X3) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | ~v5_orders_2(X0) | r2_yellow_0(X0,k2_tarski(X1,X2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u41,axiom,
% 0.21/0.50      ~r1_orders_2(X0,sK6(X0,X1,X2,X3),X3) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | ~v5_orders_2(X0) | k11_lattice3(X0,X1,X2) = X3).
% 0.21/0.50  
% 0.21/0.50  cnf(u34,axiom,
% 0.21/0.50      ~r1_orders_2(X0,X3,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) | r2_yellow_0(X0,k2_tarski(X1,X2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u35,axiom,
% 0.21/0.50      ~r1_orders_2(X0,X3,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK6(X0,X1,X2,X3),X1) | r2_yellow_0(X0,k2_tarski(X1,X2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u36,axiom,
% 0.21/0.50      ~r1_orders_2(X0,X3,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK6(X0,X1,X2,X3),X2) | r2_yellow_0(X0,k2_tarski(X1,X2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u38,axiom,
% 0.21/0.50      ~r1_orders_2(X0,X3,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = X3).
% 0.21/0.50  
% 0.21/0.50  cnf(u39,axiom,
% 0.21/0.50      ~r1_orders_2(X0,X3,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK6(X0,X1,X2,X3),X1) | k11_lattice3(X0,X1,X2) = X3).
% 0.21/0.50  
% 0.21/0.50  cnf(u40,axiom,
% 0.21/0.50      ~r1_orders_2(X0,X3,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK6(X0,X1,X2,X3),X2) | k11_lattice3(X0,X1,X2) = X3).
% 0.21/0.50  
% 0.21/0.50  cnf(u30,axiom,
% 0.21/0.50      ~r2_yellow_0(X0,k2_tarski(sK4(X0),sK5(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | v2_lattice3(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u25,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u46,axiom,
% 0.21/0.50      ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r2_yellow_0(X0,k2_tarski(X1,X2)) | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u47,axiom,
% 0.21/0.50      ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r2_yellow_0(X0,k2_tarski(X1,X2)) | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u48,axiom,
% 0.21/0.50      ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r2_yellow_0(X0,k2_tarski(X1,X2)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r1_orders_2(X0,X5,X1) | ~r1_orders_2(X0,X5,X2) | r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2))).
% 0.21/0.50  
% 0.21/0.50  cnf(u19,negated_conjecture,
% 0.21/0.50      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | ~r2_hidden(X3,sK1) | r2_hidden(k12_lattice3(sK0,X2,X3),sK1) | v2_waybel_0(sK1,sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u31,axiom,
% 0.21/0.50      ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_yellow_0(X0,k2_tarski(X1,X2)) | ~v2_lattice3(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u44,axiom,
% 0.21/0.50      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u45,axiom,
% 0.21/0.50      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u28,negated_conjecture,
% 0.21/0.50      l1_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u29,axiom,
% 0.21/0.50      ~l1_orders_2(X0) | ~v5_orders_2(X0) | m1_subset_1(sK5(X0),u1_struct_0(X0)) | v2_lattice3(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u32,axiom,
% 0.21/0.50      ~l1_orders_2(X0) | ~v5_orders_2(X0) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | v2_lattice3(X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u27,negated_conjecture,
% 0.21/0.50      v2_lattice3(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u26,negated_conjecture,
% 0.21/0.50      v5_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  % (25742)# SZS output end Saturation.
% 0.21/0.50  % (25742)------------------------------
% 0.21/0.50  % (25742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25742)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (25742)Memory used [KB]: 1663
% 0.21/0.50  % (25742)Time elapsed: 0.082 s
% 0.21/0.50  % (25742)------------------------------
% 0.21/0.50  % (25742)------------------------------
% 0.21/0.50  % (25739)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (25739)Memory used [KB]: 10618
% 0.21/0.50  % (25739)Time elapsed: 0.072 s
% 0.21/0.50  % (25739)------------------------------
% 0.21/0.50  % (25739)------------------------------
% 0.21/0.50  % (25724)Success in time 0.138 s
%------------------------------------------------------------------------------
