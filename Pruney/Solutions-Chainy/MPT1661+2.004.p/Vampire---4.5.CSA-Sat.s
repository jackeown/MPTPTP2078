%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:14 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
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
    ( ~ r2_hidden(k12_lattice3(sK0,sK2,sK3),sK1)
    | ~ v2_waybel_0(sK1,sK0) )).

cnf(u14,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | r2_hidden(sK2,sK1) )).

cnf(u15,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | r2_hidden(sK3,sK1) )).

cnf(u13,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u17,negated_conjecture,
    ( ~ v2_waybel_0(sK1,sK0)
    | m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u25,axiom,
    ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X3,X1)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ v5_orders_2(X0)
    | k12_lattice3(X0,X1,X2) = X3 )).

cnf(u33,axiom,
    ( ~ r1_orders_2(X0,X4,X1)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X4,X2)
    | r1_orders_2(X0,X4,k12_lattice3(X0,X1,X2)) )).

cnf(u22,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))
    | k12_lattice3(X0,X1,X2) = X3 )).

cnf(u23,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
    | k12_lattice3(X0,X1,X2) = X3 )).

cnf(u24,axiom,
    ( ~ r1_orders_2(X0,X3,X1)
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
    | k12_lattice3(X0,X1,X2) = X3 )).

cnf(u18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1) )).

cnf(u35,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2) )).

cnf(u12,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | ~ r2_hidden(X2,sK1)
    | ~ r2_hidden(X3,sK1)
    | r2_hidden(k12_lattice3(sK0,X2,X3),sK1)
    | v2_waybel_0(sK1,sK0) )).

cnf(u21,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u20,negated_conjecture,
    ( v2_lattice3(sK0) )).

cnf(u19,negated_conjecture,
    ( v5_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:38:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (20269)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (20257)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (20257)Refutation not found, incomplete strategy% (20257)------------------------------
% 0.21/0.48  % (20257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (20257)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (20257)Memory used [KB]: 10618
% 0.21/0.48  % (20257)Time elapsed: 0.059 s
% 0.21/0.48  % (20257)------------------------------
% 0.21/0.48  % (20257)------------------------------
% 0.21/0.48  % (20261)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (20267)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (20267)Refutation not found, incomplete strategy% (20267)------------------------------
% 0.21/0.48  % (20267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (20267)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (20267)Memory used [KB]: 10618
% 0.21/0.48  % (20267)Time elapsed: 0.062 s
% 0.21/0.48  % (20267)------------------------------
% 0.21/0.48  % (20267)------------------------------
% 0.21/0.48  % (20273)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (20273)# SZS output start Saturation.
% 0.21/0.48  cnf(u16,negated_conjecture,
% 0.21/0.48      ~r2_hidden(k12_lattice3(sK0,sK2,sK3),sK1) | ~v2_waybel_0(sK1,sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u14,negated_conjecture,
% 0.21/0.48      ~v2_waybel_0(sK1,sK0) | r2_hidden(sK2,sK1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u15,negated_conjecture,
% 0.21/0.48      ~v2_waybel_0(sK1,sK0) | r2_hidden(sK3,sK1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u13,negated_conjecture,
% 0.21/0.48      ~v2_waybel_0(sK1,sK0) | m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.21/0.48  
% 0.21/0.48  cnf(u17,negated_conjecture,
% 0.21/0.48      ~v2_waybel_0(sK1,sK0) | m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.48  
% 0.21/0.48  cnf(u25,axiom,
% 0.21/0.48      ~r1_orders_2(X0,sK4(X0,X1,X2,X3),X3) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X3,X2) | ~v5_orders_2(X0) | k12_lattice3(X0,X1,X2) = X3).
% 0.21/0.48  
% 0.21/0.48  cnf(u33,axiom,
% 0.21/0.48      ~r1_orders_2(X0,X4,X1) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X4,X2) | r1_orders_2(X0,X4,k12_lattice3(X0,X1,X2))).
% 0.21/0.48  
% 0.21/0.48  cnf(u22,axiom,
% 0.21/0.48      ~r1_orders_2(X0,X3,X1) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = X3).
% 0.21/0.48  
% 0.21/0.48  cnf(u23,axiom,
% 0.21/0.48      ~r1_orders_2(X0,X3,X1) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK4(X0,X1,X2,X3),X1) | k12_lattice3(X0,X1,X2) = X3).
% 0.21/0.48  
% 0.21/0.48  cnf(u24,axiom,
% 0.21/0.48      ~r1_orders_2(X0,X3,X1) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | r1_orders_2(X0,sK4(X0,X1,X2,X3),X2) | k12_lattice3(X0,X1,X2) = X3).
% 0.21/0.48  
% 0.21/0.48  cnf(u18,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.48  
% 0.21/0.48  cnf(u29,axiom,
% 0.21/0.48      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))).
% 0.21/0.48  
% 0.21/0.48  cnf(u34,axiom,
% 0.21/0.48      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)).
% 0.21/0.48  
% 0.21/0.48  cnf(u35,axiom,
% 0.21/0.48      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u12,negated_conjecture,
% 0.21/0.48      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | ~r2_hidden(X3,sK1) | r2_hidden(k12_lattice3(sK0,X2,X3),sK1) | v2_waybel_0(sK1,sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u21,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u20,negated_conjecture,
% 0.21/0.48      v2_lattice3(sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u19,negated_conjecture,
% 0.21/0.48      v5_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  % (20273)# SZS output end Saturation.
% 0.21/0.48  % (20273)------------------------------
% 0.21/0.48  % (20273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (20273)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (20273)Memory used [KB]: 1663
% 0.21/0.48  % (20273)Time elapsed: 0.068 s
% 0.21/0.48  % (20273)------------------------------
% 0.21/0.48  % (20273)------------------------------
% 0.21/0.48  % (20253)Success in time 0.125 s
%------------------------------------------------------------------------------
