%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:13 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   97 (  97 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal clause size      :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( ~ v1_waybel_0(sK1,sK0)
    | r2_hidden(sK2,sK1) )).

cnf(u24,negated_conjecture,
    ( ~ v1_waybel_0(sK1,sK0)
    | r2_hidden(sK3,sK1) )).

cnf(u22,negated_conjecture,
    ( ~ v1_waybel_0(sK1,sK0)
    | m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u26,negated_conjecture,
    ( ~ v1_waybel_0(sK1,sK0)
    | m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u48,axiom,
    ( ~ r1_orders_2(X0,X3,sK4(X0,X1,X2,X3))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X3)
    | ~ r1_orders_2(X0,X2,X3)
    | ~ v5_orders_2(X0)
    | k10_lattice3(X0,X1,X2) = X3 )).

cnf(u52,axiom,
    ( ~ r1_orders_2(X0,X1,X4)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X4)
    | r1_orders_2(X0,k10_lattice3(X0,X1,X2),X4) )).

cnf(u49,axiom,
    ( ~ r1_orders_2(X0,X1,X3)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X2,sK4(X0,X1,X2,X3))
    | k10_lattice3(X0,X1,X2) = X3 )).

cnf(u50,axiom,
    ( ~ r1_orders_2(X0,X1,X3)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X3)
    | r1_orders_2(X0,X1,sK4(X0,X1,X2,X3))
    | k10_lattice3(X0,X1,X2) = X3 )).

cnf(u51,axiom,
    ( ~ r1_orders_2(X0,X1,X3)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X3)
    | m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))
    | k10_lattice3(X0,X1,X2) = X3 )).

cnf(u28,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u31,axiom,
    ( ~ v2_struct_0(X0)
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0) )).

cnf(u29,negated_conjecture,
    ( v1_lattice3(sK0) )).

cnf(u30,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u21,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | ~ r2_hidden(X2,sK1)
    | ~ r2_hidden(X3,sK1)
    | r2_hidden(k13_lattice3(sK0,X2,X3),sK1)
    | v1_waybel_0(sK1,sK0) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) )).

cnf(u53,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) )).

cnf(u54,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) )).

cnf(u41,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u25,negated_conjecture,
    ( ~ r2_hidden(k13_lattice3(sK0,sK2,sK3),sK1)
    | ~ v1_waybel_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:08:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (25736)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (25744)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.48  % (25744)# SZS output start Saturation.
% 0.20/0.48  cnf(u23,negated_conjecture,
% 0.20/0.48      ~v1_waybel_0(sK1,sK0) | r2_hidden(sK2,sK1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u24,negated_conjecture,
% 0.20/0.48      ~v1_waybel_0(sK1,sK0) | r2_hidden(sK3,sK1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u22,negated_conjecture,
% 0.20/0.48      ~v1_waybel_0(sK1,sK0) | m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  cnf(u26,negated_conjecture,
% 0.20/0.48      ~v1_waybel_0(sK1,sK0) | m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  cnf(u48,axiom,
% 0.20/0.48      ~r1_orders_2(X0,X3,sK4(X0,X1,X2,X3)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~v5_orders_2(X0) | k10_lattice3(X0,X1,X2) = X3).
% 0.20/0.48  
% 0.20/0.48  cnf(u52,axiom,
% 0.20/0.48      ~r1_orders_2(X0,X1,X4) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X4) | r1_orders_2(X0,k10_lattice3(X0,X1,X2),X4)).
% 0.20/0.48  
% 0.20/0.48  cnf(u49,axiom,
% 0.20/0.48      ~r1_orders_2(X0,X1,X3) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X2,sK4(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3).
% 0.20/0.48  
% 0.20/0.48  cnf(u50,axiom,
% 0.20/0.48      ~r1_orders_2(X0,X1,X3) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,sK4(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3).
% 0.20/0.48  
% 0.20/0.48  cnf(u51,axiom,
% 0.20/0.48      ~r1_orders_2(X0,X1,X3) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) | k10_lattice3(X0,X1,X2) = X3).
% 0.20/0.48  
% 0.20/0.48  cnf(u28,negated_conjecture,
% 0.20/0.48      v5_orders_2(sK0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u31,axiom,
% 0.20/0.48      ~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u29,negated_conjecture,
% 0.20/0.48      v1_lattice3(sK0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u30,negated_conjecture,
% 0.20/0.48      l1_orders_2(sK0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u27,negated_conjecture,
% 0.20/0.48      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.48  
% 0.20/0.48  cnf(u21,negated_conjecture,
% 0.20/0.48      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | ~r2_hidden(X3,sK1) | r2_hidden(k13_lattice3(sK0,X2,X3),sK1) | v1_waybel_0(sK1,sK0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u40,axiom,
% 0.20/0.48      ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))).
% 0.20/0.48  
% 0.20/0.48  cnf(u53,axiom,
% 0.20/0.48      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))).
% 0.20/0.48  
% 0.20/0.48  cnf(u54,axiom,
% 0.20/0.48      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))).
% 0.20/0.48  
% 0.20/0.48  cnf(u39,axiom,
% 0.20/0.48      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u41,axiom,
% 0.20/0.48      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u25,negated_conjecture,
% 0.20/0.48      ~r2_hidden(k13_lattice3(sK0,sK2,sK3),sK1) | ~v1_waybel_0(sK1,sK0)).
% 0.20/0.48  
% 0.20/0.48  % (25744)# SZS output end Saturation.
% 0.20/0.48  % (25744)------------------------------
% 0.20/0.48  % (25744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (25744)Termination reason: Satisfiable
% 0.20/0.48  
% 0.20/0.48  % (25744)Memory used [KB]: 1663
% 0.20/0.48  % (25744)Time elapsed: 0.062 s
% 0.20/0.48  % (25744)------------------------------
% 0.20/0.48  % (25744)------------------------------
% 0.20/0.48  % (25730)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (25726)Success in time 0.116 s
%------------------------------------------------------------------------------
