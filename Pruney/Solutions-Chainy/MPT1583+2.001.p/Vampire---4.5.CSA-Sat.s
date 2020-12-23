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
% DateTime   : Thu Dec  3 13:16:23 EST 2020

% Result     : CounterSatisfiable 1.43s
% Output     : Saturation 1.43s
% Verified   : 
% Statistics : Number of clauses        :   42 (  42 expanded)
%              Number of leaves         :   42 (  42 expanded)
%              Depth                    :    0
%              Number of atoms          :  136 ( 136 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u24,negated_conjecture,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u52,negated_conjecture,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK1,sK2,sK3) )).

cnf(u60,negated_conjecture,
    ( ~ r2_lattice3(sK0,X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X2)
    | r1_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u49,negated_conjecture,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u51,negated_conjecture,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | ~ r1_lattice3(sK1,sK2,sK3) )).

cnf(u80,negated_conjecture,
    ( r1_orders_2(sK0,sK6(sK0,sK2,X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,X0) )).

cnf(u73,negated_conjecture,
    ( r1_orders_2(sK0,sK5(sK0,sK2,X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK2,X0) )).

cnf(u40,axiom,
    ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u36,axiom,
    ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u37,axiom,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r1_orders_2(X0,X2,X3)
    | ~ l1_orders_2(X0) )).

cnf(u63,negated_conjecture,
    ( ~ r1_lattice3(sK1,sK2,sK3)
    | ~ r2_hidden(X0,sK2)
    | r1_orders_2(sK0,X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u31,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u32,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u33,axiom,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_lattice3(X0,X1,X2) )).

cnf(u65,negated_conjecture,
    ( ~ l1_orders_2(X0)
    | r1_orders_2(sK0,sK5(X0,sK2,X1),sK3)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(sK5(X0,sK2,X1),u1_struct_0(sK0))
    | r2_lattice3(X0,sK2,X1) )).

cnf(u66,negated_conjecture,
    ( ~ l1_orders_2(X2)
    | r1_orders_2(sK0,sK6(X2,sK2,X3),sK3)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK6(X2,sK2,X3),u1_struct_0(sK0))
    | r1_lattice3(X2,sK2,X3) )).

cnf(u54,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u30,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u29,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u53,axiom,
    ( m1_subset_1(X1,X0)
    | ~ r2_hidden(X1,X0) )).

cnf(u38,axiom,
    ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u34,axiom,
    ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u48,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) )).

cnf(u28,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u67,negated_conjecture,
    ( ~ m1_subset_1(sK7(sK2),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK7(sK2),sK3)
    | r1_lattice3(sK0,sK2,sK3)
    | v1_xboole_0(sK2) )).

cnf(u76,negated_conjecture,
    ( ~ m1_subset_1(sK6(sK0,sK2,X0),u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK6(sK0,sK2,X0),sK3)
    | r1_lattice3(sK0,sK2,X0) )).

cnf(u69,negated_conjecture,
    ( ~ m1_subset_1(sK5(sK0,sK2,X0),u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK5(sK0,sK2,X0),sK3)
    | r2_lattice3(sK0,sK2,X0) )).

cnf(u47,axiom,
    ( ~ m1_subset_1(X1,X0)
    | r2_hidden(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u42,axiom,
    ( r2_hidden(sK7(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u59,axiom,
    ( r2_hidden(sK6(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | r1_lattice3(X1,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1)) )).

cnf(u39,axiom,
    ( r2_hidden(sK6(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u58,axiom,
    ( r2_hidden(sK5(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | r2_lattice3(X1,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1)) )).

cnf(u35,axiom,
    ( r2_hidden(sK5(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u56,negated_conjecture,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u55,negated_conjecture,
    ( r2_hidden(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u68,negated_conjecture,
    ( ~ r2_hidden(sK7(sK2),u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | v1_xboole_0(sK2)
    | r1_orders_2(sK0,sK7(sK2),sK3) )).

cnf(u64,negated_conjecture,
    ( ~ r2_hidden(X1,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,X1,sK3)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u41,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u43,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ r2_hidden(X1,X0) )).

cnf(u44,axiom,
    ( ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0)
    | m1_subset_1(X1,X0) )).

% (32756)Refutation not found, incomplete strategy% (32756)------------------------------
% (32756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
cnf(u45,axiom,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X0) )).

cnf(u27,negated_conjecture,
    ( sK3 = sK4 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (32742)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (32750)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (32748)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (32758)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.55  % (32756)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.43/0.55  % (32740)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.43/0.55  % (32745)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.43/0.55  % (32740)# SZS output start Saturation.
% 1.43/0.55  cnf(u24,negated_conjecture,
% 1.43/0.55      r2_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)).
% 1.43/0.55  
% 1.43/0.55  cnf(u52,negated_conjecture,
% 1.43/0.55      r2_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK1,sK2,sK3)).
% 1.43/0.55  
% 1.43/0.55  cnf(u60,negated_conjecture,
% 1.43/0.55      ~r2_lattice3(sK0,X2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 1.43/0.55  
% 1.43/0.55  cnf(u49,negated_conjecture,
% 1.43/0.55      ~r2_lattice3(sK1,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)).
% 1.43/0.55  
% 1.43/0.55  cnf(u51,negated_conjecture,
% 1.43/0.55      ~r2_lattice3(sK1,sK2,sK3) | ~r1_lattice3(sK1,sK2,sK3)).
% 1.43/0.55  
% 1.43/0.55  cnf(u80,negated_conjecture,
% 1.43/0.55      r1_orders_2(sK0,sK6(sK0,sK2,X0),sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK2,X0)).
% 1.43/0.55  
% 1.43/0.55  cnf(u73,negated_conjecture,
% 1.43/0.55      r1_orders_2(sK0,sK5(sK0,sK2,X0),sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,sK2,X0)).
% 1.43/0.55  
% 1.43/0.55  cnf(u40,axiom,
% 1.43/0.55      ~r1_orders_2(X0,X2,sK6(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 1.43/0.55  
% 1.43/0.55  cnf(u36,axiom,
% 1.43/0.55      ~r1_orders_2(X0,sK5(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 1.43/0.55  
% 1.43/0.55  cnf(u37,axiom,
% 1.43/0.55      ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X2,X3) | ~l1_orders_2(X0)).
% 1.43/0.55  
% 1.43/0.55  cnf(u63,negated_conjecture,
% 1.43/0.55      ~r1_lattice3(sK1,sK2,sK3) | ~r2_hidden(X0,sK2) | r1_orders_2(sK0,X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 1.43/0.55  
% 1.43/0.55  cnf(u31,negated_conjecture,
% 1.43/0.55      l1_orders_2(sK0)).
% 1.43/0.55  
% 1.43/0.55  cnf(u32,axiom,
% 1.43/0.55      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 1.43/0.55  
% 1.43/0.55  cnf(u33,axiom,
% 1.43/0.55      ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2)).
% 1.43/0.55  
% 1.43/0.55  cnf(u65,negated_conjecture,
% 1.43/0.55      ~l1_orders_2(X0) | r1_orders_2(sK0,sK5(X0,sK2,X1),sK3) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(sK5(X0,sK2,X1),u1_struct_0(sK0)) | r2_lattice3(X0,sK2,X1)).
% 1.43/0.55  
% 1.43/0.55  cnf(u66,negated_conjecture,
% 1.43/0.55      ~l1_orders_2(X2) | r1_orders_2(sK0,sK6(X2,sK2,X3),sK3) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_subset_1(sK6(X2,sK2,X3),u1_struct_0(sK0)) | r1_lattice3(X2,sK2,X3)).
% 1.43/0.55  
% 1.43/0.55  cnf(u54,negated_conjecture,
% 1.43/0.55      l1_struct_0(sK0)).
% 1.43/0.55  
% 1.43/0.55  cnf(u30,negated_conjecture,
% 1.43/0.55      ~v2_struct_0(sK0)).
% 1.43/0.55  
% 1.43/0.55  cnf(u29,negated_conjecture,
% 1.43/0.55      ~v2_struct_0(sK1)).
% 1.43/0.55  
% 1.43/0.55  cnf(u53,axiom,
% 1.43/0.55      m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)).
% 1.43/0.55  
% 1.43/0.55  cnf(u38,axiom,
% 1.43/0.55      m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 1.43/0.55  
% 1.43/0.55  cnf(u34,axiom,
% 1.43/0.55      m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 1.43/0.55  
% 1.43/0.55  cnf(u48,negated_conjecture,
% 1.43/0.55      m1_subset_1(sK3,u1_struct_0(sK1))).
% 1.43/0.55  
% 1.43/0.55  cnf(u28,negated_conjecture,
% 1.43/0.55      m1_subset_1(sK3,u1_struct_0(sK0))).
% 1.43/0.55  
% 1.43/0.55  cnf(u67,negated_conjecture,
% 1.43/0.55      ~m1_subset_1(sK7(sK2),u1_struct_0(sK0)) | r1_orders_2(sK0,sK7(sK2),sK3) | r1_lattice3(sK0,sK2,sK3) | v1_xboole_0(sK2)).
% 1.43/0.55  
% 1.43/0.55  cnf(u76,negated_conjecture,
% 1.43/0.55      ~m1_subset_1(sK6(sK0,sK2,X0),u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK6(sK0,sK2,X0),sK3) | r1_lattice3(sK0,sK2,X0)).
% 1.43/0.55  
% 1.43/0.56  cnf(u69,negated_conjecture,
% 1.43/0.56      ~m1_subset_1(sK5(sK0,sK2,X0),u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK5(sK0,sK2,X0),sK3) | r2_lattice3(sK0,sK2,X0)).
% 1.43/0.56  
% 1.43/0.56  cnf(u47,axiom,
% 1.43/0.56      ~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)).
% 1.43/0.56  
% 1.43/0.56  cnf(u42,axiom,
% 1.43/0.56      r2_hidden(sK7(X0),X0) | v1_xboole_0(X0)).
% 1.43/0.56  
% 1.43/0.56  cnf(u59,axiom,
% 1.43/0.56      r2_hidden(sK6(X1,X2,X0),u1_struct_0(X1)) | ~l1_orders_2(X1) | r1_lattice3(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X1))).
% 1.43/0.56  
% 1.43/0.56  cnf(u39,axiom,
% 1.43/0.56      r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 1.43/0.56  
% 1.43/0.56  cnf(u58,axiom,
% 1.43/0.56      r2_hidden(sK5(X1,X2,X0),u1_struct_0(X1)) | ~l1_orders_2(X1) | r2_lattice3(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X1))).
% 1.43/0.56  
% 1.43/0.56  cnf(u35,axiom,
% 1.43/0.56      r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 1.43/0.56  
% 1.43/0.56  cnf(u56,negated_conjecture,
% 1.43/0.56      r2_hidden(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))).
% 1.43/0.56  
% 1.43/0.56  cnf(u55,negated_conjecture,
% 1.43/0.56      r2_hidden(sK3,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))).
% 1.43/0.56  
% 1.43/0.56  cnf(u68,negated_conjecture,
% 1.43/0.56      ~r2_hidden(sK7(sK2),u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | v1_xboole_0(sK2) | r1_orders_2(sK0,sK7(sK2),sK3)).
% 1.43/0.56  
% 1.43/0.56  cnf(u64,negated_conjecture,
% 1.43/0.56      ~r2_hidden(X1,sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK3) | r1_lattice3(sK0,sK2,sK3)).
% 1.43/0.56  
% 1.43/0.56  cnf(u41,axiom,
% 1.43/0.56      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 1.43/0.56  
% 1.43/0.56  cnf(u43,axiom,
% 1.43/0.56      ~v1_xboole_0(X0) | ~r2_hidden(X1,X0)).
% 1.43/0.56  
% 1.43/0.56  cnf(u44,axiom,
% 1.43/0.56      ~v1_xboole_0(X1) | ~v1_xboole_0(X0) | m1_subset_1(X1,X0)).
% 1.43/0.56  
% 1.43/0.56  % (32756)Refutation not found, incomplete strategy% (32756)------------------------------
% 1.43/0.56  % (32756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  cnf(u45,axiom,
% 1.43/0.56      ~v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,X0)).
% 1.43/0.56  
% 1.43/0.56  cnf(u27,negated_conjecture,
% 1.43/0.56      sK3 = sK4).
% 1.43/0.56  
% 1.43/0.56  % (32740)# SZS output end Saturation.
% 1.43/0.56  % (32740)------------------------------
% 1.43/0.56  % (32740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (32740)Termination reason: Satisfiable
% 1.43/0.56  
% 1.43/0.56  % (32740)Memory used [KB]: 6268
% 1.43/0.56  % (32740)Time elapsed: 0.126 s
% 1.43/0.56  % (32740)------------------------------
% 1.43/0.56  % (32740)------------------------------
% 1.53/0.57  % (32733)Success in time 0.201 s
%------------------------------------------------------------------------------
