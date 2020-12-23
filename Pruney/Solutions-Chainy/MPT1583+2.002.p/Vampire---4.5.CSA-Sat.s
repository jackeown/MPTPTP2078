%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:23 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   36 (  36 expanded)
%              Number of leaves         :   36 (  36 expanded)
%              Depth                    :    0
%              Number of atoms          :  118 ( 118 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u26,negated_conjecture,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u50,negated_conjecture,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK1,sK2,sK3) )).

cnf(u57,negated_conjecture,
    ( ~ r2_lattice3(sK0,X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X2)
    | r1_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u47,negated_conjecture,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u49,negated_conjecture,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | ~ r1_lattice3(sK1,sK2,sK3) )).

cnf(u75,negated_conjecture,
    ( r1_orders_2(sK0,sK6(sK0,sK2,X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,X0) )).

cnf(u68,negated_conjecture,
    ( r1_orders_2(sK0,sK5(sK0,sK2,X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK2,X0) )).

cnf(u42,axiom,
    ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u38,axiom,
    ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u39,axiom,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r1_orders_2(X0,X2,X3)
    | ~ l1_orders_2(X0) )).

cnf(u60,negated_conjecture,
    ( ~ r1_lattice3(sK1,sK2,sK3)
    | ~ r2_hidden(X0,sK2)
    | r1_orders_2(sK0,X0,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u33,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u34,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u35,axiom,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_lattice3(X0,X1,X2) )).

cnf(u62,negated_conjecture,
    ( ~ l1_orders_2(X0)
    | r1_orders_2(sK0,sK5(X0,sK2,X1),sK3)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(sK5(X0,sK2,X1),u1_struct_0(sK0))
    | r2_lattice3(X0,sK2,X1) )).

cnf(u63,negated_conjecture,
    ( ~ l1_orders_2(X2)
    | r1_orders_2(sK0,sK6(X2,sK2,X3),sK3)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(sK6(X2,sK2,X3),u1_struct_0(sK0))
    | r1_lattice3(X2,sK2,X3) )).

cnf(u51,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u32,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u31,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u43,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u44,axiom,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) )).

cnf(u40,axiom,
    ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u36,axiom,
    ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u46,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) )).

cnf(u30,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u71,negated_conjecture,
    ( ~ m1_subset_1(sK6(sK0,sK2,X0),u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK6(sK0,sK2,X0),sK3)
    | r1_lattice3(sK0,sK2,X0) )).

cnf(u64,negated_conjecture,
    ( ~ m1_subset_1(sK5(sK0,sK2,X0),u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK5(sK0,sK2,X0),sK3)
    | r2_lattice3(sK0,sK2,X0) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | r2_hidden(X0,X1) )).

cnf(u41,axiom,
    ( r2_hidden(sK6(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u37,axiom,
    ( r2_hidden(sK5(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u56,axiom,
    ( r2_hidden(sK6(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | r1_lattice3(X1,X2,X0)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(X1)) )).

cnf(u55,axiom,
    ( r2_hidden(sK5(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | r2_lattice3(X1,X2,X0)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(X1)) )).

cnf(u53,negated_conjecture,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u52,negated_conjecture,
    ( r2_hidden(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u61,negated_conjecture,
    ( ~ r2_hidden(X1,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK0,X1,sK3)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u29,negated_conjecture,
    ( sK3 = sK4 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:16:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (15817)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (15834)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (15832)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (15815)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (15826)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (15817)# SZS output start Saturation.
% 0.21/0.51  cnf(u26,negated_conjecture,
% 0.21/0.51      r2_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)).
% 0.21/0.51  
% 0.21/0.51  cnf(u50,negated_conjecture,
% 0.21/0.51      r2_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK1,sK2,sK3)).
% 0.21/0.51  
% 0.21/0.51  cnf(u57,negated_conjecture,
% 0.21/0.51      ~r2_lattice3(sK0,X2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X2) | r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u47,negated_conjecture,
% 0.21/0.51      ~r2_lattice3(sK1,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)).
% 0.21/0.51  
% 0.21/0.51  cnf(u49,negated_conjecture,
% 0.21/0.51      ~r2_lattice3(sK1,sK2,sK3) | ~r1_lattice3(sK1,sK2,sK3)).
% 0.21/0.51  
% 0.21/0.51  cnf(u75,negated_conjecture,
% 0.21/0.51      r1_orders_2(sK0,sK6(sK0,sK2,X0),sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK2,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u68,negated_conjecture,
% 0.21/0.51      r1_orders_2(sK0,sK5(sK0,sK2,X0),sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,sK2,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u42,axiom,
% 0.21/0.51      ~r1_orders_2(X0,X2,sK6(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u38,axiom,
% 0.21/0.51      ~r1_orders_2(X0,sK5(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u39,axiom,
% 0.21/0.51      ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X2,X3) | ~l1_orders_2(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u60,negated_conjecture,
% 0.21/0.51      ~r1_lattice3(sK1,sK2,sK3) | ~r2_hidden(X0,sK2) | r1_orders_2(sK0,X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u33,negated_conjecture,
% 0.21/0.51      l1_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u34,axiom,
% 0.21/0.51      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u35,axiom,
% 0.21/0.51      ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u62,negated_conjecture,
% 0.21/0.51      ~l1_orders_2(X0) | r1_orders_2(sK0,sK5(X0,sK2,X1),sK3) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(sK5(X0,sK2,X1),u1_struct_0(sK0)) | r2_lattice3(X0,sK2,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u63,negated_conjecture,
% 0.21/0.51      ~l1_orders_2(X2) | r1_orders_2(sK0,sK6(X2,sK2,X3),sK3) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_subset_1(sK6(X2,sK2,X3),u1_struct_0(sK0)) | r1_lattice3(X2,sK2,X3)).
% 0.21/0.51  
% 0.21/0.51  cnf(u51,negated_conjecture,
% 0.21/0.51      l1_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u32,negated_conjecture,
% 0.21/0.51      ~v2_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u31,negated_conjecture,
% 0.21/0.51      ~v2_struct_0(sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u43,axiom,
% 0.21/0.51      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u44,axiom,
% 0.21/0.51      m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u40,axiom,
% 0.21/0.51      m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u36,axiom,
% 0.21/0.51      m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u46,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK3,u1_struct_0(sK1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u30,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u71,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(sK6(sK0,sK2,X0),u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK6(sK0,sK2,X0),sK3) | r1_lattice3(sK0,sK2,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u64,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(sK5(sK0,sK2,X0),u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK5(sK0,sK2,X0),sK3) | r2_lattice3(sK0,sK2,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u45,axiom,
% 0.21/0.51      ~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u41,axiom,
% 0.21/0.51      r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u37,axiom,
% 0.21/0.51      r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u56,axiom,
% 0.21/0.51      r2_hidden(sK6(X1,X2,X0),u1_struct_0(X1)) | ~l1_orders_2(X1) | r1_lattice3(X1,X2,X0) | v1_xboole_0(u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u55,axiom,
% 0.21/0.51      r2_hidden(sK5(X1,X2,X0),u1_struct_0(X1)) | ~l1_orders_2(X1) | r2_lattice3(X1,X2,X0) | v1_xboole_0(u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u53,negated_conjecture,
% 0.21/0.51      r2_hidden(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u52,negated_conjecture,
% 0.21/0.51      r2_hidden(sK3,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u61,negated_conjecture,
% 0.21/0.51      ~r2_hidden(X1,sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK3) | r1_lattice3(sK0,sK2,sK3)).
% 0.21/0.51  
% 0.21/0.51  cnf(u29,negated_conjecture,
% 0.21/0.51      sK3 = sK4).
% 0.21/0.51  
% 0.21/0.51  % (15817)# SZS output end Saturation.
% 0.21/0.51  % (15817)------------------------------
% 0.21/0.51  % (15817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15817)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (15817)Memory used [KB]: 6268
% 0.21/0.51  % (15817)Time elapsed: 0.089 s
% 0.21/0.51  % (15817)------------------------------
% 0.21/0.51  % (15817)------------------------------
% 0.21/0.52  % (15809)Success in time 0.15 s
%------------------------------------------------------------------------------
