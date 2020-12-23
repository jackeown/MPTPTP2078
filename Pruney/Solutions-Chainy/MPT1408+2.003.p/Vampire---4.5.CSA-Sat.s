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
% DateTime   : Thu Dec  3 13:15:29 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   36 (  36 expanded)
%              Number of leaves         :   36 (  36 expanded)
%              Depth                    :    0
%              Number of atoms          :  149 ( 149 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal clause size      :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u84,negated_conjecture,
    ( r3_lattices(sK0,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r1_lattices(sK0,X1,X0) )).

cnf(u48,axiom,
    ( ~ r3_lattices(X0,X1,X2)
    | r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | ~ v9_lattices(X0)
    | ~ v8_lattices(X0)
    | ~ v6_lattices(X0)
    | v2_struct_0(X0) )).

cnf(u35,axiom,
    ( l1_lattices(X0)
    | ~ l3_lattices(X0) )).

cnf(u61,negated_conjecture,
    ( r1_lattices(sK0,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_lattices(sK0,X1,X0) != X0 )).

cnf(u69,negated_conjecture,
    ( ~ r1_lattices(sK0,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | X0 = X1
    | ~ r1_lattices(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u71,negated_conjecture,
    ( ~ r1_lattices(sK0,X1,X0)
    | X0 = X1
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) != X1 )).

cnf(u46,axiom,
    ( ~ r1_lattices(X0,X1,X2)
    | k1_lattices(X0,X1,X2) = X2
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l2_lattices(X0)
    | v2_struct_0(X0) )).

cnf(u32,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u31,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u56,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X0) = X0 )).

cnf(u73,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | X0 = X1
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,X0,X1) != X1
    | k1_lattices(sK0,X1,X0) != X0 )).

cnf(u36,axiom,
    ( l2_lattices(X0)
    | ~ l3_lattices(X0) )).

cnf(u47,axiom,
    ( ~ l2_lattices(X0)
    | k1_lattices(X0,X1,X2) != X2
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_lattices(X0,X1,X2)
    | v2_struct_0(X0) )).

cnf(u44,axiom,
    ( ~ l2_lattices(X0)
    | ~ r1_lattices(X0,X2,X1)
    | ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | X1 = X2
    | ~ v4_lattices(X0)
    | v2_struct_0(X0) )).

cnf(u43,axiom,
    ( v9_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) )).

cnf(u45,axiom,
    ( ~ v9_lattices(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | k1_lattices(X0,X1,X1) = X1
    | ~ v8_lattices(X0)
    | ~ v6_lattices(X0)
    | v2_struct_0(X0) )).

cnf(u49,axiom,
    ( ~ v9_lattices(X0)
    | ~ r1_lattices(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | r3_lattices(X0,X1,X2)
    | ~ v8_lattices(X0)
    | ~ v6_lattices(X0)
    | v2_struct_0(X0) )).

cnf(u42,axiom,
    ( v8_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) )).

cnf(u41,axiom,
    ( v7_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) )).

cnf(u40,axiom,
    ( v6_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) )).

cnf(u39,axiom,
    ( v5_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) )).

cnf(u38,axiom,
    ( v4_lattices(X0)
    | ~ v10_lattices(X0)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) )).

cnf(u64,axiom,
    ( ~ v4_lattices(X0)
    | ~ r1_lattices(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | X1 = X2
    | ~ r1_lattices(X0,X1,X2)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0) )).

cnf(u29,negated_conjecture,
    ( v10_lattices(sK0) )).

cnf(u53,axiom,
    ( ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | k1_lattices(X1,X0,X0) = X0
    | v2_struct_0(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1)) )).

cnf(u66,axiom,
    ( ~ v10_lattices(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | X1 = X2
    | ~ r1_lattices(X0,X2,X1)
    | v2_struct_0(X0)
    | ~ l3_lattices(X0)
    | ~ r1_lattices(X0,X1,X2) )).

cnf(u81,axiom,
    ( ~ v10_lattices(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l3_lattices(X0)
    | r3_lattices(X0,X1,X2)
    | v2_struct_0(X0)
    | ~ r1_lattices(X0,X1,X2) )).

cnf(u28,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u30,negated_conjecture,
    ( l3_lattices(sK0) )).

cnf(u59,axiom,
    ( ~ l3_lattices(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_lattices(X0,X1,X2)
    | v2_struct_0(X0)
    | k1_lattices(X0,X1,X2) != X2 )).

cnf(u58,negated_conjecture,
    ( sK2 = k1_lattices(sK0,sK2,sK2) )).

cnf(u57,negated_conjecture,
    ( sK1 = k1_lattices(sK0,sK1,sK1) )).

cnf(u33,negated_conjecture,
    ( k2_filter_0(sK0,sK1) = k2_filter_0(sK0,sK2) )).

cnf(u75,negated_conjecture,
    ( sK2 != k1_lattices(sK0,X1,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k1_lattices(sK0,sK2,X1) != X1
    | sK2 = X1 )).

cnf(u74,negated_conjecture,
    ( sK1 != k1_lattices(sK0,X0,sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_lattices(sK0,sK1,X0) != X0
    | sK1 = X0 )).

cnf(u34,negated_conjecture,
    ( sK1 != sK2 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:02:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (29513)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (29505)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (29513)Refutation not found, incomplete strategy% (29513)------------------------------
% 0.22/0.51  % (29513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (29513)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (29513)Memory used [KB]: 6140
% 0.22/0.51  % (29513)Time elapsed: 0.093 s
% 0.22/0.51  % (29513)------------------------------
% 0.22/0.51  % (29513)------------------------------
% 0.22/0.51  % (29505)Refutation not found, incomplete strategy% (29505)------------------------------
% 0.22/0.51  % (29505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (29505)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (29505)Memory used [KB]: 6140
% 0.22/0.51  % (29505)Time elapsed: 0.094 s
% 0.22/0.51  % (29505)------------------------------
% 0.22/0.51  % (29505)------------------------------
% 0.22/0.52  % (29523)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (29523)# SZS output start Saturation.
% 0.22/0.52  cnf(u84,negated_conjecture,
% 0.22/0.52      r3_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattices(sK0,X1,X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u48,axiom,
% 0.22/0.52      ~r3_lattices(X0,X1,X2) | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u35,axiom,
% 0.22/0.52      l1_lattices(X0) | ~l3_lattices(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u61,negated_conjecture,
% 0.22/0.52      r1_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,X1,X0) != X0).
% 0.22/0.52  
% 0.22/0.52  cnf(u69,negated_conjecture,
% 0.22/0.52      ~r1_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | X0 = X1 | ~r1_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.22/0.52  
% 0.22/0.52  cnf(u71,negated_conjecture,
% 0.22/0.52      ~r1_lattices(sK0,X1,X0) | X0 = X1 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,X0,X1) != X1).
% 0.22/0.52  
% 0.22/0.52  cnf(u46,axiom,
% 0.22/0.52      ~r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u32,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.22/0.52  
% 0.22/0.52  cnf(u31,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.52  
% 0.22/0.52  cnf(u56,negated_conjecture,
% 0.22/0.52      ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,X0,X0) = X0).
% 0.22/0.52  
% 0.22/0.52  cnf(u73,negated_conjecture,
% 0.22/0.52      ~m1_subset_1(X0,u1_struct_0(sK0)) | X0 = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,X0,X1) != X1 | k1_lattices(sK0,X1,X0) != X0).
% 0.22/0.52  
% 0.22/0.52  cnf(u36,axiom,
% 0.22/0.52      l2_lattices(X0) | ~l3_lattices(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u47,axiom,
% 0.22/0.52      ~l2_lattices(X0) | k1_lattices(X0,X1,X2) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | v2_struct_0(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u44,axiom,
% 0.22/0.52      ~l2_lattices(X0) | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | X1 = X2 | ~v4_lattices(X0) | v2_struct_0(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u43,axiom,
% 0.22/0.52      v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u45,axiom,
% 0.22/0.52      ~v9_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k1_lattices(X0,X1,X1) = X1 | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u49,axiom,
% 0.22/0.52      ~v9_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u42,axiom,
% 0.22/0.52      v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u41,axiom,
% 0.22/0.52      v7_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u40,axiom,
% 0.22/0.52      v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u39,axiom,
% 0.22/0.52      v5_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u38,axiom,
% 0.22/0.52      v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u64,axiom,
% 0.22/0.52      ~v4_lattices(X0) | ~r1_lattices(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | X1 = X2 | ~r1_lattices(X0,X1,X2) | v2_struct_0(X0) | ~l3_lattices(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u29,negated_conjecture,
% 0.22/0.52      v10_lattices(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u53,axiom,
% 0.22/0.52      ~v10_lattices(X1) | ~l3_lattices(X1) | k1_lattices(X1,X0,X0) = X0 | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))).
% 0.22/0.52  
% 0.22/0.52  cnf(u66,axiom,
% 0.22/0.52      ~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | X1 = X2 | ~r1_lattices(X0,X2,X1) | v2_struct_0(X0) | ~l3_lattices(X0) | ~r1_lattices(X0,X1,X2)).
% 0.22/0.52  
% 0.22/0.52  cnf(u81,axiom,
% 0.22/0.52      ~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | v2_struct_0(X0) | ~r1_lattices(X0,X1,X2)).
% 0.22/0.52  
% 0.22/0.52  cnf(u28,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u30,negated_conjecture,
% 0.22/0.52      l3_lattices(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u59,axiom,
% 0.22/0.52      ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | v2_struct_0(X0) | k1_lattices(X0,X1,X2) != X2).
% 0.22/0.52  
% 0.22/0.52  cnf(u58,negated_conjecture,
% 0.22/0.52      sK2 = k1_lattices(sK0,sK2,sK2)).
% 0.22/0.52  
% 0.22/0.52  cnf(u57,negated_conjecture,
% 0.22/0.52      sK1 = k1_lattices(sK0,sK1,sK1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u33,negated_conjecture,
% 0.22/0.52      k2_filter_0(sK0,sK1) = k2_filter_0(sK0,sK2)).
% 0.22/0.52  
% 0.22/0.52  cnf(u75,negated_conjecture,
% 0.22/0.52      sK2 != k1_lattices(sK0,X1,sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,sK2,X1) != X1 | sK2 = X1).
% 0.22/0.52  
% 0.22/0.52  cnf(u74,negated_conjecture,
% 0.22/0.52      sK1 != k1_lattices(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,sK1,X0) != X0 | sK1 = X0).
% 0.22/0.52  
% 0.22/0.52  cnf(u34,negated_conjecture,
% 0.22/0.52      sK1 != sK2).
% 0.22/0.52  
% 0.22/0.52  % (29523)# SZS output end Saturation.
% 0.22/0.52  % (29523)------------------------------
% 0.22/0.52  % (29523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (29523)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (29523)Memory used [KB]: 6140
% 0.22/0.52  % (29523)Time elapsed: 0.103 s
% 0.22/0.52  % (29523)------------------------------
% 0.22/0.52  % (29523)------------------------------
% 0.22/0.52  % (29511)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (29527)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (29499)Success in time 0.154 s
%------------------------------------------------------------------------------
