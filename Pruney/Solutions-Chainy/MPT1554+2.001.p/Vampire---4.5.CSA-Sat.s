%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:04 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   20 (  20 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    0
%              Number of atoms          :   53 (  53 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u41,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK5(sK0,sK2))
    | sK1 = k1_yellow_0(sK0,sK2) )).

cnf(u44,negated_conjecture,
    ( r1_orders_2(sK0,sK5(sK0,X0),sK5(sK0,X0)) )).

cnf(u36,negated_conjecture,
    ( r1_orders_2(sK0,sK5(sK0,sK2),sK1)
    | sK1 = k1_yellow_0(sK0,sK2) )).

cnf(u32,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1)
    | sK1 = k1_yellow_0(sK0,sK2) )).

cnf(u20,axiom,
    ( ~ r1_orders_2(X0,X2,sK6(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_lattice3(X0,sK4(X0),X2)
    | ~ l1_orders_2(X0)
    | v3_lattice3(X0) )).

cnf(u13,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | sK1 != k1_yellow_0(sK0,sK2) )).

cnf(u27,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK5(sK0,X0)) )).

cnf(u14,negated_conjecture,
    ( r2_lattice3(sK0,sK2,sK1)
    | sK1 = k1_yellow_0(sK0,sK2) )).

cnf(u18,axiom,
    ( ~ r2_lattice3(X0,sK4(X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | m1_subset_1(sK6(X0,X2),u1_struct_0(X0))
    | v3_lattice3(X0) )).

cnf(u19,axiom,
    ( ~ r2_lattice3(X0,sK4(X0),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,sK4(X0),sK6(X0,X2))
    | v3_lattice3(X0) )).

cnf(u21,axiom,
    ( ~ r2_lattice3(X0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,sK5(X0,X1),X3)
    | ~ v3_lattice3(X0) )).

cnf(u10,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,X3)
    | sK1 = k1_yellow_0(sK0,sK2) )).

cnf(u11,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | sK1 != k1_yellow_0(sK0,sK2) )).

cnf(u12,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK2,sK1)
    | r2_lattice3(sK0,sK2,sK3)
    | sK1 != k1_yellow_0(sK0,sK2) )).

cnf(u25,negated_conjecture,
    ( m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) )).

cnf(u15,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u16,negated_conjecture,
    ( v3_lattice3(sK0) )).

cnf(u22,axiom,
    ( ~ v3_lattice3(X0)
    | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u23,axiom,
    ( ~ v3_lattice3(X0)
    | r2_lattice3(X0,X1,sK5(X0,X1))
    | ~ l1_orders_2(X0) )).

cnf(u17,negated_conjecture,
    ( l1_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:42:07 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.48  % (22292)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (22298)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (22293)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (22302)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (22293)Refutation not found, incomplete strategy% (22293)------------------------------
% 0.22/0.50  % (22293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22293)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22293)Memory used [KB]: 10618
% 0.22/0.50  % (22293)Time elapsed: 0.069 s
% 0.22/0.50  % (22293)------------------------------
% 0.22/0.50  % (22293)------------------------------
% 0.22/0.50  % (22302)Refutation not found, incomplete strategy% (22302)------------------------------
% 0.22/0.50  % (22302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22298)Refutation not found, incomplete strategy% (22298)------------------------------
% 0.22/0.50  % (22298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22302)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22302)Memory used [KB]: 6140
% 0.22/0.50  % (22302)Time elapsed: 0.006 s
% 0.22/0.50  % (22302)------------------------------
% 0.22/0.50  % (22302)------------------------------
% 0.22/0.50  % (22298)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22298)Memory used [KB]: 10618
% 0.22/0.50  % (22298)Time elapsed: 0.008 s
% 0.22/0.50  % (22298)------------------------------
% 0.22/0.50  % (22298)------------------------------
% 0.22/0.50  % (22287)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (22300)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (22301)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (22300)Refutation not found, incomplete strategy% (22300)------------------------------
% 0.22/0.51  % (22300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22300)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22300)Memory used [KB]: 1535
% 0.22/0.51  % (22300)Time elapsed: 0.086 s
% 0.22/0.51  % (22300)------------------------------
% 0.22/0.51  % (22300)------------------------------
% 0.22/0.51  % (22301)Refutation not found, incomplete strategy% (22301)------------------------------
% 0.22/0.51  % (22301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22301)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22301)Memory used [KB]: 10618
% 0.22/0.51  % (22301)Time elapsed: 0.078 s
% 0.22/0.51  % (22301)------------------------------
% 0.22/0.51  % (22301)------------------------------
% 0.22/0.51  % (22295)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (22296)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (22296)Refutation not found, incomplete strategy% (22296)------------------------------
% 0.22/0.52  % (22296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22296)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22296)Memory used [KB]: 10618
% 0.22/0.52  % (22296)Time elapsed: 0.091 s
% 0.22/0.52  % (22296)------------------------------
% 0.22/0.52  % (22296)------------------------------
% 0.22/0.52  % (22287)Refutation not found, incomplete strategy% (22287)------------------------------
% 0.22/0.52  % (22287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22287)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22287)Memory used [KB]: 6140
% 0.22/0.52  % (22287)Time elapsed: 0.095 s
% 0.22/0.52  % (22287)------------------------------
% 0.22/0.52  % (22287)------------------------------
% 0.22/0.52  % (22289)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.52  % (22304)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.53  % (22299)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (22304)# SZS output start Saturation.
% 0.22/0.53  cnf(u41,negated_conjecture,
% 0.22/0.53      r1_orders_2(sK0,sK1,sK5(sK0,sK2)) | sK1 = k1_yellow_0(sK0,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u44,negated_conjecture,
% 0.22/0.53      r1_orders_2(sK0,sK5(sK0,X0),sK5(sK0,X0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u36,negated_conjecture,
% 0.22/0.53      r1_orders_2(sK0,sK5(sK0,sK2),sK1) | sK1 = k1_yellow_0(sK0,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u32,negated_conjecture,
% 0.22/0.53      r1_orders_2(sK0,sK1,sK1) | sK1 = k1_yellow_0(sK0,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u20,axiom,
% 0.22/0.53      ~r1_orders_2(X0,X2,sK6(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,sK4(X0),X2) | ~l1_orders_2(X0) | v3_lattice3(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u13,negated_conjecture,
% 0.22/0.53      ~r1_orders_2(sK0,sK1,sK3) | ~r2_lattice3(sK0,sK2,sK1) | sK1 != k1_yellow_0(sK0,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u27,negated_conjecture,
% 0.22/0.53      r2_lattice3(sK0,X0,sK5(sK0,X0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u14,negated_conjecture,
% 0.22/0.53      r2_lattice3(sK0,sK2,sK1) | sK1 = k1_yellow_0(sK0,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u18,axiom,
% 0.22/0.53      ~r2_lattice3(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK6(X0,X2),u1_struct_0(X0)) | v3_lattice3(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u19,axiom,
% 0.22/0.53      ~r2_lattice3(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,sK4(X0),sK6(X0,X2)) | v3_lattice3(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u21,axiom,
% 0.22/0.53      ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,sK5(X0,X1),X3) | ~v3_lattice3(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u10,negated_conjecture,
% 0.22/0.53      ~r2_lattice3(sK0,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X3) | sK1 = k1_yellow_0(sK0,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u11,negated_conjecture,
% 0.22/0.53      ~r2_lattice3(sK0,sK2,sK1) | m1_subset_1(sK3,u1_struct_0(sK0)) | sK1 != k1_yellow_0(sK0,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u12,negated_conjecture,
% 0.22/0.53      ~r2_lattice3(sK0,sK2,sK1) | r2_lattice3(sK0,sK2,sK3) | sK1 != k1_yellow_0(sK0,sK2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u25,negated_conjecture,
% 0.22/0.53      m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u15,negated_conjecture,
% 0.22/0.53      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u16,negated_conjecture,
% 0.22/0.53      v3_lattice3(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u22,axiom,
% 0.22/0.53      ~v3_lattice3(X0) | m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u23,axiom,
% 0.22/0.53      ~v3_lattice3(X0) | r2_lattice3(X0,X1,sK5(X0,X1)) | ~l1_orders_2(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u17,negated_conjecture,
% 0.22/0.53      l1_orders_2(sK0)).
% 0.22/0.53  
% 0.22/0.53  % (22304)# SZS output end Saturation.
% 0.22/0.53  % (22304)------------------------------
% 0.22/0.53  % (22304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22304)Termination reason: Satisfiable
% 0.22/0.53  
% 0.22/0.53  % (22304)Memory used [KB]: 1663
% 0.22/0.53  % (22304)Time elapsed: 0.104 s
% 0.22/0.53  % (22304)------------------------------
% 0.22/0.53  % (22304)------------------------------
% 0.22/0.53  % (22299)Refutation not found, incomplete strategy% (22299)------------------------------
% 0.22/0.53  % (22299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22299)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22299)Memory used [KB]: 6012
% 0.22/0.53  % (22299)Time elapsed: 0.002 s
% 0.22/0.53  % (22299)------------------------------
% 0.22/0.53  % (22299)------------------------------
% 0.22/0.53  % (22286)Success in time 0.168 s
%------------------------------------------------------------------------------
