%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:59 EST 2020

% Result     : CounterSatisfiable 1.65s
% Output     : Saturation 1.65s
% Verified   : 
% Statistics : Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    0
%              Number of atoms          :   41 (  41 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u13,negated_conjecture,
    ( r1_lattice3(sK0,sK1,sK2)
    | r2_yellow_0(sK0,sK1) )).

cnf(u8,negated_conjecture,
    ( ~ r1_lattice3(sK0,sK1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | r1_orders_2(sK0,X3,sK2)
    | r2_yellow_0(sK0,sK1) )).

cnf(u9,negated_conjecture,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,X2)
    | m1_subset_1(sK3(X2),u1_struct_0(sK0))
    | ~ m1_subset_1(X2,u1_struct_0(sK0)) )).

cnf(u10,negated_conjecture,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,X2)
    | r1_lattice3(sK0,sK1,sK3(X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK0)) )).

cnf(u11,negated_conjecture,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,X2)
    | ~ r1_orders_2(sK0,sK3(X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK0)) )).

cnf(u19,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK2)
    | r2_yellow_0(sK0,sK1) )).

cnf(u22,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X0,sK2)
    | sK2 = X0
    | r2_yellow_0(sK0,sK1) )).

cnf(u12,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK1) )).

cnf(u21,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X1,X0)
    | X0 = X1 )).

cnf(u15,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u16,axiom,
    ( ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | X1 = X2 )).

cnf(u14,negated_conjecture,
    ( v5_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (29355)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (29355)Refutation not found, incomplete strategy% (29355)------------------------------
% 0.21/0.47  % (29355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29355)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (29355)Memory used [KB]: 6268
% 0.21/0.49  % (29355)Time elapsed: 0.086 s
% 0.21/0.49  % (29355)------------------------------
% 0.21/0.49  % (29355)------------------------------
% 0.21/0.52  % (29371)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (29379)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (29363)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (29371)Refutation not found, incomplete strategy% (29371)------------------------------
% 0.21/0.53  % (29371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29371)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29371)Memory used [KB]: 10746
% 0.21/0.53  % (29371)Time elapsed: 0.133 s
% 0.21/0.53  % (29371)------------------------------
% 0.21/0.53  % (29371)------------------------------
% 0.21/0.53  % (29356)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (29363)Refutation not found, incomplete strategy% (29363)------------------------------
% 0.21/0.53  % (29363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29363)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29363)Memory used [KB]: 6140
% 0.21/0.53  % (29363)Time elapsed: 0.131 s
% 0.21/0.53  % (29363)------------------------------
% 0.21/0.53  % (29363)------------------------------
% 1.42/0.55  % (29353)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.42/0.55  % (29356)Refutation not found, incomplete strategy% (29356)------------------------------
% 1.42/0.55  % (29356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (29356)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (29356)Memory used [KB]: 6140
% 1.42/0.55  % (29356)Time elapsed: 0.130 s
% 1.42/0.55  % (29356)------------------------------
% 1.42/0.55  % (29356)------------------------------
% 1.42/0.56  % (29353)Refutation not found, incomplete strategy% (29353)------------------------------
% 1.42/0.56  % (29353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (29372)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.56  % (29360)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.56  % (29364)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.56  % (29360)Refutation not found, incomplete strategy% (29360)------------------------------
% 1.42/0.56  % (29360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (29360)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (29360)Memory used [KB]: 10618
% 1.42/0.56  % (29360)Time elapsed: 0.140 s
% 1.42/0.56  % (29360)------------------------------
% 1.42/0.56  % (29360)------------------------------
% 1.42/0.56  % (29372)Refutation not found, incomplete strategy% (29372)------------------------------
% 1.42/0.56  % (29372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (29372)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (29372)Memory used [KB]: 1663
% 1.42/0.56  % (29372)Time elapsed: 0.139 s
% 1.42/0.56  % (29372)------------------------------
% 1.42/0.56  % (29372)------------------------------
% 1.42/0.56  % (29354)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.42/0.56  % (29364)Refutation not found, incomplete strategy% (29364)------------------------------
% 1.42/0.56  % (29364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (29364)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (29364)Memory used [KB]: 6268
% 1.65/0.56  % (29353)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.56  
% 1.65/0.56  % (29353)Memory used [KB]: 10618
% 1.65/0.56  % (29353)Time elapsed: 0.143 s
% 1.65/0.56  % (29353)------------------------------
% 1.65/0.56  % (29353)------------------------------
% 1.65/0.56  % (29364)Time elapsed: 0.144 s
% 1.65/0.56  % (29364)------------------------------
% 1.65/0.56  % (29364)------------------------------
% 1.65/0.57  % (29369)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.65/0.57  % (29359)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.65/0.57  % (29357)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.65/0.57  % (29361)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.65/0.57  % SZS status CounterSatisfiable for theBenchmark
% 1.65/0.57  % (29357)# SZS output start Saturation.
% 1.65/0.57  cnf(u13,negated_conjecture,
% 1.65/0.57      r1_lattice3(sK0,sK1,sK2) | r2_yellow_0(sK0,sK1)).
% 1.65/0.57  
% 1.65/0.57  cnf(u8,negated_conjecture,
% 1.65/0.57      ~r1_lattice3(sK0,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_orders_2(sK0,X3,sK2) | r2_yellow_0(sK0,sK1)).
% 1.65/0.57  
% 1.65/0.57  cnf(u9,negated_conjecture,
% 1.65/0.57      ~r2_yellow_0(sK0,sK1) | ~r1_lattice3(sK0,sK1,X2) | m1_subset_1(sK3(X2),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))).
% 1.65/0.57  
% 1.65/0.57  cnf(u10,negated_conjecture,
% 1.65/0.57      ~r2_yellow_0(sK0,sK1) | ~r1_lattice3(sK0,sK1,X2) | r1_lattice3(sK0,sK1,sK3(X2)) | ~m1_subset_1(X2,u1_struct_0(sK0))).
% 1.65/0.57  
% 1.65/0.57  cnf(u11,negated_conjecture,
% 1.65/0.57      ~r2_yellow_0(sK0,sK1) | ~r1_lattice3(sK0,sK1,X2) | ~r1_orders_2(sK0,sK3(X2),X2) | ~m1_subset_1(X2,u1_struct_0(sK0))).
% 1.65/0.57  
% 1.65/0.57  cnf(u19,negated_conjecture,
% 1.65/0.57      r1_orders_2(sK0,sK2,sK2) | r2_yellow_0(sK0,sK1)).
% 1.65/0.57  
% 1.65/0.57  cnf(u22,negated_conjecture,
% 1.65/0.57      ~r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK2) | sK2 = X0 | r2_yellow_0(sK0,sK1)).
% 1.65/0.57  
% 1.65/0.57  cnf(u12,negated_conjecture,
% 1.65/0.57      m1_subset_1(sK2,u1_struct_0(sK0)) | r2_yellow_0(sK0,sK1)).
% 1.65/0.57  
% 1.65/0.57  cnf(u21,negated_conjecture,
% 1.65/0.57      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | X0 = X1).
% 1.65/0.57  
% 1.65/0.57  cnf(u15,negated_conjecture,
% 1.65/0.57      l1_orders_2(sK0)).
% 1.65/0.57  
% 1.65/0.57  cnf(u16,axiom,
% 1.65/0.57      ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X2,X1) | X1 = X2).
% 1.65/0.57  
% 1.65/0.57  cnf(u14,negated_conjecture,
% 1.65/0.57      v5_orders_2(sK0)).
% 1.65/0.57  
% 1.65/0.57  % (29357)# SZS output end Saturation.
% 1.65/0.57  % (29357)------------------------------
% 1.65/0.57  % (29357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.57  % (29357)Termination reason: Satisfiable
% 1.65/0.57  
% 1.65/0.57  % (29357)Memory used [KB]: 6140
% 1.65/0.57  % (29357)Time elapsed: 0.151 s
% 1.65/0.57  % (29357)------------------------------
% 1.65/0.57  % (29357)------------------------------
% 1.65/0.57  % (29359)Refutation not found, incomplete strategy% (29359)------------------------------
% 1.65/0.57  % (29359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.57  % (29359)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.57  
% 1.65/0.57  % (29359)Memory used [KB]: 10618
% 1.65/0.57  % (29359)Time elapsed: 0.151 s
% 1.65/0.57  % (29359)------------------------------
% 1.65/0.57  % (29359)------------------------------
% 1.65/0.57  % (29350)Success in time 0.213 s
%------------------------------------------------------------------------------
