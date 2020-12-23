%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:03 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    0
%              Number of atoms          :   47 (  47 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (11115)Memory used [KB]: 1535
% (11115)Time elapsed: 0.094 s
cnf(u23,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1)
    | r1_yellow_0(sK0,sK2) )).

cnf(u31,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1)
    | sK1 = k1_yellow_0(sK0,sK2) )).

cnf(u22,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1)
    | r1_yellow_0(sK0,sK2)
    | sK1 = k1_yellow_0(sK0,sK2) )).

cnf(u10,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | sK1 != k1_yellow_0(sK0,sK2)
    | ~ r1_yellow_0(sK0,sK2) )).

cnf(u13,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,X3)
    | r1_orders_2(sK0,sK1,X3) )).

cnf(u16,negated_conjecture,
    ( r2_lattice3(sK0,sK2,sK1)
    | r1_yellow_0(sK0,sK2) )).

cnf(u17,negated_conjecture,
    ( r2_lattice3(sK0,sK2,sK1)
    | sK1 = k1_yellow_0(sK0,sK2) )).

cnf(u8,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | sK1 != k1_yellow_0(sK0,sK2)
    | ~ r1_yellow_0(sK0,sK2) )).

cnf(u9,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK2,sK1)
    | r2_lattice3(sK0,sK2,sK3)
    | sK1 != k1_yellow_0(sK0,sK2)
    | ~ r1_yellow_0(sK0,sK2) )).

cnf(u11,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,X3)
    | r1_orders_2(sK0,sK1,X3) )).

cnf(u12,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK2,sK1)
    | r2_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,X3)
    | r1_orders_2(sK0,sK1,X3) )).

cnf(u15,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK2)
    | r1_orders_2(sK0,sK1,X3) )).

cnf(u14,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | sK1 = k1_yellow_0(sK0,sK2)
    | r1_orders_2(sK0,sK1,X3) )).

cnf(u18,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:22:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (11117)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (11116)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (11125)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (11124)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (11116)Refutation not found, incomplete strategy% (11116)------------------------------
% 0.21/0.49  % (11116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11116)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (11116)Memory used [KB]: 6140
% 0.21/0.49  % (11116)Time elapsed: 0.053 s
% 0.21/0.49  % (11116)------------------------------
% 0.21/0.49  % (11116)------------------------------
% 0.21/0.50  % (11117)Refutation not found, incomplete strategy% (11117)------------------------------
% 0.21/0.50  % (11117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11117)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (11117)Memory used [KB]: 10618
% 0.21/0.50  % (11117)Time elapsed: 0.061 s
% 0.21/0.50  % (11117)------------------------------
% 0.21/0.50  % (11117)------------------------------
% 0.21/0.50  % (11124)Refutation not found, incomplete strategy% (11124)------------------------------
% 0.21/0.50  % (11124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11124)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (11124)Memory used [KB]: 1663
% 0.21/0.50  % (11124)Time elapsed: 0.066 s
% 0.21/0.50  % (11124)------------------------------
% 0.21/0.50  % (11124)------------------------------
% 0.21/0.50  % (11126)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (11126)Refutation not found, incomplete strategy% (11126)------------------------------
% 0.21/0.50  % (11126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11126)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (11126)Memory used [KB]: 6140
% 0.21/0.50  % (11126)Time elapsed: 0.057 s
% 0.21/0.50  % (11126)------------------------------
% 0.21/0.50  % (11126)------------------------------
% 0.21/0.50  % (11118)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (11111)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (11122)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (11119)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.53  % (11131)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.53  % (11130)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (11123)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (11128)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.53  % (11129)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.53  % (11122)Refutation not found, incomplete strategy% (11122)------------------------------
% 0.21/0.53  % (11122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11122)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11122)Memory used [KB]: 10618
% 0.21/0.53  % (11122)Time elapsed: 0.096 s
% 0.21/0.53  % (11122)------------------------------
% 0.21/0.53  % (11122)------------------------------
% 0.21/0.53  % (11115)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.53  % (11115)Refutation not found, incomplete strategy% (11115)------------------------------
% 0.21/0.53  % (11115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11115)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (11128)# SZS output start Saturation.
% 0.21/0.53  % (11115)Memory used [KB]: 1535
% 0.21/0.53  % (11115)Time elapsed: 0.094 s
% 0.21/0.53  cnf(u23,negated_conjecture,
% 0.21/0.53      r1_orders_2(sK0,sK1,sK1) | r1_yellow_0(sK0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u31,negated_conjecture,
% 0.21/0.53      r1_orders_2(sK0,sK1,sK1) | sK1 = k1_yellow_0(sK0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u22,negated_conjecture,
% 0.21/0.53      r1_orders_2(sK0,sK1,sK1) | r1_yellow_0(sK0,sK2) | sK1 = k1_yellow_0(sK0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u10,negated_conjecture,
% 0.21/0.53      ~r1_orders_2(sK0,sK1,sK3) | ~r2_lattice3(sK0,sK2,sK1) | sK1 != k1_yellow_0(sK0,sK2) | ~r1_yellow_0(sK0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u13,negated_conjecture,
% 0.21/0.53      ~r1_orders_2(sK0,sK1,sK3) | ~r2_lattice3(sK0,sK2,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK2,X3) | r1_orders_2(sK0,sK1,X3)).
% 0.21/0.53  
% 0.21/0.53  cnf(u16,negated_conjecture,
% 0.21/0.53      r2_lattice3(sK0,sK2,sK1) | r1_yellow_0(sK0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u17,negated_conjecture,
% 0.21/0.53      r2_lattice3(sK0,sK2,sK1) | sK1 = k1_yellow_0(sK0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u8,negated_conjecture,
% 0.21/0.53      ~r2_lattice3(sK0,sK2,sK1) | m1_subset_1(sK3,u1_struct_0(sK0)) | sK1 != k1_yellow_0(sK0,sK2) | ~r1_yellow_0(sK0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u9,negated_conjecture,
% 0.21/0.53      ~r2_lattice3(sK0,sK2,sK1) | r2_lattice3(sK0,sK2,sK3) | sK1 != k1_yellow_0(sK0,sK2) | ~r1_yellow_0(sK0,sK2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u11,negated_conjecture,
% 0.21/0.53      ~r2_lattice3(sK0,sK2,sK1) | m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK2,X3) | r1_orders_2(sK0,sK1,X3)).
% 0.21/0.53  
% 0.21/0.53  cnf(u12,negated_conjecture,
% 0.21/0.53      ~r2_lattice3(sK0,sK2,sK1) | r2_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK2,X3) | r1_orders_2(sK0,sK1,X3)).
% 0.21/0.53  
% 0.21/0.53  cnf(u15,negated_conjecture,
% 0.21/0.53      ~r2_lattice3(sK0,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_yellow_0(sK0,sK2) | r1_orders_2(sK0,sK1,X3)).
% 0.21/0.53  
% 0.21/0.53  cnf(u14,negated_conjecture,
% 0.21/0.53      ~r2_lattice3(sK0,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | sK1 = k1_yellow_0(sK0,sK2) | r1_orders_2(sK0,sK1,X3)).
% 0.21/0.53  
% 0.21/0.53  cnf(u18,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.53  
% 0.21/0.53  % (11128)# SZS output end Saturation.
% 0.21/0.53  % (11128)------------------------------
% 0.21/0.53  % (11128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11128)Termination reason: Satisfiable
% 0.21/0.53  
% 0.21/0.53  % (11128)Memory used [KB]: 1663
% 0.21/0.53  % (11128)Time elapsed: 0.053 s
% 0.21/0.53  % (11128)------------------------------
% 0.21/0.53  % (11128)------------------------------
% 0.21/0.53  % (11115)------------------------------
% 0.21/0.53  % (11115)------------------------------
% 0.21/0.53  % (11123)Refutation not found, incomplete strategy% (11123)------------------------------
% 0.21/0.53  % (11123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11123)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11123)Memory used [KB]: 6012
% 0.21/0.53  % (11123)Time elapsed: 0.003 s
% 0.21/0.53  % (11123)------------------------------
% 0.21/0.53  % (11123)------------------------------
% 0.21/0.53  % (11127)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.53  % (11110)Success in time 0.163 s
%------------------------------------------------------------------------------
