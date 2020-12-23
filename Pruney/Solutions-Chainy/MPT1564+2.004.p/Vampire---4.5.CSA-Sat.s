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
% DateTime   : Thu Dec  3 13:16:14 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   30 (  30 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    0
%              Number of atoms          :   81 (  81 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u66,axiom,
    ( sP3(k1_xboole_0) )).

cnf(u59,axiom,
    ( ~ sP3(X1)
    | ~ r2_hidden(X0,X1) )).

cnf(u49,axiom,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_orders_2(X0,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u52,axiom,
    ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u48,axiom,
    ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
    | r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u45,axiom,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_orders_2(X0,X2,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u41,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u44,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u47,axiom,
    ( ~ l1_orders_2(X0)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2) )).

cnf(u51,axiom,
    ( ~ l1_orders_2(X0)
    | r2_hidden(sK2(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2) )).

cnf(u46,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2) )).

cnf(u50,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2) )).

cnf(u60,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u53,axiom,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0) )).

cnf(u40,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u68,axiom,
    ( ~ r2_hidden(X0,k1_xboole_0) )).

cnf(u54,axiom,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) )).

cnf(u56,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u43,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u70,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(sK1(sK0,X0,X1),X0)
    | r1_lattice3(sK0,X0,X1) )).

cnf(u71,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(sK2(sK0,X0,X1),X0)
    | r2_lattice3(sK0,X0,X1) )).

cnf(u74,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK1(sK0,X0,X1),u1_struct_0(sK0))
    | r1_lattice3(sK0,X0,X1) )).

cnf(u76,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
    | r2_lattice3(sK0,X0,X1) )).

cnf(u75,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))
    | sP3(X1) )).

cnf(u67,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | sP3(X0) )).

cnf(u55,axiom,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | r2_hidden(X0,X1) )).

cnf(u65,axiom,
    ( v1_xboole_0(k1_zfmisc_1(X0))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u42,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u58,axiom,
    ( ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | sP3(X1) )).

cnf(u62,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:58:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (20324)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.50  % (20324)Refutation not found, incomplete strategy% (20324)------------------------------
% 0.22/0.50  % (20324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (20329)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (20324)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (20324)Memory used [KB]: 9850
% 0.22/0.50  % (20324)Time elapsed: 0.069 s
% 0.22/0.50  % (20324)------------------------------
% 0.22/0.50  % (20324)------------------------------
% 0.22/0.50  % (20323)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.51  % (20341)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.22/0.51  % (20332)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (20341)# SZS output start Saturation.
% 0.22/0.51  cnf(u66,axiom,
% 0.22/0.51      sP3(k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u59,axiom,
% 0.22/0.51      ~sP3(X1) | ~r2_hidden(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u49,axiom,
% 0.22/0.51      ~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u52,axiom,
% 0.22/0.51      ~r1_orders_2(X0,sK2(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u48,axiom,
% 0.22/0.51      ~r1_orders_2(X0,X2,sK1(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u45,axiom,
% 0.22/0.51      ~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u41,negated_conjecture,
% 0.22/0.51      l1_orders_2(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u44,axiom,
% 0.22/0.51      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u47,axiom,
% 0.22/0.51      ~l1_orders_2(X0) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u51,axiom,
% 0.22/0.51      ~l1_orders_2(X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u46,axiom,
% 0.22/0.51      ~l1_orders_2(X0) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u50,axiom,
% 0.22/0.51      ~l1_orders_2(X0) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u60,negated_conjecture,
% 0.22/0.51      l1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u53,axiom,
% 0.22/0.51      ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | v2_struct_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u40,negated_conjecture,
% 0.22/0.51      ~v2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u68,axiom,
% 0.22/0.51      ~r2_hidden(X0,k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u54,axiom,
% 0.22/0.51      ~r2_hidden(X0,X1) | m1_subset_1(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u56,axiom,
% 0.22/0.51      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u43,axiom,
% 0.22/0.51      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u70,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK1(sK0,X0,X1),X0) | r1_lattice3(sK0,X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u71,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK2(sK0,X0,X1),X0) | r2_lattice3(sK0,X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u74,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK1(sK0,X0,X1),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u76,negated_conjecture,
% 0.22/0.51      ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u75,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) | sP3(X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u67,axiom,
% 0.22/0.51      ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | sP3(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u55,axiom,
% 0.22/0.51      ~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u65,axiom,
% 0.22/0.51      v1_xboole_0(k1_zfmisc_1(X0)) | r2_hidden(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u42,axiom,
% 0.22/0.51      v1_xboole_0(k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u58,axiom,
% 0.22/0.51      ~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP3(X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u62,negated_conjecture,
% 0.22/0.51      ~v1_xboole_0(u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  % (20341)# SZS output end Saturation.
% 0.22/0.51  % (20341)------------------------------
% 0.22/0.51  % (20341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20341)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (20341)Memory used [KB]: 5373
% 0.22/0.51  % (20341)Time elapsed: 0.076 s
% 0.22/0.51  % (20341)------------------------------
% 0.22/0.51  % (20341)------------------------------
% 0.22/0.51  % (20330)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.51  % (20327)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.51  % (20333)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.51  % (20320)Success in time 0.145 s
%------------------------------------------------------------------------------
