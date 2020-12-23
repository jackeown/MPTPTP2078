%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:20 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   65 (  65 expanded)
%              Number of leaves         :   65 (  65 expanded)
%              Depth                    :    0
%              Number of atoms          :  151 ( 151 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u56,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u54,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u63,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u93,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u92,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u55,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u53,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u89,axiom,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) )).

cnf(u61,axiom,
    ( v1_partfun1(k6_partfun1(X0),X0) )).

cnf(u75,axiom,
    ( ~ v1_partfun1(X1,X0)
    | ~ v4_relat_1(X1,X0)
    | k1_relat_1(X1) = X0
    | ~ v1_relat_1(X1) )).

cnf(u51,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) )).

cnf(u49,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) )).

cnf(u119,axiom,
    ( v4_relat_1(k6_partfun1(k1_xboole_0),X1) )).

cnf(u115,axiom,
    ( v4_relat_1(k6_partfun1(X2),X2) )).

cnf(u114,negated_conjecture,
    ( v4_relat_1(sK2,u1_struct_0(sK0)) )).

cnf(u50,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u67,axiom,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )).

cnf(u68,axiom,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) )).

cnf(u69,axiom,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )).

cnf(u70,axiom,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )).

cnf(u73,axiom,
    ( ~ v1_funct_1(X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_xboole_0(X2) )).

cnf(u87,axiom,
    ( v2_funct_1(k6_partfun1(X0)) )).

cnf(u126,negated_conjecture,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) )).

cnf(u128,negated_conjecture,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) )).

cnf(u136,negated_conjecture,
    ( ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) )).

cnf(u140,negated_conjecture,
    ( ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) )).

cnf(u100,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u88,axiom,
    ( v1_relat_1(k6_partfun1(X0)) )).

cnf(u99,axiom,
    ( v1_relat_1(o_1_1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))
    | ~ v1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )).

cnf(u104,axiom,
    ( v1_relat_1(o_1_1_relat_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ v1_relat_1(k1_zfmisc_1(k1_xboole_0)) )).

cnf(u71,axiom,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) )).

cnf(u94,axiom,
    ( v1_relat_1(k1_xboole_0) )).

cnf(u113,axiom,
    ( ~ v1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v4_relat_1(o_1_1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0) )).

cnf(u120,axiom,
    ( ~ v1_relat_1(k1_zfmisc_1(k6_partfun1(k1_xboole_0)))
    | v1_xboole_0(o_1_1_relat_1(k1_zfmisc_1(k6_partfun1(k1_xboole_0)))) )).

cnf(u110,axiom,
    ( ~ v1_relat_1(k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(o_1_1_relat_1(k1_zfmisc_1(k1_xboole_0))) )).

cnf(u118,axiom,
    ( ~ v1_relat_1(k1_zfmisc_1(k1_xboole_0))
    | v4_relat_1(o_1_1_relat_1(k1_zfmisc_1(k1_xboole_0)),X0) )).

cnf(u72,axiom,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X0,X1) )).

cnf(u79,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) )).

cnf(u96,axiom,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) )).

cnf(u62,axiom,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )).

cnf(u52,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) )).

cnf(u64,axiom,
    ( m1_subset_1(o_1_1_relat_1(X0),X0)
    | ~ v1_relat_1(X0) )).

cnf(u106,axiom,
    ( ~ m1_subset_1(X0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

cnf(u112,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k6_partfun1(k1_xboole_0)))
    | v1_xboole_0(X0) )).

cnf(u102,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | v1_relat_1(X1) )).

cnf(u109,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(X0) )).

cnf(u116,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | v4_relat_1(X1,X0) )).

cnf(u80,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(X2) )).

cnf(u81,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v4_relat_1(X2,X0) )).

cnf(u111,axiom,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0)) )).

cnf(u108,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u141,negated_conjecture,
    ( ~ v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v1_xboole_0(X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | v1_xboole_0(X0) )).

cnf(u65,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | v1_xboole_0(X1) )).

cnf(u66,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u57,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u98,axiom,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u133,axiom,
    ( k1_relat_1(k6_partfun1(X0)) = X0 )).

cnf(u91,axiom,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) )).

cnf(u90,axiom,
    ( k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) )).

cnf(u82,axiom,
    ( k2_relset_1(X0,X1,X2) != X1
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | v1_funct_1(k2_funct_1(X2)) )).

cnf(u83,axiom,
    ( k2_relset_1(X0,X1,X2) != X1
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | v1_funct_2(k2_funct_1(X2),X1,X0) )).

cnf(u84,axiom,
    ( k2_relset_1(X0,X1,X2) != X1
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )).

cnf(u85,axiom,
    ( k2_relset_1(X0,X1,X2) != X1
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X2)
    | k1_xboole_0 = X1
    | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )).

cnf(u86,axiom,
    ( k2_relset_1(X0,X1,X2) != X1
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X2)
    | k1_xboole_0 = X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) )).

cnf(u76,axiom,
    ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (15128)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (15136)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (15128)Refutation not found, incomplete strategy% (15128)------------------------------
% 0.21/0.52  % (15128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15136)Refutation not found, incomplete strategy% (15136)------------------------------
% 0.21/0.52  % (15136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15128)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15128)Memory used [KB]: 6268
% 0.21/0.52  % (15128)Time elapsed: 0.099 s
% 0.21/0.52  % (15128)------------------------------
% 0.21/0.52  % (15128)------------------------------
% 0.21/0.53  % (15136)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15136)Memory used [KB]: 6268
% 0.21/0.53  % (15136)Time elapsed: 0.106 s
% 0.21/0.53  % (15136)------------------------------
% 0.21/0.53  % (15136)------------------------------
% 0.21/0.53  % (15144)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (15129)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (15144)Refutation not found, incomplete strategy% (15144)------------------------------
% 0.21/0.53  % (15144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15144)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15144)Memory used [KB]: 10874
% 0.21/0.53  % (15144)Time elapsed: 0.110 s
% 0.21/0.53  % (15144)------------------------------
% 0.21/0.53  % (15144)------------------------------
% 0.21/0.54  % (15129)Refutation not found, incomplete strategy% (15129)------------------------------
% 0.21/0.54  % (15129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15129)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15129)Memory used [KB]: 6268
% 0.21/0.54  % (15129)Time elapsed: 0.125 s
% 0.21/0.54  % (15129)------------------------------
% 0.21/0.54  % (15129)------------------------------
% 0.21/0.54  % (15130)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (15124)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (15134)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (15124)Refutation not found, incomplete strategy% (15124)------------------------------
% 0.21/0.54  % (15124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15124)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15124)Memory used [KB]: 1791
% 0.21/0.54  % (15124)Time elapsed: 0.122 s
% 0.21/0.54  % (15124)------------------------------
% 0.21/0.54  % (15124)------------------------------
% 0.21/0.54  % (15126)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (15137)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (15130)# SZS output start Saturation.
% 0.21/0.54  cnf(u56,negated_conjecture,
% 0.21/0.54      l1_orders_2(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u54,negated_conjecture,
% 0.21/0.54      l1_orders_2(sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u63,axiom,
% 0.21/0.54      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u93,negated_conjecture,
% 0.21/0.54      l1_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u92,negated_conjecture,
% 0.21/0.54      l1_struct_0(sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u55,negated_conjecture,
% 0.21/0.54      ~v2_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u53,negated_conjecture,
% 0.21/0.54      ~v2_struct_0(sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u89,axiom,
% 0.21/0.54      v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u61,axiom,
% 0.21/0.54      v1_partfun1(k6_partfun1(X0),X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u75,axiom,
% 0.21/0.54      ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u51,negated_conjecture,
% 0.21/0.54      v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))).
% 0.21/0.54  
% 0.21/0.54  cnf(u49,negated_conjecture,
% 0.21/0.54      ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))).
% 0.21/0.54  
% 0.21/0.54  cnf(u119,axiom,
% 0.21/0.54      v4_relat_1(k6_partfun1(k1_xboole_0),X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u115,axiom,
% 0.21/0.54      v4_relat_1(k6_partfun1(X2),X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u114,negated_conjecture,
% 0.21/0.54      v4_relat_1(sK2,u1_struct_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u50,negated_conjecture,
% 0.21/0.54      v1_funct_1(sK2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u67,axiom,
% 0.21/0.54      ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u68,axiom,
% 0.21/0.54      ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u69,axiom,
% 0.21/0.54      ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u70,axiom,
% 0.21/0.54      ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u73,axiom,
% 0.21/0.54      ~v1_funct_1(X2) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~v1_xboole_0(X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u87,axiom,
% 0.21/0.54      v2_funct_1(k6_partfun1(X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u126,negated_conjecture,
% 0.21/0.54      ~v2_funct_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))).
% 0.21/0.54  
% 0.21/0.54  cnf(u128,negated_conjecture,
% 0.21/0.54      ~v2_funct_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u136,negated_conjecture,
% 0.21/0.54      ~v2_funct_1(sK2) | k1_relat_1(sK2) = k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u140,negated_conjecture,
% 0.21/0.54      ~v2_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u100,negated_conjecture,
% 0.21/0.54      v1_relat_1(sK2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u88,axiom,
% 0.21/0.54      v1_relat_1(k6_partfun1(X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u99,axiom,
% 0.21/0.54      v1_relat_1(o_1_1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u104,axiom,
% 0.21/0.54      v1_relat_1(o_1_1_relat_1(k1_zfmisc_1(k1_xboole_0))) | ~v1_relat_1(k1_zfmisc_1(k1_xboole_0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u71,axiom,
% 0.21/0.54      v1_relat_1(k2_zfmisc_1(X0,X1))).
% 0.21/0.54  
% 0.21/0.54  cnf(u94,axiom,
% 0.21/0.54      v1_relat_1(k1_xboole_0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u113,axiom,
% 0.21/0.54      ~v1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(o_1_1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u120,axiom,
% 0.21/0.54      ~v1_relat_1(k1_zfmisc_1(k6_partfun1(k1_xboole_0))) | v1_xboole_0(o_1_1_relat_1(k1_zfmisc_1(k6_partfun1(k1_xboole_0))))).
% 0.21/0.54  
% 0.21/0.54  cnf(u110,axiom,
% 0.21/0.54      ~v1_relat_1(k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(o_1_1_relat_1(k1_zfmisc_1(k1_xboole_0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u118,axiom,
% 0.21/0.54      ~v1_relat_1(k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(o_1_1_relat_1(k1_zfmisc_1(k1_xboole_0)),X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u72,axiom,
% 0.21/0.54      r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u79,axiom,
% 0.21/0.54      ~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u96,axiom,
% 0.21/0.54      m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u62,axiom,
% 0.21/0.54      m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u52,negated_conjecture,
% 0.21/0.54      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))).
% 0.21/0.54  
% 0.21/0.54  cnf(u64,axiom,
% 0.21/0.54      m1_subset_1(o_1_1_relat_1(X0),X0) | ~v1_relat_1(X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u106,axiom,
% 0.21/0.54      ~m1_subset_1(X0,k1_xboole_0) | v1_xboole_0(k1_xboole_0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u112,axiom,
% 0.21/0.54      ~m1_subset_1(X0,k1_zfmisc_1(k6_partfun1(k1_xboole_0))) | v1_xboole_0(X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u102,axiom,
% 0.21/0.54      ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_relat_1(X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u109,axiom,
% 0.21/0.54      ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u116,axiom,
% 0.21/0.54      ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u80,axiom,
% 0.21/0.54      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u81,axiom,
% 0.21/0.54      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u111,axiom,
% 0.21/0.54      v1_xboole_0(k6_partfun1(k1_xboole_0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u108,axiom,
% 0.21/0.54      v1_xboole_0(k1_xboole_0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u141,negated_conjecture,
% 0.21/0.54      ~v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X1,X0) | v1_xboole_0(X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u65,axiom,
% 0.21/0.54      ~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u66,axiom,
% 0.21/0.54      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u57,axiom,
% 0.21/0.54      r1_tarski(k1_xboole_0,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u98,axiom,
% 0.21/0.54      ~r1_tarski(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u133,axiom,
% 0.21/0.54      k1_relat_1(k6_partfun1(X0)) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u91,axiom,
% 0.21/0.54      k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u90,axiom,
% 0.21/0.54      k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u82,axiom,
% 0.21/0.54      k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_1(k2_funct_1(X2))).
% 0.21/0.54  
% 0.21/0.54  cnf(u83,axiom,
% 0.21/0.54      k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_2(k2_funct_1(X2),X1,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u84,axiom,
% 0.21/0.54      k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u85,axiom,
% 0.21/0.54      k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))).
% 0.21/0.54  
% 0.21/0.54  cnf(u86,axiom,
% 0.21/0.54      k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u76,axiom,
% 0.21/0.54      k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0).
% 0.21/0.54  
% 0.21/0.54  % (15130)# SZS output end Saturation.
% 0.21/0.54  % (15130)------------------------------
% 0.21/0.54  % (15130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15130)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (15130)Memory used [KB]: 6268
% 0.21/0.54  % (15130)Time elapsed: 0.122 s
% 0.21/0.54  % (15130)------------------------------
% 0.21/0.54  % (15130)------------------------------
% 0.21/0.54  % (15134)Refutation not found, incomplete strategy% (15134)------------------------------
% 0.21/0.54  % (15134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15134)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15134)Memory used [KB]: 10746
% 0.21/0.54  % (15134)Time elapsed: 0.122 s
% 0.21/0.54  % (15134)------------------------------
% 0.21/0.54  % (15134)------------------------------
% 0.21/0.54  % (15123)Success in time 0.177 s
%------------------------------------------------------------------------------
