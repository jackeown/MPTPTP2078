%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:22 EST 2020

% Result     : CounterSatisfiable 1.72s
% Output     : Saturation 1.72s
% Verified   : 
% Statistics : Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   45 (  45 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u30,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u28,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u32,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u47,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u46,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u29,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u27,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u62,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u63,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u67,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
    | ~ v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
    | v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u43,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | ~ v1_funct_2(X2,X0,k1_xboole_0) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) != X0
    | v1_funct_2(X2,X0,X1) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) = X0
    | ~ v1_funct_2(X2,X0,X1) )).

cnf(u24,negated_conjecture,
    ( v1_funct_1(sK2) )).

% (32106)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
cnf(u31,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u73,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u33,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u60,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

cnf(u64,negated_conjecture,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:20:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (32126)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (32126)Refutation not found, incomplete strategy% (32126)------------------------------
% 0.22/0.46  % (32126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (32126)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (32126)Memory used [KB]: 10618
% 0.22/0.46  % (32126)Time elapsed: 0.003 s
% 0.22/0.46  % (32126)------------------------------
% 0.22/0.46  % (32126)------------------------------
% 0.22/0.47  % (32118)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (32118)Refutation not found, incomplete strategy% (32118)------------------------------
% 0.22/0.47  % (32118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (32118)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (32118)Memory used [KB]: 6012
% 0.22/0.47  % (32118)Time elapsed: 0.002 s
% 0.22/0.47  % (32118)------------------------------
% 0.22/0.47  % (32118)------------------------------
% 0.22/0.48  % (32109)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (32111)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (32113)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (32105)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (32105)Refutation not found, incomplete strategy% (32105)------------------------------
% 0.22/0.51  % (32105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (32105)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (32105)Memory used [KB]: 10618
% 0.22/0.51  % (32105)Time elapsed: 0.069 s
% 0.22/0.51  % (32105)------------------------------
% 0.22/0.51  % (32105)------------------------------
% 0.22/0.51  % (32120)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (32115)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (32113)Refutation not found, incomplete strategy% (32113)------------------------------
% 0.22/0.52  % (32113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32113)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (32113)Memory used [KB]: 10746
% 0.22/0.52  % (32113)Time elapsed: 0.069 s
% 0.22/0.52  % (32113)------------------------------
% 0.22/0.52  % (32113)------------------------------
% 0.22/0.53  % (32115)Refutation not found, incomplete strategy% (32115)------------------------------
% 0.22/0.53  % (32115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32115)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (32115)Memory used [KB]: 6396
% 0.22/0.53  % (32115)Time elapsed: 0.093 s
% 0.22/0.53  % (32115)------------------------------
% 0.22/0.53  % (32115)------------------------------
% 0.22/0.55  % (32116)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.57/0.56  % (32107)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.57/0.56  % (32104)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.57/0.56  % (32107)Refutation not found, incomplete strategy% (32107)------------------------------
% 1.57/0.56  % (32107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (32107)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (32107)Memory used [KB]: 10746
% 1.57/0.56  % (32107)Time elapsed: 0.128 s
% 1.57/0.56  % (32107)------------------------------
% 1.57/0.56  % (32107)------------------------------
% 1.57/0.56  % (32124)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.57/0.56  % (32112)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.57/0.57  % (32122)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.57/0.57  % (32108)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.57/0.57  % (32123)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.57/0.57  % (32108)Refutation not found, incomplete strategy% (32108)------------------------------
% 1.57/0.57  % (32108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (32108)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (32108)Memory used [KB]: 1663
% 1.57/0.57  % (32108)Time elapsed: 0.138 s
% 1.57/0.57  % (32108)------------------------------
% 1.57/0.57  % (32108)------------------------------
% 1.57/0.57  % (32116)Refutation not found, incomplete strategy% (32116)------------------------------
% 1.57/0.57  % (32116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (32116)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (32116)Memory used [KB]: 10618
% 1.57/0.57  % (32116)Time elapsed: 0.116 s
% 1.57/0.57  % (32116)------------------------------
% 1.57/0.57  % (32116)------------------------------
% 1.72/0.57  % (32124)Refutation not found, incomplete strategy% (32124)------------------------------
% 1.72/0.57  % (32124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.57  % (32125)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.72/0.57  % (32124)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.57  
% 1.72/0.57  % (32124)Memory used [KB]: 1663
% 1.72/0.57  % (32124)Time elapsed: 0.142 s
% 1.72/0.57  % (32124)------------------------------
% 1.72/0.57  % (32124)------------------------------
% 1.72/0.57  % (32104)Refutation not found, incomplete strategy% (32104)------------------------------
% 1.72/0.57  % (32104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.57  % (32104)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.57  
% 1.72/0.57  % (32104)Memory used [KB]: 6140
% 1.72/0.57  % (32104)Time elapsed: 0.139 s
% 1.72/0.57  % (32104)------------------------------
% 1.72/0.57  % (32104)------------------------------
% 1.72/0.58  % (32122)Refutation not found, incomplete strategy% (32122)------------------------------
% 1.72/0.58  % (32122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.58  % (32122)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.58  
% 1.72/0.58  % (32122)Memory used [KB]: 10874
% 1.72/0.58  % (32122)Time elapsed: 0.141 s
% 1.72/0.58  % (32122)------------------------------
% 1.72/0.58  % (32122)------------------------------
% 1.72/0.58  % (32125)Refutation not found, incomplete strategy% (32125)------------------------------
% 1.72/0.58  % (32125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.58  % (32125)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.58  
% 1.72/0.58  % (32125)Memory used [KB]: 6140
% 1.72/0.58  % (32125)Time elapsed: 0.142 s
% 1.72/0.58  % (32125)------------------------------
% 1.72/0.58  % (32125)------------------------------
% 1.72/0.58  % (32119)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.72/0.58  % (32110)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.72/0.58  % (32111)Refutation not found, incomplete strategy% (32111)------------------------------
% 1.72/0.58  % (32111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.58  % (32111)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.58  
% 1.72/0.58  % (32111)Memory used [KB]: 1663
% 1.72/0.58  % (32111)Time elapsed: 0.155 s
% 1.72/0.58  % (32111)------------------------------
% 1.72/0.58  % (32111)------------------------------
% 1.72/0.58  % SZS status CounterSatisfiable for theBenchmark
% 1.72/0.58  % (32123)# SZS output start Saturation.
% 1.72/0.58  cnf(u30,negated_conjecture,
% 1.72/0.58      l1_orders_2(sK0)).
% 1.72/0.58  
% 1.72/0.58  cnf(u28,negated_conjecture,
% 1.72/0.58      l1_orders_2(sK1)).
% 1.72/0.58  
% 1.72/0.58  cnf(u32,axiom,
% 1.72/0.58      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 1.72/0.58  
% 1.72/0.58  cnf(u47,negated_conjecture,
% 1.72/0.58      l1_struct_0(sK0)).
% 1.72/0.58  
% 1.72/0.58  cnf(u46,negated_conjecture,
% 1.72/0.58      l1_struct_0(sK1)).
% 1.72/0.58  
% 1.72/0.58  cnf(u29,negated_conjecture,
% 1.72/0.58      ~v2_struct_0(sK0)).
% 1.72/0.58  
% 1.72/0.58  cnf(u27,negated_conjecture,
% 1.72/0.58      ~v2_struct_0(sK1)).
% 1.72/0.58  
% 1.72/0.58  cnf(u62,negated_conjecture,
% 1.72/0.58      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 1.72/0.58  
% 1.72/0.58  cnf(u63,negated_conjecture,
% 1.72/0.58      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 1.72/0.58  
% 1.72/0.58  cnf(u67,negated_conjecture,
% 1.72/0.58      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 1.72/0.58  
% 1.72/0.58  cnf(u45,axiom,
% 1.72/0.58      ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)).
% 1.72/0.58  
% 1.72/0.58  cnf(u41,axiom,
% 1.72/0.58      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)).
% 1.72/0.58  
% 1.72/0.58  cnf(u42,axiom,
% 1.72/0.58      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)).
% 1.72/0.58  
% 1.72/0.58  cnf(u43,axiom,
% 1.72/0.58      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)).
% 1.72/0.58  
% 1.72/0.58  cnf(u34,axiom,
% 1.72/0.58      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)).
% 1.72/0.58  
% 1.72/0.58  cnf(u39,axiom,
% 1.72/0.58      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)).
% 1.72/0.58  
% 1.72/0.58  cnf(u40,axiom,
% 1.72/0.58      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)).
% 1.72/0.58  
% 1.72/0.58  cnf(u24,negated_conjecture,
% 1.72/0.58      v1_funct_1(sK2)).
% 1.72/0.58  
% 1.72/0.58  % (32106)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.72/0.58  cnf(u31,axiom,
% 1.72/0.58      v1_xboole_0(k1_xboole_0)).
% 1.72/0.58  
% 1.72/0.58  cnf(u73,negated_conjecture,
% 1.72/0.58      ~v1_xboole_0(k1_relat_1(sK2))).
% 1.72/0.58  
% 1.72/0.58  cnf(u33,axiom,
% 1.72/0.58      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 1.72/0.58  
% 1.72/0.58  cnf(u60,negated_conjecture,
% 1.72/0.58      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 1.72/0.58  
% 1.72/0.58  cnf(u64,negated_conjecture,
% 1.72/0.58      k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)).
% 1.72/0.58  
% 1.72/0.58  % (32123)# SZS output end Saturation.
% 1.72/0.58  % (32123)------------------------------
% 1.72/0.58  % (32123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.58  % (32123)Termination reason: Satisfiable
% 1.72/0.58  
% 1.72/0.58  % (32123)Memory used [KB]: 1663
% 1.72/0.58  % (32123)Time elapsed: 0.139 s
% 1.72/0.58  % (32123)------------------------------
% 1.72/0.58  % (32123)------------------------------
% 1.72/0.58  % (32101)Success in time 0.215 s
%------------------------------------------------------------------------------
