%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:22 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   37 (  37 expanded)
%              Number of leaves         :   37 (  37 expanded)
%              Depth                    :    0
%              Number of atoms          :   74 (  74 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u36,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u34,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u38,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u56,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u55,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u35,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u33,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u87,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u71,axiom,
    ( ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X1,X0))),X1,X0)
    | k1_xboole_0 = X0
    | k1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) = X1 )).

cnf(u65,axiom,
    ( ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))),X0,k1_xboole_0)
    | k1_xboole_0 = sK3(k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 )).

cnf(u62,axiom,
    ( ~ v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))),k1_xboole_0,X0)
    | k1_xboole_0 = k1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )).

cnf(u30,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u95,negated_conjecture,
    ( r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u57,axiom,
    ( r2_hidden(sK3(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u42,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) )).

cnf(u84,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u104,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u39,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u88,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u40,axiom,
    ( m1_subset_1(sK3(X0),X0) )).

cnf(u94,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u54,axiom,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) )).

cnf(u50,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
    | ~ v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u51,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
    | v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u52,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | ~ v1_funct_2(X2,X0,k1_xboole_0) )).

cnf(u43,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )).

cnf(u48,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) != X0
    | v1_funct_2(X2,X0,X1) )).

cnf(u49,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) = X0
    | ~ v1_funct_2(X2,X0,X1) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | r2_hidden(X0,X1) )).

cnf(u37,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u96,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))),sK2)
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u74,axiom,
    ( ~ r1_tarski(X0,sK3(X0))
    | v1_xboole_0(X0) )).

cnf(u85,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

cnf(u90,negated_conjecture,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

cnf(u59,axiom,
    ( k1_relset_1(X0,X1,sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )).

cnf(u68,axiom,
    ( k1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) != X1
    | k1_xboole_0 = X0
    | v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X1,X0))),X1,X0) )).

cnf(u64,axiom,
    ( k1_xboole_0 != k1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))
    | v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))),k1_xboole_0,X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:44:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (6737)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.43  % (6737)Refutation not found, incomplete strategy% (6737)------------------------------
% 0.21/0.43  % (6737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (6737)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.43  
% 0.21/0.43  % (6737)Memory used [KB]: 1663
% 0.21/0.43  % (6737)Time elapsed: 0.004 s
% 0.21/0.43  % (6737)------------------------------
% 0.21/0.43  % (6737)------------------------------
% 0.21/0.47  % (6726)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (6725)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (6729)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (6728)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (6721)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (6720)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (6734)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (6735)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (6731)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (6720)Refutation not found, incomplete strategy% (6720)------------------------------
% 0.21/0.50  % (6720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6720)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (6720)Memory used [KB]: 10618
% 0.21/0.50  % (6720)Time elapsed: 0.070 s
% 0.21/0.50  % (6720)------------------------------
% 0.21/0.50  % (6720)------------------------------
% 0.21/0.50  % (6721)Refutation not found, incomplete strategy% (6721)------------------------------
% 0.21/0.50  % (6721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6721)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (6721)Memory used [KB]: 10618
% 0.21/0.50  % (6721)Time elapsed: 0.083 s
% 0.21/0.50  % (6721)------------------------------
% 0.21/0.50  % (6721)------------------------------
% 0.21/0.50  % (6734)Refutation not found, incomplete strategy% (6734)------------------------------
% 0.21/0.50  % (6734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6734)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (6734)Memory used [KB]: 6140
% 0.21/0.50  % (6734)Time elapsed: 0.085 s
% 0.21/0.50  % (6734)------------------------------
% 0.21/0.50  % (6734)------------------------------
% 0.21/0.50  % (6731)Refutation not found, incomplete strategy% (6731)------------------------------
% 0.21/0.50  % (6731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6731)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (6731)Memory used [KB]: 6140
% 0.21/0.50  % (6731)Time elapsed: 0.085 s
% 0.21/0.50  % (6731)------------------------------
% 0.21/0.50  % (6731)------------------------------
% 0.21/0.50  % (6724)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (6730)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (6730)Refutation not found, incomplete strategy% (6730)------------------------------
% 0.21/0.50  % (6730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6730)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (6730)Memory used [KB]: 10618
% 0.21/0.50  % (6730)Time elapsed: 0.093 s
% 0.21/0.50  % (6730)------------------------------
% 0.21/0.50  % (6730)------------------------------
% 0.21/0.51  % (6736)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (6727)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (6733)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (6736)# SZS output start Saturation.
% 0.21/0.51  cnf(u36,negated_conjecture,
% 0.21/0.51      l1_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u34,negated_conjecture,
% 0.21/0.51      l1_orders_2(sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u38,axiom,
% 0.21/0.51      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u56,negated_conjecture,
% 0.21/0.51      l1_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u55,negated_conjecture,
% 0.21/0.51      l1_struct_0(sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u35,negated_conjecture,
% 0.21/0.51      ~v2_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u33,negated_conjecture,
% 0.21/0.51      ~v2_struct_0(sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u87,negated_conjecture,
% 0.21/0.51      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u71,axiom,
% 0.21/0.51      ~v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X1,X0))),X1,X0) | k1_xboole_0 = X0 | k1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) = X1).
% 0.21/0.51  
% 0.21/0.51  cnf(u65,axiom,
% 0.21/0.51      ~v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))),X0,k1_xboole_0) | k1_xboole_0 = sK3(k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u62,axiom,
% 0.21/0.51      ~v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))),k1_xboole_0,X0) | k1_xboole_0 = k1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))).
% 0.21/0.51  
% 0.21/0.51  cnf(u30,negated_conjecture,
% 0.21/0.51      v1_funct_1(sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u95,negated_conjecture,
% 0.21/0.51      r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.21/0.51  
% 0.21/0.51  cnf(u57,axiom,
% 0.21/0.51      r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u42,axiom,
% 0.21/0.51      ~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u84,axiom,
% 0.21/0.51      v1_xboole_0(k1_xboole_0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u104,negated_conjecture,
% 0.21/0.51      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u39,axiom,
% 0.21/0.51      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u88,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.21/0.51  
% 0.21/0.51  cnf(u40,axiom,
% 0.21/0.51      m1_subset_1(sK3(X0),X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u94,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u54,axiom,
% 0.21/0.51      ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u50,axiom,
% 0.21/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u51,axiom,
% 0.21/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u52,axiom,
% 0.21/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u43,axiom,
% 0.21/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u48,axiom,
% 0.21/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u49,axiom,
% 0.21/0.51      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u41,axiom,
% 0.21/0.51      ~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u37,axiom,
% 0.21/0.51      r1_tarski(k1_xboole_0,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u96,negated_conjecture,
% 0.21/0.51      ~r1_tarski(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))),sK2) | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.21/0.51  
% 0.21/0.51  cnf(u74,axiom,
% 0.21/0.51      ~r1_tarski(X0,sK3(X0)) | v1_xboole_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u85,negated_conjecture,
% 0.21/0.51      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u90,negated_conjecture,
% 0.21/0.51      k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u59,axiom,
% 0.21/0.51      k1_relset_1(X0,X1,sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) = k1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X0,X1))))).
% 0.21/0.51  
% 0.21/0.51  cnf(u68,axiom,
% 0.21/0.51      k1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) != X1 | k1_xboole_0 = X0 | v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(X1,X0))),X1,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u64,axiom,
% 0.21/0.51      k1_xboole_0 != k1_relat_1(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) | v1_funct_2(sK3(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))),k1_xboole_0,X0)).
% 0.21/0.51  
% 0.21/0.51  % (6736)# SZS output end Saturation.
% 0.21/0.51  % (6736)------------------------------
% 0.21/0.51  % (6736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6736)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (6736)Memory used [KB]: 1663
% 0.21/0.51  % (6736)Time elapsed: 0.094 s
% 0.21/0.51  % (6736)------------------------------
% 0.21/0.51  % (6736)------------------------------
% 0.21/0.51  % (6719)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (6722)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (6718)Success in time 0.145 s
%------------------------------------------------------------------------------
