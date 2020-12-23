%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:23 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   50 (  50 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u31,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u29,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u33,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u50,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u49,negated_conjecture,
    ( l1_struct_0(sK1) )).

cnf(u30,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u28,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u67,negated_conjecture,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) )).

cnf(u25,negated_conjecture,
    ( v1_funct_1(sK2) )).

cnf(u68,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) )).

cnf(u72,negated_conjecture,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2)) )).

cnf(u48,axiom,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) )).

cnf(u44,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
    | ~ v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
    | v1_funct_2(X2,k1_xboole_0,X1) )).

cnf(u46,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | ~ v1_funct_2(X2,X0,k1_xboole_0) )).

cnf(u37,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) != X0
    | v1_funct_2(X2,X0,X1) )).

cnf(u43,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_xboole_0 = X1
    | k1_relset_1(X0,X1,X2) = X0
    | ~ v1_funct_2(X2,X0,X1) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(X1) )).

cnf(u52,negated_conjecture,
    ( v1_relat_1(sK2) )).

cnf(u36,axiom,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) )).

cnf(u32,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u79,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(sK2)) )).

cnf(u35,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u69,negated_conjecture,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) )).

cnf(u65,negated_conjecture,
    ( u1_struct_0(sK0) = k1_relat_1(sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:33:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (15961)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.46  % (15949)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (15952)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (15949)Refutation not found, incomplete strategy% (15949)------------------------------
% 0.20/0.47  % (15949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (15956)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (15949)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (15949)Memory used [KB]: 10746
% 0.20/0.47  % (15949)Time elapsed: 0.051 s
% 0.20/0.47  % (15949)------------------------------
% 0.20/0.47  % (15949)------------------------------
% 0.20/0.47  % (15952)Refutation not found, incomplete strategy% (15952)------------------------------
% 0.20/0.47  % (15952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (15952)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (15952)Memory used [KB]: 10746
% 0.20/0.47  % (15952)Time elapsed: 0.009 s
% 0.20/0.47  % (15952)------------------------------
% 0.20/0.47  % (15952)------------------------------
% 0.20/0.48  % (15956)Refutation not found, incomplete strategy% (15956)------------------------------
% 0.20/0.48  % (15956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (15956)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (15956)Memory used [KB]: 6140
% 0.20/0.48  % (15956)Time elapsed: 0.071 s
% 0.20/0.48  % (15956)------------------------------
% 0.20/0.48  % (15956)------------------------------
% 0.20/0.48  % (15959)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (15959)Refutation not found, incomplete strategy% (15959)------------------------------
% 0.20/0.48  % (15959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (15959)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (15959)Memory used [KB]: 1663
% 0.20/0.48  % (15959)Time elapsed: 0.064 s
% 0.20/0.48  % (15959)------------------------------
% 0.20/0.48  % (15959)------------------------------
% 0.20/0.48  % (15951)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (15946)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (15948)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (15957)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (15946)Refutation not found, incomplete strategy% (15946)------------------------------
% 0.20/0.49  % (15946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15946)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15948)Refutation not found, incomplete strategy% (15948)------------------------------
% 0.20/0.49  % (15948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15948)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15948)Memory used [KB]: 10618
% 0.20/0.49  % (15948)Time elapsed: 0.068 s
% 0.20/0.49  % (15948)------------------------------
% 0.20/0.49  % (15948)------------------------------
% 0.20/0.49  % (15957)Refutation not found, incomplete strategy% (15957)------------------------------
% 0.20/0.49  % (15957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15957)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15957)Memory used [KB]: 10618
% 0.20/0.49  % (15957)Time elapsed: 0.092 s
% 0.20/0.49  % (15957)------------------------------
% 0.20/0.49  % (15957)------------------------------
% 0.20/0.49  % (15967)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (15950)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (15967)Refutation not found, incomplete strategy% (15967)------------------------------
% 0.20/0.49  % (15967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15967)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15967)Memory used [KB]: 10618
% 0.20/0.49  % (15967)Time elapsed: 0.090 s
% 0.20/0.49  % (15967)------------------------------
% 0.20/0.49  % (15967)------------------------------
% 0.20/0.49  % (15966)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % (15965)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  % (15966)Refutation not found, incomplete strategy% (15966)------------------------------
% 0.20/0.49  % (15966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15966)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15966)Memory used [KB]: 6140
% 0.20/0.49  % (15966)Time elapsed: 0.089 s
% 0.20/0.49  % (15966)------------------------------
% 0.20/0.49  % (15966)------------------------------
% 0.20/0.49  % (15955)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (15947)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (15965)Refutation not found, incomplete strategy% (15965)------------------------------
% 0.20/0.49  % (15965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15965)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15965)Memory used [KB]: 1663
% 0.20/0.49  % (15965)Time elapsed: 0.089 s
% 0.20/0.49  % (15965)------------------------------
% 0.20/0.49  % (15965)------------------------------
% 0.20/0.49  % (15947)Refutation not found, incomplete strategy% (15947)------------------------------
% 0.20/0.49  % (15947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15947)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15947)Memory used [KB]: 10618
% 0.20/0.49  % (15947)Time elapsed: 0.082 s
% 0.20/0.49  % (15947)------------------------------
% 0.20/0.49  % (15947)------------------------------
% 0.20/0.50  % (15962)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (15954)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.50  % (15955)Refutation not found, incomplete strategy% (15955)------------------------------
% 0.20/0.50  % (15955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (15955)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (15955)Memory used [KB]: 10746
% 0.20/0.50  % (15955)Time elapsed: 0.087 s
% 0.20/0.50  % (15955)------------------------------
% 0.20/0.50  % (15955)------------------------------
% 0.20/0.50  % (15962)Refutation not found, incomplete strategy% (15962)------------------------------
% 0.20/0.50  % (15962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (15962)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (15962)Memory used [KB]: 6140
% 0.20/0.50  % (15962)Time elapsed: 0.096 s
% 0.20/0.50  % (15962)------------------------------
% 0.20/0.50  % (15962)------------------------------
% 0.20/0.50  % (15953)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (15963)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (15946)Memory used [KB]: 6140
% 0.20/0.50  % (15946)Time elapsed: 0.075 s
% 0.20/0.50  % (15946)------------------------------
% 0.20/0.50  % (15946)------------------------------
% 0.20/0.50  % (15964)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (15958)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (15958)Refutation not found, incomplete strategy% (15958)------------------------------
% 0.20/0.50  % (15958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (15958)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (15958)Memory used [KB]: 6012
% 0.20/0.50  % (15958)Time elapsed: 0.002 s
% 0.20/0.50  % (15958)------------------------------
% 0.20/0.50  % (15958)------------------------------
% 0.20/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.50  % (15964)# SZS output start Saturation.
% 0.20/0.50  cnf(u31,negated_conjecture,
% 0.20/0.50      l1_orders_2(sK0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u29,negated_conjecture,
% 0.20/0.50      l1_orders_2(sK1)).
% 0.20/0.50  
% 0.20/0.50  cnf(u33,axiom,
% 0.20/0.50      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u50,negated_conjecture,
% 0.20/0.50      l1_struct_0(sK0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u49,negated_conjecture,
% 0.20/0.50      l1_struct_0(sK1)).
% 0.20/0.50  
% 0.20/0.50  cnf(u30,negated_conjecture,
% 0.20/0.50      ~v2_struct_0(sK0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u28,negated_conjecture,
% 0.20/0.50      ~v2_struct_0(sK1)).
% 0.20/0.50  
% 0.20/0.50  cnf(u67,negated_conjecture,
% 0.20/0.50      v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))).
% 0.20/0.50  
% 0.20/0.50  cnf(u25,negated_conjecture,
% 0.20/0.50      v1_funct_1(sK2)).
% 0.20/0.50  
% 0.20/0.50  cnf(u68,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))).
% 0.20/0.50  
% 0.20/0.50  cnf(u72,negated_conjecture,
% 0.20/0.50      ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2))).
% 0.20/0.50  
% 0.20/0.50  cnf(u48,axiom,
% 0.20/0.50      ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u44,axiom,
% 0.20/0.50      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)).
% 0.20/0.50  
% 0.20/0.50  cnf(u45,axiom,
% 0.20/0.50      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)).
% 0.20/0.50  
% 0.20/0.50  cnf(u46,axiom,
% 0.20/0.50      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u37,axiom,
% 0.20/0.50      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)).
% 0.20/0.50  
% 0.20/0.50  cnf(u42,axiom,
% 0.20/0.50      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)).
% 0.20/0.50  
% 0.20/0.50  cnf(u43,axiom,
% 0.20/0.50      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)).
% 0.20/0.50  
% 0.20/0.50  cnf(u34,axiom,
% 0.20/0.50      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)).
% 0.20/0.50  
% 0.20/0.50  cnf(u52,negated_conjecture,
% 0.20/0.50      v1_relat_1(sK2)).
% 0.20/0.50  
% 0.20/0.50  cnf(u36,axiom,
% 0.20/0.50      v1_relat_1(k2_zfmisc_1(X0,X1))).
% 0.20/0.50  
% 0.20/0.50  cnf(u32,axiom,
% 0.20/0.50      v1_xboole_0(k1_xboole_0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u79,negated_conjecture,
% 0.20/0.50      ~v1_xboole_0(k1_relat_1(sK2))).
% 0.20/0.50  
% 0.20/0.50  cnf(u35,axiom,
% 0.20/0.50      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u69,negated_conjecture,
% 0.20/0.50      k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)).
% 0.20/0.50  
% 0.20/0.50  cnf(u65,negated_conjecture,
% 0.20/0.50      u1_struct_0(sK0) = k1_relat_1(sK2)).
% 0.20/0.50  
% 0.20/0.50  % (15964)# SZS output end Saturation.
% 0.20/0.50  % (15964)------------------------------
% 0.20/0.50  % (15964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (15964)Termination reason: Satisfiable
% 0.20/0.50  
% 0.20/0.50  % (15964)Memory used [KB]: 1663
% 0.20/0.50  % (15964)Time elapsed: 0.098 s
% 0.20/0.50  % (15964)------------------------------
% 0.20/0.50  % (15964)------------------------------
% 0.20/0.50  % (15943)Success in time 0.151 s
%------------------------------------------------------------------------------
