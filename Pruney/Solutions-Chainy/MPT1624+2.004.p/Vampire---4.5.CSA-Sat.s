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
% DateTime   : Thu Dec  3 13:16:53 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    0
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u12,negated_conjecture,
    ( v2_waybel_0(sK2,sK0) )).

cnf(u24,negated_conjecture,
    ( ~ v2_waybel_0(sK2,sK1) )).

cnf(u17,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u15,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) )).

cnf(u14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u21,axiom,
    ( ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X5,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r1_orders_2(X0,X4,X5)
    | r1_orders_2(X1,X4,X5) )).

cnf(u23,axiom,
    ( ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ m1_subset_1(X5,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r2_orders_2(X0,X4,X5)
    | r2_orders_2(X1,X4,X5) )).

cnf(u16,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) )).

cnf(u11,negated_conjecture,
    ( sK2 = sK3 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:55:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (1914)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.44  % (1914)Refutation not found, incomplete strategy% (1914)------------------------------
% 0.22/0.44  % (1914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (1914)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.44  
% 0.22/0.44  % (1914)Memory used [KB]: 1663
% 0.22/0.44  % (1914)Time elapsed: 0.003 s
% 0.22/0.44  % (1914)------------------------------
% 0.22/0.44  % (1914)------------------------------
% 0.22/0.48  % (1906)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (1903)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (1921)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (1915)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (1908)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (1921)Refutation not found, incomplete strategy% (1921)------------------------------
% 0.22/0.49  % (1921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (1921)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (1921)Memory used [KB]: 6140
% 0.22/0.49  % (1921)Time elapsed: 0.082 s
% 0.22/0.49  % (1921)------------------------------
% 0.22/0.49  % (1921)------------------------------
% 0.22/0.49  % (1908)Refutation not found, incomplete strategy% (1908)------------------------------
% 0.22/0.49  % (1908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (1908)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (1908)Memory used [KB]: 10618
% 0.22/0.49  % (1908)Time elapsed: 0.061 s
% 0.22/0.49  % (1908)------------------------------
% 0.22/0.49  % (1908)------------------------------
% 0.22/0.50  % (1918)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (1902)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (1922)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (1922)Refutation not found, incomplete strategy% (1922)------------------------------
% 0.22/0.50  % (1922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (1922)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (1922)Memory used [KB]: 10618
% 0.22/0.50  % (1922)Time elapsed: 0.090 s
% 0.22/0.50  % (1922)------------------------------
% 0.22/0.50  % (1922)------------------------------
% 0.22/0.50  % (1917)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (1911)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (1917)Refutation not found, incomplete strategy% (1917)------------------------------
% 0.22/0.50  % (1917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (1917)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.51  % (1917)Memory used [KB]: 6140
% 0.22/0.51  % (1917)Time elapsed: 0.084 s
% 0.22/0.51  % (1917)------------------------------
% 0.22/0.51  % (1917)------------------------------
% 0.22/0.51  % (1918)Refutation not found, incomplete strategy% (1918)------------------------------
% 0.22/0.51  % (1918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1918)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (1918)Memory used [KB]: 10618
% 0.22/0.51  % (1918)Time elapsed: 0.066 s
% 0.22/0.51  % (1918)------------------------------
% 0.22/0.51  % (1918)------------------------------
% 0.22/0.51  % (1898)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (1898)Refutation not found, incomplete strategy% (1898)------------------------------
% 0.22/0.51  % (1898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1898)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (1898)Memory used [KB]: 6140
% 0.22/0.51  % (1898)Time elapsed: 0.082 s
% 0.22/0.51  % (1898)------------------------------
% 0.22/0.51  % (1898)------------------------------
% 0.22/0.51  % (1901)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (1900)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (1905)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (1901)Refutation not found, incomplete strategy% (1901)------------------------------
% 0.22/0.51  % (1901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1901)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (1901)Memory used [KB]: 10618
% 0.22/0.51  % (1901)Time elapsed: 0.090 s
% 0.22/0.51  % (1901)------------------------------
% 0.22/0.51  % (1901)------------------------------
% 0.22/0.51  % (1900)Refutation not found, incomplete strategy% (1900)------------------------------
% 0.22/0.51  % (1900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1900)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (1900)Memory used [KB]: 10618
% 0.22/0.51  % (1900)Time elapsed: 0.093 s
% 0.22/0.51  % (1900)------------------------------
% 0.22/0.51  % (1900)------------------------------
% 0.22/0.51  % (1902)Refutation not found, incomplete strategy% (1902)------------------------------
% 0.22/0.51  % (1902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1902)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (1902)Memory used [KB]: 1663
% 0.22/0.51  % (1902)Time elapsed: 0.095 s
% 0.22/0.51  % (1902)------------------------------
% 0.22/0.51  % (1902)------------------------------
% 0.22/0.52  % (1920)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.52  % (1912)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (1912)Refutation not found, incomplete strategy% (1912)------------------------------
% 0.22/0.52  % (1912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1912)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1912)Memory used [KB]: 6012
% 0.22/0.52  % (1912)Time elapsed: 0.002 s
% 0.22/0.52  % (1912)------------------------------
% 0.22/0.52  % (1912)------------------------------
% 0.22/0.52  % (1904)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  % (1910)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (1899)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (1920)Refutation not found, incomplete strategy% (1920)------------------------------
% 0.22/0.52  % (1920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1920)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1920)Memory used [KB]: 1663
% 0.22/0.52  % (1920)Time elapsed: 0.095 s
% 0.22/0.52  % (1920)------------------------------
% 0.22/0.52  % (1920)------------------------------
% 0.22/0.52  % (1910)Refutation not found, incomplete strategy% (1910)------------------------------
% 0.22/0.52  % (1910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1910)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1910)Memory used [KB]: 6012
% 0.22/0.52  % (1910)Time elapsed: 0.092 s
% 0.22/0.52  % (1910)------------------------------
% 0.22/0.52  % (1910)------------------------------
% 0.22/0.52  % (1904)Refutation not found, incomplete strategy% (1904)------------------------------
% 0.22/0.52  % (1904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1904)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1904)Memory used [KB]: 10618
% 0.22/0.52  % (1904)Time elapsed: 0.084 s
% 0.22/0.52  % (1904)------------------------------
% 0.22/0.52  % (1904)------------------------------
% 0.22/0.52  % (1911)Refutation not found, incomplete strategy% (1911)------------------------------
% 0.22/0.52  % (1911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1911)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1911)Memory used [KB]: 10618
% 0.22/0.52  % (1911)Time elapsed: 0.095 s
% 0.22/0.52  % (1911)------------------------------
% 0.22/0.52  % (1911)------------------------------
% 0.22/0.52  % (1899)Refutation not found, incomplete strategy% (1899)------------------------------
% 0.22/0.52  % (1899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1899)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1899)Memory used [KB]: 10618
% 0.22/0.52  % (1899)Time elapsed: 0.090 s
% 0.22/0.52  % (1899)------------------------------
% 0.22/0.52  % (1899)------------------------------
% 0.22/0.52  % (1919)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (1919)# SZS output start Saturation.
% 0.22/0.52  cnf(u12,negated_conjecture,
% 0.22/0.52      v2_waybel_0(sK2,sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u24,negated_conjecture,
% 0.22/0.52      ~v2_waybel_0(sK2,sK1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u17,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u15,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u25,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))).
% 0.22/0.52  
% 0.22/0.52  cnf(u14,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  cnf(u21,axiom,
% 0.22/0.52      ~m1_subset_1(X4,u1_struct_0(X1)) | ~l1_orders_2(X1) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r1_orders_2(X0,X4,X5) | r1_orders_2(X1,X4,X5)).
% 0.22/0.52  
% 0.22/0.52  cnf(u23,axiom,
% 0.22/0.52      ~m1_subset_1(X4,u1_struct_0(X1)) | ~l1_orders_2(X1) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_orders_2(X0,X4,X5) | r2_orders_2(X1,X4,X5)).
% 0.22/0.52  
% 0.22/0.52  cnf(u16,negated_conjecture,
% 0.22/0.52      g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))).
% 0.22/0.52  
% 0.22/0.52  cnf(u11,negated_conjecture,
% 0.22/0.52      sK2 = sK3).
% 0.22/0.52  
% 0.22/0.52  % (1919)# SZS output end Saturation.
% 0.22/0.52  % (1919)------------------------------
% 0.22/0.52  % (1919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1919)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (1919)Memory used [KB]: 1663
% 0.22/0.52  % (1919)Time elapsed: 0.090 s
% 0.22/0.52  % (1919)------------------------------
% 0.22/0.52  % (1919)------------------------------
% 0.22/0.52  % (1897)Success in time 0.155 s
%------------------------------------------------------------------------------
