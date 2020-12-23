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
% DateTime   : Thu Dec  3 13:16:52 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
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
    ( v1_waybel_0(sK2,sK0) )).

cnf(u24,negated_conjecture,
    ( ~ v1_waybel_0(sK2,sK1) )).

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
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:52:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (28594)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (28594)Refutation not found, incomplete strategy% (28594)------------------------------
% 0.21/0.48  % (28594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (28594)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (28594)Memory used [KB]: 1663
% 0.21/0.48  % (28594)Time elapsed: 0.053 s
% 0.21/0.48  % (28594)------------------------------
% 0.21/0.48  % (28594)------------------------------
% 0.21/0.48  % (28605)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (28597)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (28605)Refutation not found, incomplete strategy% (28605)------------------------------
% 0.21/0.48  % (28605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (28602)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (28602)Refutation not found, incomplete strategy% (28602)------------------------------
% 0.21/0.48  % (28602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (28602)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (28602)Memory used [KB]: 6012
% 0.21/0.48  % (28602)Time elapsed: 0.002 s
% 0.21/0.48  % (28602)------------------------------
% 0.21/0.48  % (28602)------------------------------
% 0.21/0.49  % (28591)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (28605)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (28605)Memory used [KB]: 6140
% 0.21/0.49  % (28605)Time elapsed: 0.007 s
% 0.21/0.49  % (28605)------------------------------
% 0.21/0.49  % (28605)------------------------------
% 0.21/0.49  % (28591)Refutation not found, incomplete strategy% (28591)------------------------------
% 0.21/0.49  % (28591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (28591)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (28591)Memory used [KB]: 10618
% 0.21/0.49  % (28591)Time elapsed: 0.071 s
% 0.21/0.49  % (28591)------------------------------
% 0.21/0.49  % (28591)------------------------------
% 0.21/0.50  % (28592)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (28592)Refutation not found, incomplete strategy% (28592)------------------------------
% 0.21/0.50  % (28592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28592)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (28592)Memory used [KB]: 10618
% 0.21/0.50  % (28592)Time elapsed: 0.084 s
% 0.21/0.50  % (28592)------------------------------
% 0.21/0.50  % (28592)------------------------------
% 0.21/0.50  % (28595)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (28600)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (28610)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (28610)Refutation not found, incomplete strategy% (28610)------------------------------
% 0.21/0.51  % (28610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28610)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (28610)Memory used [KB]: 10618
% 0.21/0.51  % (28610)Time elapsed: 0.095 s
% 0.21/0.51  % (28610)------------------------------
% 0.21/0.51  % (28610)------------------------------
% 0.21/0.51  % (28607)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (28608)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (28607)# SZS output start Saturation.
% 0.21/0.51  cnf(u12,negated_conjecture,
% 0.21/0.51      v1_waybel_0(sK2,sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u24,negated_conjecture,
% 0.21/0.51      ~v1_waybel_0(sK2,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u17,negated_conjecture,
% 0.21/0.51      l1_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u15,negated_conjecture,
% 0.21/0.51      l1_orders_2(sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u25,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u14,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u21,axiom,
% 0.21/0.51      ~m1_subset_1(X4,u1_struct_0(X1)) | ~l1_orders_2(X1) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r1_orders_2(X0,X4,X5) | r1_orders_2(X1,X4,X5)).
% 0.21/0.51  
% 0.21/0.51  cnf(u23,axiom,
% 0.21/0.51      ~m1_subset_1(X4,u1_struct_0(X1)) | ~l1_orders_2(X1) | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_orders_2(X0,X4,X5) | r2_orders_2(X1,X4,X5)).
% 0.21/0.51  
% 0.21/0.51  cnf(u16,negated_conjecture,
% 0.21/0.51      g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u11,negated_conjecture,
% 0.21/0.51      sK2 = sK3).
% 0.21/0.51  
% 0.21/0.51  % (28607)# SZS output end Saturation.
% 0.21/0.51  % (28607)------------------------------
% 0.21/0.51  % (28607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28607)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (28607)Memory used [KB]: 1663
% 0.21/0.51  % (28607)Time elapsed: 0.092 s
% 0.21/0.51  % (28607)------------------------------
% 0.21/0.51  % (28607)------------------------------
% 0.21/0.51  % (28590)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (28589)Success in time 0.148 s
%------------------------------------------------------------------------------
