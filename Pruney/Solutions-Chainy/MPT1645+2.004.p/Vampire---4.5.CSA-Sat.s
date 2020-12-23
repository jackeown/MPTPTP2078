%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:04 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   52 (  52 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u118,negated_conjecture,(
    ! [X3,X2] :
      ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK0) = X2 ) )).

tff(u117,negated_conjecture,(
    ! [X1,X0] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_orders_2(sK0) = X1 ) )).

tff(u116,negated_conjecture,(
    ! [X3,X2] :
      ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      | u1_struct_0(sK1) = X2 ) )).

tff(u115,negated_conjecture,(
    ! [X1,X0] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      | u1_orders_2(sK1) = X1 ) )).

tff(u114,negated_conjecture,(
    u1_orders_2(sK0) = u1_orders_2(sK1) )).

tff(u113,negated_conjecture,(
    u1_struct_0(sK0) = u1_struct_0(sK1) )).

tff(u112,negated_conjecture,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) )).

tff(u111,negated_conjecture,(
    sK2 = sK3 )).

tff(u110,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) )).

% (8330)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
tff(u109,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u108,negated_conjecture,(
    l1_orders_2(sK1) )).

tff(u107,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) )).

tff(u106,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) )).

tff(u105,negated_conjecture,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u104,negated_conjecture,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u103,negated_conjecture,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u102,negated_conjecture,(
    m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) )).

tff(u101,axiom,(
    ! [X1,X5,X0,X4] :
      ( ~ r1_orders_2(X0,X4,X5)
      | r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

tff(u100,axiom,(
    ! [X1,X5,X0,X4] :
      ( ~ r2_orders_2(X0,X4,X5)
      | r2_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

tff(u99,negated_conjecture,
    ( ~ ~ v12_waybel_0(sK3,sK1)
    | ~ v12_waybel_0(sK2,sK1) )).

tff(u98,negated_conjecture,
    ( ~ v12_waybel_0(sK2,sK0)
    | v12_waybel_0(sK2,sK0) )).

tff(u97,negated_conjecture,
    ( ~ ~ v13_waybel_0(sK2,sK0)
    | ~ v13_waybel_0(sK2,sK0) )).

tff(u96,negated_conjecture,
    ( ~ ~ v13_waybel_0(sK3,sK1)
    | ~ v13_waybel_0(sK2,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:48:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (8323)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (8317)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (8323)# SZS output start Saturation.
% 0.20/0.51  tff(u118,negated_conjecture,
% 0.20/0.51      (![X3, X2] : (((g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_struct_0(sK0) = X2))))).
% 0.20/0.51  
% 0.20/0.51  tff(u117,negated_conjecture,
% 0.20/0.51      (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_orders_2(sK0) = X1))))).
% 0.20/0.51  
% 0.20/0.51  tff(u116,negated_conjecture,
% 0.20/0.51      (![X3, X2] : (((g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))) | (u1_struct_0(sK1) = X2))))).
% 0.20/0.51  
% 0.20/0.51  tff(u115,negated_conjecture,
% 0.20/0.51      (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))) | (u1_orders_2(sK1) = X1))))).
% 0.20/0.51  
% 0.20/0.51  tff(u114,negated_conjecture,
% 0.20/0.51      (u1_orders_2(sK0) = u1_orders_2(sK1))).
% 0.20/0.51  
% 0.20/0.51  tff(u113,negated_conjecture,
% 0.20/0.51      (u1_struct_0(sK0) = u1_struct_0(sK1))).
% 0.20/0.51  
% 0.20/0.51  tff(u112,negated_conjecture,
% 0.20/0.51      (g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)))).
% 0.20/0.51  
% 0.20/0.51  tff(u111,negated_conjecture,
% 0.20/0.51      (sK2 = sK3)).
% 0.20/0.51  
% 0.20/0.51  tff(u110,axiom,
% 0.20/0.51      (![X0] : ((~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))))).
% 0.20/0.51  
% 0.20/0.51  % (8330)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  tff(u109,negated_conjecture,
% 0.20/0.51      l1_orders_2(sK0)).
% 0.20/0.51  
% 0.20/0.51  tff(u108,negated_conjecture,
% 0.20/0.51      l1_orders_2(sK1)).
% 0.20/0.51  
% 0.20/0.51  tff(u107,axiom,
% 0.20/0.51      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X1 = X3))))).
% 0.20/0.51  
% 0.20/0.51  tff(u106,axiom,
% 0.20/0.51      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X0 = X2))))).
% 0.20/0.51  
% 0.20/0.51  tff(u105,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  tff(u104,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))).
% 0.20/0.51  
% 0.20/0.51  tff(u103,negated_conjecture,
% 0.20/0.51      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u102,negated_conjecture,
% 0.20/0.51      m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))).
% 0.20/0.51  
% 0.20/0.51  tff(u101,axiom,
% 0.20/0.51      (![X1, X5, X0, X4] : ((~r1_orders_2(X0,X4,X5) | r1_orders_2(X1,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u100,axiom,
% 0.20/0.51      (![X1, X5, X0, X4] : ((~r2_orders_2(X0,X4,X5) | r2_orders_2(X1,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u99,negated_conjecture,
% 0.20/0.51      ((~~v12_waybel_0(sK3,sK1)) | ~v12_waybel_0(sK2,sK1))).
% 0.20/0.51  
% 0.20/0.51  tff(u98,negated_conjecture,
% 0.20/0.51      ((~v12_waybel_0(sK2,sK0)) | v12_waybel_0(sK2,sK0))).
% 0.20/0.51  
% 0.20/0.51  tff(u97,negated_conjecture,
% 0.20/0.51      ((~~v13_waybel_0(sK2,sK0)) | ~v13_waybel_0(sK2,sK0))).
% 0.20/0.51  
% 0.20/0.51  tff(u96,negated_conjecture,
% 0.20/0.51      ((~~v13_waybel_0(sK3,sK1)) | ~v13_waybel_0(sK2,sK1))).
% 0.20/0.51  
% 0.20/0.51  % (8323)# SZS output end Saturation.
% 0.20/0.51  % (8323)------------------------------
% 0.20/0.51  % (8323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8323)Termination reason: Satisfiable
% 0.20/0.51  
% 0.20/0.51  % (8323)Memory used [KB]: 10618
% 0.20/0.51  % (8323)Time elapsed: 0.082 s
% 0.20/0.51  % (8323)------------------------------
% 0.20/0.51  % (8323)------------------------------
% 1.22/0.52  % (8312)Success in time 0.153 s
%------------------------------------------------------------------------------
