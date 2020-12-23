%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:53 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  22 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    0
%              Number of atoms          :   47 (  47 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u94,negated_conjecture,(
    ! [X3,X2] :
      ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK0) = X2 ) )).

tff(u93,negated_conjecture,(
    ! [X1,X0] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_orders_2(sK0) = X1 ) )).

tff(u92,negated_conjecture,(
    ! [X3,X2] :
      ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      | u1_struct_0(sK1) = X2 ) )).

tff(u91,negated_conjecture,(
    ! [X1,X0] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      | u1_orders_2(sK1) = X1 ) )).

tff(u90,negated_conjecture,(
    u1_orders_2(sK0) = u1_orders_2(sK1) )).

tff(u89,negated_conjecture,(
    u1_struct_0(sK0) = u1_struct_0(sK1) )).

tff(u88,negated_conjecture,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) )).

tff(u87,negated_conjecture,(
    sK2 = sK3 )).

tff(u86,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) )).

tff(u85,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u84,negated_conjecture,(
    l1_orders_2(sK1) )).

tff(u83,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) )).

tff(u82,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) )).

tff(u81,negated_conjecture,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u80,negated_conjecture,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u79,negated_conjecture,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u78,negated_conjecture,(
    m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) )).

tff(u77,axiom,(
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

tff(u76,axiom,(
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

tff(u75,negated_conjecture,(
    ~ v2_waybel_0(sK3,sK1) )).

tff(u74,negated_conjecture,(
    ~ v2_waybel_0(sK2,sK1) )).

tff(u73,negated_conjecture,(
    v2_waybel_0(sK2,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (6083)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.46  % (6092)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.46  % (6083)# SZS output start Saturation.
% 0.20/0.46  tff(u94,negated_conjecture,
% 0.20/0.46      (![X3, X2] : (((g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_struct_0(sK0) = X2))))).
% 0.20/0.46  
% 0.20/0.46  tff(u93,negated_conjecture,
% 0.20/0.46      (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_orders_2(sK0) = X1))))).
% 0.20/0.46  
% 0.20/0.46  tff(u92,negated_conjecture,
% 0.20/0.46      (![X3, X2] : (((g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))) | (u1_struct_0(sK1) = X2))))).
% 0.20/0.46  
% 0.20/0.46  tff(u91,negated_conjecture,
% 0.20/0.46      (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))) | (u1_orders_2(sK1) = X1))))).
% 0.20/0.46  
% 0.20/0.46  tff(u90,negated_conjecture,
% 0.20/0.46      (u1_orders_2(sK0) = u1_orders_2(sK1))).
% 0.20/0.46  
% 0.20/0.46  tff(u89,negated_conjecture,
% 0.20/0.46      (u1_struct_0(sK0) = u1_struct_0(sK1))).
% 0.20/0.46  
% 0.20/0.46  tff(u88,negated_conjecture,
% 0.20/0.46      (g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)))).
% 0.20/0.46  
% 0.20/0.46  tff(u87,negated_conjecture,
% 0.20/0.46      (sK2 = sK3)).
% 0.20/0.46  
% 0.20/0.46  tff(u86,axiom,
% 0.20/0.46      (![X0] : ((~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))))).
% 0.20/0.46  
% 0.20/0.46  tff(u85,negated_conjecture,
% 0.20/0.46      l1_orders_2(sK0)).
% 0.20/0.46  
% 0.20/0.46  tff(u84,negated_conjecture,
% 0.20/0.46      l1_orders_2(sK1)).
% 0.20/0.46  
% 0.20/0.46  tff(u83,axiom,
% 0.20/0.46      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X1 = X3))))).
% 0.20/0.46  
% 0.20/0.46  tff(u82,axiom,
% 0.20/0.46      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X0 = X2))))).
% 0.20/0.46  
% 0.20/0.46  tff(u81,negated_conjecture,
% 0.20/0.46      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.46  
% 0.20/0.46  tff(u80,negated_conjecture,
% 0.20/0.46      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))).
% 0.20/0.46  
% 0.20/0.46  tff(u79,negated_conjecture,
% 0.20/0.46      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u78,negated_conjecture,
% 0.20/0.46      m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))).
% 0.20/0.46  
% 0.20/0.46  tff(u77,axiom,
% 0.20/0.46      (![X1, X5, X0, X4] : ((~r1_orders_2(X0,X4,X5) | r1_orders_2(X1,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u76,axiom,
% 0.20/0.46      (![X1, X5, X0, X4] : ((~r2_orders_2(X0,X4,X5) | r2_orders_2(X1,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u75,negated_conjecture,
% 0.20/0.46      ~v2_waybel_0(sK3,sK1)).
% 0.20/0.46  
% 0.20/0.46  tff(u74,negated_conjecture,
% 0.20/0.46      ~v2_waybel_0(sK2,sK1)).
% 0.20/0.46  
% 0.20/0.46  tff(u73,negated_conjecture,
% 0.20/0.46      v2_waybel_0(sK2,sK0)).
% 0.20/0.46  
% 0.20/0.46  % (6083)# SZS output end Saturation.
% 0.20/0.46  % (6083)------------------------------
% 0.20/0.46  % (6083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (6083)Termination reason: Satisfiable
% 0.20/0.46  
% 0.20/0.46  % (6083)Memory used [KB]: 10618
% 0.20/0.46  % (6083)Time elapsed: 0.046 s
% 0.20/0.46  % (6083)------------------------------
% 0.20/0.46  % (6083)------------------------------
% 0.20/0.46  % (6072)Success in time 0.108 s
%------------------------------------------------------------------------------
