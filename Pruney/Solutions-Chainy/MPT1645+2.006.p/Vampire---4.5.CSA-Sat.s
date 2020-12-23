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
% DateTime   : Thu Dec  3 13:17:05 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    0
%              Number of atoms          :  110 ( 110 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u182,axiom,(
    ! [X1,X3,X0,X2] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) )).

tff(u181,axiom,(
    ! [X1,X3,X0,X2] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) )).

tff(u180,axiom,(
    ! [X1,X5,X0,X4] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X1,X4,X5)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

tff(u179,axiom,(
    ! [X1,X5,X0,X4] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r2_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_orders_2(X1,X4,X5)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

% (8647)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
tff(u178,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | u1_struct_0(sK1) != u1_struct_0(sK2)
    | ! [X1,X0,X2] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK2,X1,X2)
        | ~ l1_orders_2(X0) ) )).

tff(u177,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | u1_struct_0(sK1) != u1_struct_0(sK2)
    | ! [X1,X0,X2] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        | ~ r1_orders_2(sK2,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_orders_2(X0,X1,X2)
        | ~ l1_orders_2(X0) ) )).

tff(u176,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | u1_struct_0(sK1) != u1_struct_0(sK2)
    | ! [X1,X0,X2] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        | ~ r2_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r2_orders_2(sK2,X1,X2)
        | ~ l1_orders_2(X0) ) )).

tff(u175,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | u1_struct_0(sK1) != u1_struct_0(sK2)
    | ! [X1,X0,X2] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
        | ~ r2_orders_2(sK2,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_orders_2(X0,X1,X2)
        | ~ l1_orders_2(X0) ) )).

tff(u174,negated_conjecture,(
    sK3 = sK4 )).

tff(u173,negated_conjecture,
    ( u1_struct_0(sK1) != u1_struct_0(sK2)
    | u1_struct_0(sK1) = u1_struct_0(sK2) )).

tff(u172,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | u1_orders_2(sK1) = u1_orders_2(sK2) )).

tff(u171,negated_conjecture,(
    l1_orders_2(sK1) )).

tff(u170,negated_conjecture,(
    l1_orders_2(sK2) )).

tff(u169,negated_conjecture,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u168,axiom,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) )).

tff(u167,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) )).

tff(u166,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | u1_struct_0(sK1) != u1_struct_0(sK2)
    | ! [X1,X0] :
        ( ~ r1_orders_2(sK2,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK1,X0,X1) ) )).

tff(u165,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | u1_struct_0(sK1) != u1_struct_0(sK2)
    | ! [X1,X0] :
        ( ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK2,X0,X1) ) )).

tff(u164,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | u1_struct_0(sK1) != u1_struct_0(sK2)
    | ! [X1,X0] :
        ( ~ r2_orders_2(sK2,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_orders_2(sK1,X0,X1) ) )).

tff(u163,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | u1_struct_0(sK1) != u1_struct_0(sK2)
    | ! [X1,X0] :
        ( ~ r2_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_orders_2(sK2,X0,X1) ) )).

tff(u162,negated_conjecture,
    ( ~ sP0(sK2,sK3,sK1,sK3)
    | ~ v12_waybel_0(sK3,sK2) )).

tff(u161,negated_conjecture,
    ( ~ sP0(sK2,sK3,sK1,sK3)
    | v12_waybel_0(sK3,sK1) )).

tff(u160,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(X0,X1,X2,X3)
      | ~ v12_waybel_0(X1,X0) ) )).

tff(u159,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(X0,X1,X2,X3)
      | v12_waybel_0(X3,X2) ) )).

tff(u158,negated_conjecture,
    ( ~ sP0(sK2,sK3,sK1,sK3)
    | sP0(sK2,sK3,sK1,sK3) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (8644)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.45  % (8644)Refutation not found, incomplete strategy% (8644)------------------------------
% 0.21/0.45  % (8644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (8652)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.46  % (8644)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (8644)Memory used [KB]: 10618
% 0.21/0.46  % (8644)Time elapsed: 0.059 s
% 0.21/0.46  % (8644)------------------------------
% 0.21/0.46  % (8644)------------------------------
% 0.21/0.47  % (8662)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.48  % (8654)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.48  % (8654)Refutation not found, incomplete strategy% (8654)------------------------------
% 0.21/0.48  % (8654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8654)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (8654)Memory used [KB]: 10490
% 0.21/0.48  % (8654)Time elapsed: 0.085 s
% 0.21/0.48  % (8654)------------------------------
% 0.21/0.48  % (8654)------------------------------
% 0.21/0.48  % (8662)Refutation not found, incomplete strategy% (8662)------------------------------
% 0.21/0.48  % (8662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8662)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (8662)Memory used [KB]: 1663
% 0.21/0.48  % (8662)Time elapsed: 0.075 s
% 0.21/0.48  % (8662)------------------------------
% 0.21/0.48  % (8662)------------------------------
% 0.21/0.48  % (8668)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (8668)# SZS output start Saturation.
% 0.21/0.49  tff(u182,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : (((g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X1 = X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))))).
% 0.21/0.49  
% 0.21/0.49  tff(u181,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : (((g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X0 = X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))))).
% 0.21/0.49  
% 0.21/0.49  tff(u180,axiom,
% 0.21/0.49      (![X1, X5, X0, X4] : (((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) | ~r1_orders_2(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X1,X4,X5) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u179,axiom,
% 0.21/0.49      (![X1, X5, X0, X4] : (((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) | ~r2_orders_2(X0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | r2_orders_2(X1,X4,X5) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  % (8647)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  tff(u178,negated_conjecture,
% 0.21/0.49      ((~m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))) | (~(u1_struct_0(sK1) = u1_struct_0(sK2))) | (![X1, X0, X2] : (((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(sK2,X1,X2) | ~l1_orders_2(X0)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u177,negated_conjecture,
% 0.21/0.49      ((~m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))) | (~(u1_struct_0(sK1) = u1_struct_0(sK2))) | (![X1, X0, X2] : (((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))) | ~r1_orders_2(sK2,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u176,negated_conjecture,
% 0.21/0.49      ((~m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))) | (~(u1_struct_0(sK1) = u1_struct_0(sK2))) | (![X1, X0, X2] : (((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_orders_2(sK2,X1,X2) | ~l1_orders_2(X0)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u175,negated_conjecture,
% 0.21/0.49      ((~m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))) | (~(u1_struct_0(sK1) = u1_struct_0(sK2))) | (![X1, X0, X2] : (((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))) | ~r2_orders_2(sK2,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | r2_orders_2(X0,X1,X2) | ~l1_orders_2(X0)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u174,negated_conjecture,
% 0.21/0.49      (sK3 = sK4)).
% 0.21/0.49  
% 0.21/0.49  tff(u173,negated_conjecture,
% 0.21/0.49      ((~(u1_struct_0(sK1) = u1_struct_0(sK2))) | (u1_struct_0(sK1) = u1_struct_0(sK2)))).
% 0.21/0.49  
% 0.21/0.49  tff(u172,negated_conjecture,
% 0.21/0.49      ((~m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))) | (u1_orders_2(sK1) = u1_orders_2(sK2)))).
% 0.21/0.49  
% 0.21/0.49  tff(u171,negated_conjecture,
% 0.21/0.49      l1_orders_2(sK1)).
% 0.21/0.49  
% 0.21/0.49  tff(u170,negated_conjecture,
% 0.21/0.49      l1_orders_2(sK2)).
% 0.21/0.49  
% 0.21/0.49  tff(u169,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))).
% 0.21/0.49  
% 0.21/0.49  tff(u168,axiom,
% 0.21/0.49      (![X0] : ((m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u167,negated_conjecture,
% 0.21/0.49      ((~m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))) | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u166,negated_conjecture,
% 0.21/0.49      ((~m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))) | (~(u1_struct_0(sK1) = u1_struct_0(sK2))) | (![X1, X0] : ((~r1_orders_2(sK2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_orders_2(sK1,X0,X1)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u165,negated_conjecture,
% 0.21/0.49      ((~m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))) | (~(u1_struct_0(sK1) = u1_struct_0(sK2))) | (![X1, X0] : ((~r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r1_orders_2(sK2,X0,X1)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u164,negated_conjecture,
% 0.21/0.49      ((~m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))) | (~(u1_struct_0(sK1) = u1_struct_0(sK2))) | (![X1, X0] : ((~r2_orders_2(sK2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r2_orders_2(sK1,X0,X1)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u163,negated_conjecture,
% 0.21/0.49      ((~m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))) | (~(u1_struct_0(sK1) = u1_struct_0(sK2))) | (![X1, X0] : ((~r2_orders_2(sK1,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r2_orders_2(sK2,X0,X1)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u162,negated_conjecture,
% 0.21/0.49      ((~sP0(sK2,sK3,sK1,sK3)) | ~v12_waybel_0(sK3,sK2))).
% 0.21/0.49  
% 0.21/0.49  tff(u161,negated_conjecture,
% 0.21/0.49      ((~sP0(sK2,sK3,sK1,sK3)) | v12_waybel_0(sK3,sK1))).
% 0.21/0.49  
% 0.21/0.49  tff(u160,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((~sP0(X0,X1,X2,X3) | ~v12_waybel_0(X1,X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u159,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((~sP0(X0,X1,X2,X3) | v12_waybel_0(X3,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u158,negated_conjecture,
% 0.21/0.49      ((~sP0(sK2,sK3,sK1,sK3)) | sP0(sK2,sK3,sK1,sK3))).
% 0.21/0.49  
% 0.21/0.49  % (8668)# SZS output end Saturation.
% 0.21/0.49  % (8668)------------------------------
% 0.21/0.49  % (8668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8668)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (8668)Memory used [KB]: 10618
% 0.21/0.49  % (8668)Time elapsed: 0.081 s
% 0.21/0.49  % (8668)------------------------------
% 0.21/0.49  % (8668)------------------------------
% 0.21/0.49  % (8641)Success in time 0.133 s
%------------------------------------------------------------------------------
