%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:04 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    0
%              Number of atoms          :   90 (  90 expanded)
%              Number of equality atoms :   28 (  28 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (4073)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
tff(u197,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X1,X0)
          | u1_orders_2(sK0) = X0 )
    | ! [X1,X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X1,X0)
        | u1_orders_2(sK0) = X0 ) )).

tff(u196,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          | u1_struct_0(sK0) = X0 )
    | ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK0) = X0 ) )).

tff(u195,negated_conjecture,
    ( sK2 != sK3
    | sK2 = sK3 )).

tff(u194,negated_conjecture,
    ( u1_struct_0(sK0) != u1_struct_0(sK1)
    | u1_struct_0(sK0) = u1_struct_0(sK1) )).

tff(u193,negated_conjecture,
    ( u1_orders_2(sK0) != u1_orders_2(sK1)
    | u1_orders_2(sK0) = u1_orders_2(sK1) )).

tff(u192,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | u1_orders_2(X0) = X2
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) )).

tff(u191,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) )).

tff(u190,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u189,negated_conjecture,
    ( ~ l1_orders_2(sK1)
    | l1_orders_2(sK1) )).

tff(u188,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) )).

tff(u187,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) )).

tff(u186,axiom,(
    ! [X1,X5,X0,X4] :
      ( ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

tff(u185,axiom,(
    ! [X1,X5,X0,X4] :
      ( ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_orders_2(X0,X4,X5)
      | r2_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

tff(u184,negated_conjecture,
    ( ~ ! [X3,X5,X4] :
          ( ~ m1_subset_1(X5,u1_struct_0(sK0))
          | ~ m1_subset_1(X3,u1_struct_0(sK0))
          | ~ r2_orders_2(X4,X5,X3)
          | r2_orders_2(sK1,X5,X3)
          | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
          | ~ m1_subset_1(X3,u1_struct_0(X4))
          | ~ m1_subset_1(X5,u1_struct_0(X4))
          | ~ l1_orders_2(X4) )
    | ! [X3,X5,X4] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_orders_2(X4,X5,X3)
        | r2_orders_2(sK1,X5,X3)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))
        | ~ m1_subset_1(X3,u1_struct_0(X4))
        | ~ m1_subset_1(X5,u1_struct_0(X4))
        | ~ l1_orders_2(X4) ) )).

tff(u183,negated_conjecture,
    ( ~ ! [X1,X0,X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | ~ r1_orders_2(X1,X2,X0)
          | r1_orders_2(sK1,X2,X0)
          | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(X1))
          | ~ m1_subset_1(X2,u1_struct_0(X1))
          | ~ l1_orders_2(X1) )
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(X1,X2,X0)
        | r1_orders_2(sK1,X2,X0)
        | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ l1_orders_2(X1) ) )).

tff(u182,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u181,axiom,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) )).

tff(u180,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u179,negated_conjecture,
    ( ~ ~ v13_waybel_0(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1) )).

tff(u178,negated_conjecture,
    ( ~ v13_waybel_0(sK2,sK0)
    | v13_waybel_0(sK2,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (4066)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (4062)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (4082)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (4066)Refutation not found, incomplete strategy% (4066)------------------------------
% 0.20/0.52  % (4066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4066)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (4066)Memory used [KB]: 10618
% 0.20/0.52  % (4066)Time elapsed: 0.110 s
% 0.20/0.52  % (4066)------------------------------
% 0.20/0.52  % (4066)------------------------------
% 0.20/0.52  % (4064)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (4065)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (4063)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (4065)Refutation not found, incomplete strategy% (4065)------------------------------
% 0.20/0.52  % (4065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4065)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (4065)Memory used [KB]: 6140
% 0.20/0.52  % (4065)Time elapsed: 0.107 s
% 0.20/0.52  % (4065)------------------------------
% 0.20/0.52  % (4065)------------------------------
% 0.20/0.52  % (4063)Refutation not found, incomplete strategy% (4063)------------------------------
% 0.20/0.52  % (4063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4063)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (4063)Memory used [KB]: 6140
% 0.20/0.52  % (4063)Time elapsed: 0.106 s
% 0.20/0.52  % (4063)------------------------------
% 0.20/0.52  % (4063)------------------------------
% 0.20/0.53  % (4064)Refutation not found, incomplete strategy% (4064)------------------------------
% 0.20/0.53  % (4064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4064)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4064)Memory used [KB]: 6140
% 0.20/0.53  % (4064)Time elapsed: 0.110 s
% 0.20/0.53  % (4064)------------------------------
% 0.20/0.53  % (4064)------------------------------
% 0.20/0.53  % (4082)Refutation not found, incomplete strategy% (4082)------------------------------
% 0.20/0.53  % (4082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4082)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4082)Memory used [KB]: 10618
% 0.20/0.53  % (4082)Time elapsed: 0.118 s
% 0.20/0.53  % (4082)------------------------------
% 0.20/0.53  % (4082)------------------------------
% 0.20/0.53  % (4080)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (4072)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (4062)# SZS output start Saturation.
% 0.20/0.53  % (4073)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  tff(u197,negated_conjecture,
% 0.20/0.53      ((~(![X1, X0] : (((g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X1,X0)) | (u1_orders_2(sK0) = X0))))) | (![X1, X0] : (((g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X1,X0)) | (u1_orders_2(sK0) = X0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u196,negated_conjecture,
% 0.20/0.53      ((~(![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_struct_0(sK0) = X0))))) | (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_struct_0(sK0) = X0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u195,negated_conjecture,
% 0.20/0.53      ((~(sK2 = sK3)) | (sK2 = sK3))).
% 0.20/0.53  
% 0.20/0.53  tff(u194,negated_conjecture,
% 0.20/0.53      ((~(u1_struct_0(sK0) = u1_struct_0(sK1))) | (u1_struct_0(sK0) = u1_struct_0(sK1)))).
% 0.20/0.53  
% 0.20/0.53  tff(u193,negated_conjecture,
% 0.20/0.53      ((~(u1_orders_2(sK0) = u1_orders_2(sK1))) | (u1_orders_2(sK0) = u1_orders_2(sK1)))).
% 0.20/0.53  
% 0.20/0.53  tff(u192,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~l1_orders_2(X0) | (u1_orders_2(X0) = X2) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u191,axiom,
% 0.20/0.53      (![X1, X0, X2] : ((~l1_orders_2(X0) | (u1_struct_0(X0) = X1) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u190,negated_conjecture,
% 0.20/0.53      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.20/0.53  
% 0.20/0.53  tff(u189,negated_conjecture,
% 0.20/0.53      ((~l1_orders_2(sK1)) | l1_orders_2(sK1))).
% 0.20/0.53  
% 0.20/0.53  tff(u188,axiom,
% 0.20/0.53      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X1 = X3))))).
% 0.20/0.53  
% 0.20/0.53  tff(u187,axiom,
% 0.20/0.53      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X0 = X2))))).
% 0.20/0.53  
% 0.20/0.53  tff(u186,axiom,
% 0.20/0.53      (![X1, X5, X0, X4] : ((~m1_subset_1(X5,u1_struct_0(X1)) | ~r1_orders_2(X0,X4,X5) | r1_orders_2(X1,X4,X5) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u185,axiom,
% 0.20/0.53      (![X1, X5, X0, X4] : ((~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_orders_2(X0,X4,X5) | r2_orders_2(X1,X4,X5) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u184,negated_conjecture,
% 0.20/0.53      ((~(![X3, X5, X4] : ((~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_orders_2(X4,X5,X3) | r2_orders_2(sK1,X5,X3) | (g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))) | ~m1_subset_1(X3,u1_struct_0(X4)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_orders_2(X4))))) | (![X3, X5, X4] : ((~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_orders_2(X4,X5,X3) | r2_orders_2(sK1,X5,X3) | (g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))) | ~m1_subset_1(X3,u1_struct_0(X4)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_orders_2(X4)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u183,negated_conjecture,
% 0.20/0.53      ((~(![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(X1,X2,X0) | r1_orders_2(sK1,X2,X0) | (g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1))))) | (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(X1,X2,X0) | r1_orders_2(sK1,X2,X0) | (g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u182,negated_conjecture,
% 0.20/0.53      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u181,axiom,
% 0.20/0.53      (![X0] : ((m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))))).
% 0.20/0.53  
% 0.20/0.53  tff(u180,negated_conjecture,
% 0.20/0.53      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 0.20/0.53  
% 0.20/0.53  tff(u179,negated_conjecture,
% 0.20/0.53      ((~~v13_waybel_0(sK2,sK1)) | ~v13_waybel_0(sK2,sK1))).
% 0.20/0.53  
% 0.20/0.53  tff(u178,negated_conjecture,
% 0.20/0.53      ((~v13_waybel_0(sK2,sK0)) | v13_waybel_0(sK2,sK0))).
% 0.20/0.53  
% 0.20/0.53  % (4062)# SZS output end Saturation.
% 0.20/0.53  % (4062)------------------------------
% 0.20/0.53  % (4062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4062)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (4062)Memory used [KB]: 6268
% 0.20/0.53  % (4062)Time elapsed: 0.111 s
% 0.20/0.53  % (4062)------------------------------
% 0.20/0.53  % (4062)------------------------------
% 0.20/0.53  % (4071)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.53  % (4081)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (4059)Success in time 0.175 s
%------------------------------------------------------------------------------
