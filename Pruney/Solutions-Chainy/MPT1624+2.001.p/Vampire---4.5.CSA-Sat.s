%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:52 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    0
%              Number of atoms          :  110 ( 110 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u280,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X1,X0)
          | u1_orders_2(sK0) = X0 )
    | ! [X1,X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X1,X0)
        | u1_orders_2(sK0) = X0 ) )).

tff(u279,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          | u1_struct_0(sK0) = X0 )
    | ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK0) = X0 ) )).

tff(u278,negated_conjecture,
    ( sK2 != sK3
    | sK2 = sK3 )).

tff(u277,negated_conjecture,
    ( u1_struct_0(sK0) != u1_struct_0(sK1)
    | u1_struct_0(sK0) = u1_struct_0(sK1) )).

tff(u276,negated_conjecture,
    ( u1_orders_2(sK0) != u1_orders_2(sK1)
    | u1_orders_2(sK0) = u1_orders_2(sK1) )).

tff(u275,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) )).

tff(u274,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

tff(u273,negated_conjecture,
    ( ~ ! [X3] :
          ( ~ r1_tarski(u1_struct_0(X3),u1_struct_0(sK0))
          | ~ r1_tarski(u1_orders_2(X3),u1_orders_2(sK0))
          | m1_yellow_0(X3,sK1)
          | ~ l1_orders_2(X3) )
    | ! [X3] :
        ( ~ r1_tarski(u1_struct_0(X3),u1_struct_0(sK0))
        | ~ r1_tarski(u1_orders_2(X3),u1_orders_2(sK0))
        | m1_yellow_0(X3,sK1)
        | ~ l1_orders_2(X3) ) )).

tff(u272,negated_conjecture,
    ( ~ ! [X4] :
          ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(X4))
          | ~ r1_tarski(u1_orders_2(sK0),u1_orders_2(X4))
          | m1_yellow_0(sK1,X4)
          | ~ l1_orders_2(X4) )
    | ! [X4] :
        ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(X4))
        | ~ r1_tarski(u1_orders_2(sK0),u1_orders_2(X4))
        | m1_yellow_0(sK1,X4)
        | ~ l1_orders_2(X4) ) )).

tff(u271,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u270,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) )).

tff(u269,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) )).

tff(u268,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) )).

tff(u267,axiom,(
    ! [X1,X5,X0,X4] :
      ( ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X4,X5)
      | r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) )).

% (6050)Refutation not found, incomplete strategy% (6050)------------------------------
% (6050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6050)Termination reason: Refutation not found, incomplete strategy

% (6050)Memory used [KB]: 10618
% (6050)Time elapsed: 0.108 s
% (6050)------------------------------
% (6050)------------------------------
tff(u266,negated_conjecture,
    ( ~ ! [X1,X0,X2] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK0))
          | ~ r1_orders_2(sK1,X1,X0)
          | r1_orders_2(X2,X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(X2))
          | ~ m1_subset_1(X1,u1_struct_0(X2))
          | ~ m1_yellow_0(sK1,X2)
          | ~ l1_orders_2(X2) )
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,X1,X0)
        | r1_orders_2(X2,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(X2))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ m1_yellow_0(sK1,X2)
        | ~ l1_orders_2(X2) ) )).

tff(u265,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u264,axiom,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) )).

tff(u263,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u262,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | u1_orders_2(X0) = X2
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) )).

tff(u261,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_yellow_0(X0,X0) ) )).

tff(u260,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) )).

tff(u259,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u258,negated_conjecture,
    ( ~ l1_orders_2(sK1)
    | l1_orders_2(sK1) )).

tff(u257,axiom,(
    ! [X1,X0] :
      ( ~ m1_yellow_0(X1,X0)
      | r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

tff(u256,axiom,(
    ! [X1,X0] :
      ( ~ m1_yellow_0(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

tff(u255,negated_conjecture,
    ( ~ m1_yellow_0(sK0,sK0)
    | m1_yellow_0(sK0,sK0) )).

tff(u254,negated_conjecture,
    ( ~ m1_yellow_0(sK0,sK1)
    | m1_yellow_0(sK0,sK1) )).

tff(u253,negated_conjecture,
    ( ~ m1_yellow_0(sK1,sK1)
    | m1_yellow_0(sK1,sK1) )).

tff(u252,negated_conjecture,
    ( ~ m1_yellow_0(sK1,sK0)
    | m1_yellow_0(sK1,sK0) )).

tff(u251,negated_conjecture,
    ( ~ ~ v2_waybel_0(sK2,sK1)
    | ~ v2_waybel_0(sK2,sK1) )).

tff(u250,negated_conjecture,
    ( ~ v2_waybel_0(sK2,sK0)
    | v2_waybel_0(sK2,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (6048)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.46  % (6042)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.47  % (6042)Refutation not found, incomplete strategy% (6042)------------------------------
% 0.19/0.47  % (6042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (6042)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (6042)Memory used [KB]: 6268
% 0.19/0.48  % (6042)Time elapsed: 0.062 s
% 0.19/0.48  % (6042)------------------------------
% 0.19/0.48  % (6042)------------------------------
% 0.19/0.49  % (6044)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.49  % (6043)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.49  % (6031)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.49  % (6031)Refutation not found, incomplete strategy% (6031)------------------------------
% 0.19/0.49  % (6031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (6031)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (6031)Memory used [KB]: 10618
% 0.19/0.49  % (6031)Time elapsed: 0.086 s
% 0.19/0.49  % (6031)------------------------------
% 0.19/0.49  % (6031)------------------------------
% 0.19/0.49  % (6036)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.50  % (6041)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.50  % (6041)Refutation not found, incomplete strategy% (6041)------------------------------
% 0.19/0.50  % (6041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (6041)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (6041)Memory used [KB]: 10618
% 0.19/0.50  % (6041)Time elapsed: 0.105 s
% 0.19/0.50  % (6041)------------------------------
% 0.19/0.50  % (6041)------------------------------
% 0.19/0.50  % (6034)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.50  % (6052)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.50  % (6052)Refutation not found, incomplete strategy% (6052)------------------------------
% 0.19/0.50  % (6052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (6052)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (6052)Memory used [KB]: 10618
% 0.19/0.50  % (6052)Time elapsed: 0.067 s
% 0.19/0.50  % (6052)------------------------------
% 0.19/0.50  % (6052)------------------------------
% 0.19/0.50  % (6047)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.50  % (6039)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.51  % (6030)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.51  % (6032)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.51  % (6049)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.51  % (6045)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.51  % (6050)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.51  % (6035)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.51  % (6055)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.51  % (6032)# SZS output start Saturation.
% 0.19/0.51  tff(u280,negated_conjecture,
% 0.19/0.51      ((~(![X1, X0] : (((g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X1,X0)) | (u1_orders_2(sK0) = X0))))) | (![X1, X0] : (((g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X1,X0)) | (u1_orders_2(sK0) = X0)))))).
% 0.19/0.51  
% 0.19/0.51  tff(u279,negated_conjecture,
% 0.19/0.51      ((~(![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_struct_0(sK0) = X0))))) | (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_struct_0(sK0) = X0)))))).
% 0.19/0.51  
% 0.19/0.51  tff(u278,negated_conjecture,
% 0.19/0.51      ((~(sK2 = sK3)) | (sK2 = sK3))).
% 0.19/0.51  
% 0.19/0.51  tff(u277,negated_conjecture,
% 0.19/0.51      ((~(u1_struct_0(sK0) = u1_struct_0(sK1))) | (u1_struct_0(sK0) = u1_struct_0(sK1)))).
% 0.19/0.51  
% 0.19/0.51  tff(u276,negated_conjecture,
% 0.19/0.51      ((~(u1_orders_2(sK0) = u1_orders_2(sK1))) | (u1_orders_2(sK0) = u1_orders_2(sK1)))).
% 0.19/0.51  
% 0.19/0.51  tff(u275,axiom,
% 0.19/0.51      (![X1, X0] : ((~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | (X0 = X1))))).
% 0.19/0.51  
% 0.19/0.51  tff(u274,axiom,
% 0.19/0.51      (![X1, X0] : ((~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.19/0.51  
% 0.19/0.51  tff(u273,negated_conjecture,
% 0.19/0.51      ((~(![X3] : ((~r1_tarski(u1_struct_0(X3),u1_struct_0(sK0)) | ~r1_tarski(u1_orders_2(X3),u1_orders_2(sK0)) | m1_yellow_0(X3,sK1) | ~l1_orders_2(X3))))) | (![X3] : ((~r1_tarski(u1_struct_0(X3),u1_struct_0(sK0)) | ~r1_tarski(u1_orders_2(X3),u1_orders_2(sK0)) | m1_yellow_0(X3,sK1) | ~l1_orders_2(X3)))))).
% 0.19/0.51  
% 0.19/0.51  tff(u272,negated_conjecture,
% 0.19/0.51      ((~(![X4] : ((~r1_tarski(u1_struct_0(sK0),u1_struct_0(X4)) | ~r1_tarski(u1_orders_2(sK0),u1_orders_2(X4)) | m1_yellow_0(sK1,X4) | ~l1_orders_2(X4))))) | (![X4] : ((~r1_tarski(u1_struct_0(sK0),u1_struct_0(X4)) | ~r1_tarski(u1_orders_2(sK0),u1_orders_2(X4)) | m1_yellow_0(sK1,X4) | ~l1_orders_2(X4)))))).
% 0.19/0.51  
% 0.19/0.51  tff(u271,axiom,
% 0.19/0.51      (![X1] : (r1_tarski(X1,X1)))).
% 0.19/0.51  
% 0.19/0.51  tff(u270,axiom,
% 0.19/0.51      (![X1, X0, X2] : ((~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))))).
% 0.19/0.51  
% 0.19/0.51  tff(u269,axiom,
% 0.19/0.51      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X1 = X3))))).
% 0.19/0.51  
% 0.19/0.51  tff(u268,axiom,
% 0.19/0.51      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X0 = X2))))).
% 0.19/0.51  
% 0.19/0.51  tff(u267,axiom,
% 0.19/0.51      (![X1, X5, X0, X4] : ((~m1_subset_1(X5,u1_struct_0(X1)) | ~r1_orders_2(X1,X4,X5) | r1_orders_2(X0,X4,X5) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0))))).
% 0.19/0.51  
% 0.19/0.51  % (6050)Refutation not found, incomplete strategy% (6050)------------------------------
% 0.19/0.51  % (6050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (6050)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (6050)Memory used [KB]: 10618
% 0.19/0.51  % (6050)Time elapsed: 0.108 s
% 0.19/0.51  % (6050)------------------------------
% 0.19/0.51  % (6050)------------------------------
% 0.19/0.51  tff(u266,negated_conjecture,
% 0.19/0.51      ((~(![X1, X0, X2] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK1,X1,X0) | r1_orders_2(X2,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_yellow_0(sK1,X2) | ~l1_orders_2(X2))))) | (![X1, X0, X2] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK1,X1,X0) | r1_orders_2(X2,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_yellow_0(sK1,X2) | ~l1_orders_2(X2)))))).
% 0.19/0.51  
% 0.19/0.51  tff(u265,negated_conjecture,
% 0.19/0.51      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.19/0.51  
% 0.19/0.51  tff(u264,axiom,
% 0.19/0.51      (![X0] : ((m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))))).
% 0.19/0.51  
% 0.19/0.51  tff(u263,negated_conjecture,
% 0.19/0.51      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 0.19/0.51  
% 0.19/0.51  tff(u262,axiom,
% 0.19/0.51      (![X1, X0, X2] : ((~l1_orders_2(X0) | (u1_orders_2(X0) = X2) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)))))).
% 0.19/0.51  
% 0.19/0.51  tff(u261,axiom,
% 0.19/0.51      (![X0] : ((~l1_orders_2(X0) | m1_yellow_0(X0,X0))))).
% 0.19/0.51  
% 0.19/0.51  tff(u260,axiom,
% 0.19/0.51      (![X1, X0, X2] : ((~l1_orders_2(X0) | (u1_struct_0(X0) = X1) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)))))).
% 0.19/0.51  
% 0.19/0.51  tff(u259,negated_conjecture,
% 0.19/0.51      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.19/0.51  
% 0.19/0.51  tff(u258,negated_conjecture,
% 0.19/0.51      ((~l1_orders_2(sK1)) | l1_orders_2(sK1))).
% 0.19/0.51  
% 0.19/0.51  tff(u257,axiom,
% 0.19/0.51      (![X1, X0] : ((~m1_yellow_0(X1,X0) | r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.19/0.51  
% 0.19/0.51  tff(u256,axiom,
% 0.19/0.51      (![X1, X0] : ((~m1_yellow_0(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.19/0.51  
% 0.19/0.51  tff(u255,negated_conjecture,
% 0.19/0.51      ((~m1_yellow_0(sK0,sK0)) | m1_yellow_0(sK0,sK0))).
% 0.19/0.51  
% 0.19/0.51  tff(u254,negated_conjecture,
% 0.19/0.51      ((~m1_yellow_0(sK0,sK1)) | m1_yellow_0(sK0,sK1))).
% 0.19/0.51  
% 0.19/0.51  tff(u253,negated_conjecture,
% 0.19/0.51      ((~m1_yellow_0(sK1,sK1)) | m1_yellow_0(sK1,sK1))).
% 0.19/0.51  
% 0.19/0.51  tff(u252,negated_conjecture,
% 0.19/0.51      ((~m1_yellow_0(sK1,sK0)) | m1_yellow_0(sK1,sK0))).
% 0.19/0.51  
% 0.19/0.51  tff(u251,negated_conjecture,
% 0.19/0.51      ((~~v2_waybel_0(sK2,sK1)) | ~v2_waybel_0(sK2,sK1))).
% 0.19/0.51  
% 0.19/0.51  tff(u250,negated_conjecture,
% 0.19/0.51      ((~v2_waybel_0(sK2,sK0)) | v2_waybel_0(sK2,sK0))).
% 0.19/0.51  
% 0.19/0.51  % (6032)# SZS output end Saturation.
% 0.19/0.51  % (6032)------------------------------
% 0.19/0.51  % (6032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (6032)Termination reason: Satisfiable
% 0.19/0.51  
% 0.19/0.51  % (6032)Memory used [KB]: 6268
% 0.19/0.51  % (6032)Time elapsed: 0.107 s
% 0.19/0.51  % (6032)------------------------------
% 0.19/0.51  % (6032)------------------------------
% 0.19/0.51  % (6045)Refutation not found, incomplete strategy% (6045)------------------------------
% 0.19/0.51  % (6045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (6045)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (6045)Memory used [KB]: 6268
% 0.19/0.51  % (6045)Time elapsed: 0.112 s
% 0.19/0.51  % (6045)------------------------------
% 0.19/0.51  % (6045)------------------------------
% 0.19/0.51  % (6029)Success in time 0.159 s
%------------------------------------------------------------------------------
