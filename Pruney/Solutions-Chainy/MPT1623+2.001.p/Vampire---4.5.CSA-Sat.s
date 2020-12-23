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
% DateTime   : Thu Dec  3 13:16:52 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   33 (  33 expanded)
%              Depth                    :    0
%              Number of atoms          :  102 ( 102 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u284,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ! [X3,X2] :
        ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK0) = X2 ) )).

tff(u283,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK0) = X1 ) )).

tff(u282,negated_conjecture,
    ( u1_orders_2(sK0) != u1_orders_2(sK1)
    | u1_orders_2(sK0) = u1_orders_2(sK1) )).

tff(u281,negated_conjecture,
    ( u1_struct_0(sK0) != u1_struct_0(sK1)
    | u1_struct_0(sK0) = u1_struct_0(sK1) )).

tff(u280,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) )).

tff(u279,negated_conjecture,
    ( sK2 != sK3
    | sK2 = sK3 )).

tff(u278,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) )).

tff(u277,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

tff(u276,negated_conjecture,
    ( ~ l1_orders_2(sK1)
    | u1_orders_2(sK0) != u1_orders_2(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK1)
    | ! [X3] :
        ( ~ r1_tarski(u1_struct_0(X3),u1_struct_0(sK0))
        | ~ r1_tarski(u1_orders_2(X3),u1_orders_2(sK0))
        | m1_yellow_0(X3,sK1)
        | ~ l1_orders_2(X3) ) )).

tff(u275,negated_conjecture,
    ( ~ l1_orders_2(sK1)
    | u1_orders_2(sK0) != u1_orders_2(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK1)
    | ! [X4] :
        ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(X4))
        | ~ r1_tarski(u1_orders_2(sK0),u1_orders_2(X4))
        | m1_yellow_0(sK1,X4)
        | ~ l1_orders_2(X4) ) )).

tff(u274,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u273,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) )).

tff(u272,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) )).

tff(u271,axiom,(
    ! [X1,X5,X0,X4] :
      ( ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X4,X5)
      | r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) )).

tff(u270,negated_conjecture,
    ( u1_struct_0(sK0) != u1_struct_0(sK1)
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK1,X1,X0)
        | r1_orders_2(X2,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(X2))
        | ~ m1_subset_1(X1,u1_struct_0(X2))
        | ~ m1_yellow_0(sK1,X2)
        | ~ l1_orders_2(X2) ) )).

tff(u269,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u268,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u267,axiom,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) )).

tff(u266,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u265,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) )).

tff(u264,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | u1_orders_2(X0) = X2
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) )).

tff(u263,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) ) )).

tff(u262,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_yellow_0(X0,X0) ) )).

tff(u261,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u260,negated_conjecture,
    ( ~ l1_orders_2(sK1)
    | l1_orders_2(sK1) )).

tff(u259,axiom,(
    ! [X1,X0] :
      ( ~ m1_yellow_0(X1,X0)
      | r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

tff(u258,axiom,(
    ! [X1,X0] :
      ( ~ m1_yellow_0(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) )).

tff(u257,negated_conjecture,
    ( ~ m1_yellow_0(sK0,sK0)
    | m1_yellow_0(sK0,sK0) )).

tff(u256,negated_conjecture,
    ( ~ m1_yellow_0(sK0,sK1)
    | m1_yellow_0(sK0,sK1) )).

tff(u255,negated_conjecture,
    ( ~ m1_yellow_0(sK1,sK1)
    | m1_yellow_0(sK1,sK1) )).

tff(u254,negated_conjecture,
    ( ~ m1_yellow_0(sK1,sK0)
    | m1_yellow_0(sK1,sK0) )).

tff(u253,negated_conjecture,
    ( ~ ~ v1_waybel_0(sK2,sK1)
    | ~ v1_waybel_0(sK2,sK1) )).

tff(u252,negated_conjecture,
    ( ~ v1_waybel_0(sK2,sK0)
    | v1_waybel_0(sK2,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:31:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (22617)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (22614)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (22616)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (22626)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (22632)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (22616)Refutation not found, incomplete strategy% (22616)------------------------------
% 0.21/0.50  % (22616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22618)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (22618)Refutation not found, incomplete strategy% (22618)------------------------------
% 0.21/0.50  % (22618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22636)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (22618)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (22618)Memory used [KB]: 6140
% 0.21/0.50  % (22618)Time elapsed: 0.088 s
% 0.21/0.50  % (22618)------------------------------
% 0.21/0.50  % (22618)------------------------------
% 0.21/0.50  % (22635)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (22636)# SZS output start Saturation.
% 0.21/0.51  tff(u284,negated_conjecture,
% 0.21/0.51      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | (![X3, X2] : (((g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_struct_0(sK0) = X2)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u283,negated_conjecture,
% 0.21/0.51      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_orders_2(sK0) = X1)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u282,negated_conjecture,
% 0.21/0.51      ((~(u1_orders_2(sK0) = u1_orders_2(sK1))) | (u1_orders_2(sK0) = u1_orders_2(sK1)))).
% 0.21/0.51  
% 0.21/0.51  tff(u281,negated_conjecture,
% 0.21/0.51      ((~(u1_struct_0(sK0) = u1_struct_0(sK1))) | (u1_struct_0(sK0) = u1_struct_0(sK1)))).
% 0.21/0.51  
% 0.21/0.51  tff(u280,negated_conjecture,
% 0.21/0.51      ((~(g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)))) | (g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))))).
% 0.21/0.51  
% 0.21/0.51  tff(u279,negated_conjecture,
% 0.21/0.51      ((~(sK2 = sK3)) | (sK2 = sK3))).
% 0.21/0.51  
% 0.21/0.51  tff(u278,axiom,
% 0.21/0.51      (![X1, X0] : ((~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | (X0 = X1))))).
% 0.21/0.51  
% 0.21/0.51  tff(u277,axiom,
% 0.21/0.51      (![X1, X0] : ((~r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | m1_yellow_0(X1,X0) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u276,negated_conjecture,
% 0.21/0.51      ((~l1_orders_2(sK1)) | (~(u1_orders_2(sK0) = u1_orders_2(sK1))) | (~(u1_struct_0(sK0) = u1_struct_0(sK1))) | (![X3] : ((~r1_tarski(u1_struct_0(X3),u1_struct_0(sK0)) | ~r1_tarski(u1_orders_2(X3),u1_orders_2(sK0)) | m1_yellow_0(X3,sK1) | ~l1_orders_2(X3)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u275,negated_conjecture,
% 0.21/0.51      ((~l1_orders_2(sK1)) | (~(u1_orders_2(sK0) = u1_orders_2(sK1))) | (~(u1_struct_0(sK0) = u1_struct_0(sK1))) | (![X4] : ((~r1_tarski(u1_struct_0(sK0),u1_struct_0(X4)) | ~r1_tarski(u1_orders_2(sK0),u1_orders_2(X4)) | m1_yellow_0(sK1,X4) | ~l1_orders_2(X4)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u274,axiom,
% 0.21/0.51      (![X1] : (r1_tarski(X1,X1)))).
% 0.21/0.51  
% 0.21/0.51  tff(u273,axiom,
% 0.21/0.51      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X1 = X3))))).
% 0.21/0.51  
% 0.21/0.51  tff(u272,axiom,
% 0.21/0.51      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X0 = X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u271,axiom,
% 0.21/0.51      (![X1, X5, X0, X4] : ((~m1_subset_1(X5,u1_struct_0(X1)) | ~r1_orders_2(X1,X4,X5) | r1_orders_2(X0,X4,X5) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_yellow_0(X1,X0) | ~l1_orders_2(X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u270,negated_conjecture,
% 0.21/0.51      ((~(u1_struct_0(sK0) = u1_struct_0(sK1))) | (![X1, X0, X2] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK1,X1,X0) | r1_orders_2(X2,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~m1_yellow_0(sK1,X2) | ~l1_orders_2(X2)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u269,negated_conjecture,
% 0.21/0.51      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u268,negated_conjecture,
% 0.21/0.51      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))).
% 0.21/0.51  
% 0.21/0.51  tff(u267,axiom,
% 0.21/0.51      (![X0] : ((m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u266,negated_conjecture,
% 0.21/0.51      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u265,negated_conjecture,
% 0.21/0.51      ((~m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))) | m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u264,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~l1_orders_2(X0) | (u1_orders_2(X0) = X2) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u263,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~l1_orders_2(X0) | (u1_struct_0(X0) = X1) | (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u262,axiom,
% 0.21/0.51      (![X0] : ((~l1_orders_2(X0) | m1_yellow_0(X0,X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u261,negated_conjecture,
% 0.21/0.51      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.21/0.51  
% 0.21/0.51  tff(u260,negated_conjecture,
% 0.21/0.51      ((~l1_orders_2(sK1)) | l1_orders_2(sK1))).
% 0.21/0.51  
% 0.21/0.51  tff(u259,axiom,
% 0.21/0.51      (![X1, X0] : ((~m1_yellow_0(X1,X0) | r1_tarski(u1_orders_2(X1),u1_orders_2(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u258,axiom,
% 0.21/0.51      (![X1, X0] : ((~m1_yellow_0(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~l1_orders_2(X1) | ~l1_orders_2(X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u257,negated_conjecture,
% 0.21/0.51      ((~m1_yellow_0(sK0,sK0)) | m1_yellow_0(sK0,sK0))).
% 0.21/0.51  
% 0.21/0.51  tff(u256,negated_conjecture,
% 0.21/0.51      ((~m1_yellow_0(sK0,sK1)) | m1_yellow_0(sK0,sK1))).
% 0.21/0.51  
% 0.21/0.51  tff(u255,negated_conjecture,
% 0.21/0.51      ((~m1_yellow_0(sK1,sK1)) | m1_yellow_0(sK1,sK1))).
% 0.21/0.51  
% 0.21/0.51  tff(u254,negated_conjecture,
% 0.21/0.51      ((~m1_yellow_0(sK1,sK0)) | m1_yellow_0(sK1,sK0))).
% 0.21/0.51  
% 0.21/0.51  tff(u253,negated_conjecture,
% 0.21/0.51      ((~~v1_waybel_0(sK2,sK1)) | ~v1_waybel_0(sK2,sK1))).
% 0.21/0.51  
% 0.21/0.51  tff(u252,negated_conjecture,
% 0.21/0.51      ((~v1_waybel_0(sK2,sK0)) | v1_waybel_0(sK2,sK0))).
% 0.21/0.51  
% 0.21/0.51  % (22636)# SZS output end Saturation.
% 0.21/0.51  % (22636)------------------------------
% 0.21/0.51  % (22636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22636)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (22636)Memory used [KB]: 10746
% 0.21/0.51  % (22636)Time elapsed: 0.066 s
% 0.21/0.51  % (22636)------------------------------
% 0.21/0.51  % (22636)------------------------------
% 0.21/0.51  % (22637)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (22612)Success in time 0.143 s
%------------------------------------------------------------------------------
