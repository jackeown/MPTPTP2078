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
% DateTime   : Thu Dec  3 13:15:58 EST 2020

% Result     : CounterSatisfiable 1.32s
% Output     : Saturation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   48 (  48 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u137,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK0) = X1 ) )).

tff(u136,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK0) = X0 ) )).

tff(u135,negated_conjecture,
    ( u1_struct_0(sK0) != u1_struct_0(sK1)
    | u1_struct_0(sK0) = u1_struct_0(sK1) )).

tff(u134,negated_conjecture,
    ( u1_orders_2(sK0) != u1_orders_2(sK1)
    | u1_orders_2(sK0) = u1_orders_2(sK1) )).

tff(u133,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) )).

tff(u132,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u131,negated_conjecture,
    ( ~ l1_orders_2(sK1)
    | l1_orders_2(sK1) )).

tff(u130,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) )).

tff(u129,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) )).

tff(u128,negated_conjecture,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

tff(u127,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u126,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) )).

tff(u125,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
          | r1_orders_2(sK1,X0,X1)
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) )).

tff(u124,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK1,sK2)
    | ~ r1_yellow_0(sK1,sK2) )).

tff(u123,negated_conjecture,
    ( ~ r1_yellow_0(sK0,sK2)
    | r1_yellow_0(sK0,sK2) )).

tff(u122,negated_conjecture,
    ( ~ ~ r2_yellow_0(sK1,sK2)
    | ~ r2_yellow_0(sK1,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:06:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (3872)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (3888)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (3864)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (3864)Refutation not found, incomplete strategy% (3864)------------------------------
% 0.21/0.51  % (3864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3864)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3864)Memory used [KB]: 6268
% 0.21/0.51  % (3864)Time elapsed: 0.109 s
% 0.21/0.51  % (3864)------------------------------
% 0.21/0.51  % (3864)------------------------------
% 1.19/0.51  % (3872)Refutation not found, incomplete strategy% (3872)------------------------------
% 1.19/0.51  % (3872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (3880)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.19/0.52  % (3872)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.52  
% 1.19/0.52  % (3872)Memory used [KB]: 6268
% 1.19/0.52  % (3872)Time elapsed: 0.106 s
% 1.19/0.52  % (3872)------------------------------
% 1.19/0.52  % (3872)------------------------------
% 1.19/0.52  % (3861)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.19/0.53  % (3880)Refutation not found, incomplete strategy% (3880)------------------------------
% 1.19/0.53  % (3880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (3880)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (3880)Memory used [KB]: 10746
% 1.32/0.53  % (3880)Time elapsed: 0.119 s
% 1.32/0.53  % (3880)------------------------------
% 1.32/0.53  % (3880)------------------------------
% 1.32/0.53  % (3882)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.53  % (3860)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.53  % (3860)Refutation not found, incomplete strategy% (3860)------------------------------
% 1.32/0.53  % (3860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (3860)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (3860)Memory used [KB]: 1663
% 1.32/0.53  % (3860)Time elapsed: 0.123 s
% 1.32/0.53  % (3860)------------------------------
% 1.32/0.53  % (3860)------------------------------
% 1.32/0.53  % (3871)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.53  % (3884)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.53  % (3887)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.53  % (3863)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.53  % (3887)Refutation not found, incomplete strategy% (3887)------------------------------
% 1.32/0.53  % (3887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (3887)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (3887)Memory used [KB]: 6268
% 1.32/0.53  % (3887)Time elapsed: 0.132 s
% 1.32/0.53  % (3887)------------------------------
% 1.32/0.53  % (3887)------------------------------
% 1.32/0.53  % (3862)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.53  % (3865)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.54  % (3874)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.54  % (3879)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.32/0.54  % (3863)Refutation not found, incomplete strategy% (3863)------------------------------
% 1.32/0.54  % (3863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (3863)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (3863)Memory used [KB]: 10746
% 1.32/0.54  % (3863)Time elapsed: 0.126 s
% 1.32/0.54  % (3863)------------------------------
% 1.32/0.54  % (3863)------------------------------
% 1.32/0.54  % (3883)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.32/0.54  % (3862)Refutation not found, incomplete strategy% (3862)------------------------------
% 1.32/0.54  % (3862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (3862)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (3862)Memory used [KB]: 10746
% 1.32/0.54  % (3862)Time elapsed: 0.125 s
% 1.32/0.54  % (3862)------------------------------
% 1.32/0.54  % (3862)------------------------------
% 1.32/0.54  % (3865)Refutation not found, incomplete strategy% (3865)------------------------------
% 1.32/0.54  % (3865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (3865)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (3865)Memory used [KB]: 6268
% 1.32/0.54  % (3865)Time elapsed: 0.127 s
% 1.32/0.54  % (3865)------------------------------
% 1.32/0.54  % (3865)------------------------------
% 1.32/0.54  % (3868)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.32/0.54  % (3873)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.32/0.54  % (3879)Refutation not found, incomplete strategy% (3879)------------------------------
% 1.32/0.54  % (3879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (3879)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (3879)Memory used [KB]: 10746
% 1.32/0.54  % (3879)Time elapsed: 0.133 s
% 1.32/0.54  % (3879)------------------------------
% 1.32/0.54  % (3879)------------------------------
% 1.32/0.54  % (3868)Refutation not found, incomplete strategy% (3868)------------------------------
% 1.32/0.54  % (3868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (3868)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (3868)Memory used [KB]: 10746
% 1.32/0.54  % (3868)Time elapsed: 0.130 s
% 1.32/0.54  % (3868)------------------------------
% 1.32/0.54  % (3868)------------------------------
% 1.32/0.54  % (3871)Refutation not found, incomplete strategy% (3871)------------------------------
% 1.32/0.54  % (3871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (3871)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (3871)Memory used [KB]: 10746
% 1.32/0.54  % (3871)Time elapsed: 0.143 s
% 1.32/0.54  % (3871)------------------------------
% 1.32/0.54  % (3871)------------------------------
% 1.32/0.54  % (3878)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.54  % (3876)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.54  % (3877)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.54  % (3875)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.32/0.54  % (3877)Refutation not found, incomplete strategy% (3877)------------------------------
% 1.32/0.54  % (3877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (3877)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (3877)Memory used [KB]: 10618
% 1.32/0.54  % (3877)Time elapsed: 0.137 s
% 1.32/0.54  % (3877)------------------------------
% 1.32/0.54  % (3877)------------------------------
% 1.32/0.54  % SZS status CounterSatisfiable for theBenchmark
% 1.32/0.54  % (3876)# SZS output start Saturation.
% 1.32/0.54  tff(u137,negated_conjecture,
% 1.32/0.54      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_orders_2(sK0) = X1)))))).
% 1.32/0.54  
% 1.32/0.54  tff(u136,negated_conjecture,
% 1.32/0.54      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | (![X1, X0] : (((g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))) | (u1_struct_0(sK0) = X0)))))).
% 1.32/0.54  
% 1.32/0.54  tff(u135,negated_conjecture,
% 1.32/0.54      ((~(u1_struct_0(sK0) = u1_struct_0(sK1))) | (u1_struct_0(sK0) = u1_struct_0(sK1)))).
% 1.32/0.54  
% 1.32/0.54  tff(u134,negated_conjecture,
% 1.32/0.54      ((~(u1_orders_2(sK0) = u1_orders_2(sK1))) | (u1_orders_2(sK0) = u1_orders_2(sK1)))).
% 1.32/0.54  
% 1.32/0.54  tff(u133,axiom,
% 1.32/0.54      (![X0] : ((~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))))).
% 1.32/0.54  
% 1.32/0.54  tff(u132,negated_conjecture,
% 1.32/0.54      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 1.32/0.54  
% 1.32/0.54  tff(u131,negated_conjecture,
% 1.32/0.54      ((~l1_orders_2(sK1)) | l1_orders_2(sK1))).
% 1.32/0.54  
% 1.32/0.54  tff(u130,axiom,
% 1.32/0.54      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X1 = X3))))).
% 1.32/0.54  
% 1.32/0.54  tff(u129,axiom,
% 1.32/0.54      (![X1, X3, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | (g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | (X0 = X2))))).
% 1.32/0.54  
% 1.32/0.54  tff(u128,negated_conjecture,
% 1.32/0.54      ((~m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))).
% 1.32/0.54  
% 1.32/0.54  tff(u127,axiom,
% 1.32/0.54      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0))))).
% 1.32/0.54  
% 1.32/0.54  tff(u126,axiom,
% 1.32/0.54      (![X1, X0, X2] : ((~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2))))).
% 1.32/0.54  
% 1.32/0.54  tff(u125,negated_conjecture,
% 1.32/0.54      ((~(![X1, X0] : ((~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))))) | (![X1, X0] : ((~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))))))).
% 1.32/0.54  
% 1.32/0.54  tff(u124,negated_conjecture,
% 1.32/0.54      ((~~r1_yellow_0(sK1,sK2)) | ~r1_yellow_0(sK1,sK2))).
% 1.32/0.54  
% 1.32/0.54  tff(u123,negated_conjecture,
% 1.32/0.54      ((~r1_yellow_0(sK0,sK2)) | r1_yellow_0(sK0,sK2))).
% 1.32/0.54  
% 1.32/0.54  tff(u122,negated_conjecture,
% 1.32/0.54      ((~~r2_yellow_0(sK1,sK2)) | ~r2_yellow_0(sK1,sK2))).
% 1.32/0.54  
% 1.32/0.54  % (3876)# SZS output end Saturation.
% 1.32/0.54  % (3876)------------------------------
% 1.32/0.54  % (3876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (3876)Termination reason: Satisfiable
% 1.32/0.54  
% 1.32/0.54  % (3876)Memory used [KB]: 10746
% 1.32/0.54  % (3876)Time elapsed: 0.138 s
% 1.32/0.54  % (3876)------------------------------
% 1.32/0.54  % (3876)------------------------------
% 1.32/0.54  % (3875)Refutation not found, incomplete strategy% (3875)------------------------------
% 1.32/0.54  % (3875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (3875)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (3875)Memory used [KB]: 6140
% 1.32/0.54  % (3875)Time elapsed: 0.107 s
% 1.32/0.54  % (3875)------------------------------
% 1.32/0.54  % (3875)------------------------------
% 1.32/0.54  % (3866)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.55  % (3889)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.55  % (3859)Success in time 0.184 s
%------------------------------------------------------------------------------
