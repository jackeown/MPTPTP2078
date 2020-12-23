%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:59 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   11 (  11 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    0
%              Number of atoms          :   38 (  38 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u83,negated_conjecture,
    ( ~ ( sK1 != sK2 )
    | sK1 != sK2 )).

tff(u82,negated_conjecture,
    ( k5_waybel_0(sK0,sK1) != k5_waybel_0(sK0,sK2)
    | k5_waybel_0(sK0,sK1) = k5_waybel_0(sK0,sK2) )).

tff(u81,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u80,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | v3_orders_2(sK0) )).

tff(u79,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u78,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u77,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u76,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ r1_orders_2(sK0,X0,X1)
          | ~ r1_orders_2(sK0,X1,X0)
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | ~ m1_subset_1(X1,u1_struct_0(sK0))
          | X0 = X1 )
    | ! [X1,X0] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | X0 = X1 ) )).

tff(u75,axiom,(
    ! [X1,X0] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u74,axiom,(
    ! [X1,X0,X2] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2 ) )).

tff(u73,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | v5_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:56:50 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.46  % (18945)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.47  % (18953)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.47  % (18958)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (18945)Refutation not found, incomplete strategy% (18945)------------------------------
% 0.20/0.47  % (18945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (18945)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (18945)Memory used [KB]: 10618
% 0.20/0.47  % (18945)Time elapsed: 0.060 s
% 0.20/0.47  % (18945)------------------------------
% 0.20/0.47  % (18945)------------------------------
% 0.20/0.47  % (18958)Refutation not found, incomplete strategy% (18958)------------------------------
% 0.20/0.47  % (18958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (18958)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (18958)Memory used [KB]: 6140
% 0.20/0.47  % (18958)Time elapsed: 0.077 s
% 0.20/0.47  % (18958)------------------------------
% 0.20/0.47  % (18958)------------------------------
% 0.20/0.47  % (18953)Refutation not found, incomplete strategy% (18953)------------------------------
% 0.20/0.47  % (18953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (18953)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (18953)Memory used [KB]: 1663
% 0.20/0.47  % (18953)Time elapsed: 0.074 s
% 0.20/0.47  % (18953)------------------------------
% 0.20/0.47  % (18953)------------------------------
% 0.20/0.48  % (18947)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.48  % (18947)# SZS output start Saturation.
% 0.20/0.48  tff(u83,negated_conjecture,
% 0.20/0.48      ((~(sK1 != sK2)) | (sK1 != sK2))).
% 0.20/0.48  
% 0.20/0.48  tff(u82,negated_conjecture,
% 0.20/0.48      ((~(k5_waybel_0(sK0,sK1) = k5_waybel_0(sK0,sK2))) | (k5_waybel_0(sK0,sK1) = k5_waybel_0(sK0,sK2)))).
% 0.20/0.48  
% 0.20/0.48  tff(u81,negated_conjecture,
% 0.20/0.48      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u80,negated_conjecture,
% 0.20/0.48      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u79,negated_conjecture,
% 0.20/0.48      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u78,negated_conjecture,
% 0.20/0.48      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 0.20/0.48  
% 0.20/0.48  tff(u77,negated_conjecture,
% 0.20/0.48      ((~m1_subset_1(sK2,u1_struct_0(sK0))) | m1_subset_1(sK2,u1_struct_0(sK0)))).
% 0.20/0.48  
% 0.20/0.48  tff(u76,negated_conjecture,
% 0.20/0.48      ((~(![X1, X0] : ((~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | (X0 = X1))))) | (![X1, X0] : ((~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | (X0 = X1)))))).
% 0.20/0.48  
% 0.20/0.48  tff(u75,axiom,
% 0.20/0.48      (![X1, X0] : ((r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u74,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | (X1 = X2))))).
% 0.20/0.48  
% 0.20/0.48  tff(u73,negated_conjecture,
% 0.20/0.48      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 0.20/0.48  
% 0.20/0.48  % (18947)# SZS output end Saturation.
% 0.20/0.48  % (18947)------------------------------
% 0.20/0.48  % (18947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18947)Termination reason: Satisfiable
% 0.20/0.48  
% 0.20/0.48  % (18947)Memory used [KB]: 6140
% 0.20/0.48  % (18947)Time elapsed: 0.075 s
% 0.20/0.48  % (18947)------------------------------
% 0.20/0.48  % (18947)------------------------------
% 0.20/0.49  % (18950)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (18950)Refutation not found, incomplete strategy% (18950)------------------------------
% 0.20/0.49  % (18950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18950)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (18950)Memory used [KB]: 6012
% 0.20/0.49  % (18950)Time elapsed: 0.089 s
% 0.20/0.49  % (18950)------------------------------
% 0.20/0.49  % (18950)------------------------------
% 0.20/0.49  % (18951)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (18951)Refutation not found, incomplete strategy% (18951)------------------------------
% 0.20/0.49  % (18951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18951)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (18951)Memory used [KB]: 10618
% 0.20/0.49  % (18951)Time elapsed: 0.095 s
% 0.20/0.49  % (18951)------------------------------
% 0.20/0.49  % (18951)------------------------------
% 0.20/0.49  % (18963)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.49  % (18963)Refutation not found, incomplete strategy% (18963)------------------------------
% 0.20/0.49  % (18963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18963)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (18963)Memory used [KB]: 1663
% 0.20/0.49  % (18963)Time elapsed: 0.098 s
% 0.20/0.49  % (18963)------------------------------
% 0.20/0.49  % (18963)------------------------------
% 0.20/0.49  % (18946)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (18961)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.49  % (18957)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (18944)Success in time 0.146 s
%------------------------------------------------------------------------------
