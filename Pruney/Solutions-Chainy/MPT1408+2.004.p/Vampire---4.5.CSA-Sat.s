%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:29 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   29 (  29 expanded)
%              Depth                    :    0
%              Number of atoms          :  108 ( 108 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u191,negated_conjecture,
    ( ~ ( sK1 != sK2 )
    | sK1 != sK2 )).

tff(u190,negated_conjecture,
    ( k2_filter_0(sK0,sK1) != k2_filter_0(sK0,sK2)
    | k2_filter_0(sK0,sK1) = k2_filter_0(sK0,sK2) )).

tff(u189,negated_conjecture,
    ( ~ l3_lattices(sK0)
    | l3_lattices(sK0) )).

tff(u188,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u187,axiom,(
    ! [X1,X0,X2] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r3_lattices(X0,X1,X2) ) )).

tff(u186,negated_conjecture,
    ( ~ v10_lattices(sK0)
    | v10_lattices(sK0) )).

tff(u185,axiom,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) )).

tff(u184,axiom,(
    ! [X0] :
      ( v5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) )).

tff(u183,axiom,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) )).

tff(u182,negated_conjecture,
    ( ~ v6_lattices(sK0)
    | v6_lattices(sK0) )).

tff(u181,axiom,(
    ! [X0] :
      ( v7_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) )).

tff(u180,axiom,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) )).

tff(u179,negated_conjecture,
    ( ~ v8_lattices(sK0)
    | v8_lattices(sK0) )).

tff(u178,axiom,(
    ! [X1,X0,X2] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) )).

tff(u177,axiom,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) )).

tff(u176,negated_conjecture,
    ( ~ v9_lattices(sK0)
    | v9_lattices(sK0) )).

tff(u175,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) )).

tff(u174,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) )).

tff(u173,axiom,(
    ! [X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP3(X0) ) )).

% (28555)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (28555)Refutation not found, incomplete strategy% (28555)------------------------------
% (28555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28555)Termination reason: Refutation not found, incomplete strategy

% (28555)Memory used [KB]: 6140
% (28555)Time elapsed: 0.091 s
% (28555)------------------------------
% (28555)------------------------------
% (28559)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (28564)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (28567)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (28575)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (28566)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (28553)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (28561)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (28569)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (28563)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (28569)Refutation not found, incomplete strategy% (28569)------------------------------
% (28569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28568)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (28563)Refutation not found, incomplete strategy% (28563)------------------------------
% (28563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
tff(u172,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK0))
          | r1_lattices(sK0,X0,X0) )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,X0) ) )).

tff(u171,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u170,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u169,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ r3_lattices(sK0,X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(sK0))
          | r1_lattices(sK0,X1,X0)
          | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ! [X1,X0] :
        ( ~ r3_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u168,axiom,(
    ! [X1,X0] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) )).

tff(u167,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) )).

tff(u166,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattices(X0,X2,X1)
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) )).

tff(u165,negated_conjecture,
    ( ~ r1_lattices(sK0,sK1,sK1)
    | r1_lattices(sK0,sK1,sK1) )).

tff(u164,negated_conjecture,
    ( ~ r1_lattices(sK0,sK2,sK2)
    | r1_lattices(sK0,sK2,sK2) )).

tff(u163,negated_conjecture,
    ( ~ sP3(sK0)
    | sP3(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:52:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (28551)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (28558)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.50  % (28551)Refutation not found, incomplete strategy% (28551)------------------------------
% 0.20/0.50  % (28551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28551)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (28551)Memory used [KB]: 10618
% 0.20/0.50  % (28551)Time elapsed: 0.079 s
% 0.20/0.50  % (28551)------------------------------
% 0.20/0.50  % (28551)------------------------------
% 0.20/0.50  % (28554)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (28572)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (28552)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (28558)Refutation not found, incomplete strategy% (28558)------------------------------
% 0.20/0.50  % (28558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28558)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (28558)Memory used [KB]: 1663
% 0.20/0.50  % (28558)Time elapsed: 0.096 s
% 0.20/0.50  % (28558)------------------------------
% 0.20/0.50  % (28558)------------------------------
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (28552)# SZS output start Saturation.
% 0.20/0.51  tff(u191,negated_conjecture,
% 0.20/0.51      ((~(sK1 != sK2)) | (sK1 != sK2))).
% 0.20/0.51  
% 0.20/0.51  tff(u190,negated_conjecture,
% 0.20/0.51      ((~(k2_filter_0(sK0,sK1) = k2_filter_0(sK0,sK2))) | (k2_filter_0(sK0,sK1) = k2_filter_0(sK0,sK2)))).
% 0.20/0.51  
% 0.20/0.51  tff(u189,negated_conjecture,
% 0.20/0.51      ((~l3_lattices(sK0)) | l3_lattices(sK0))).
% 0.20/0.51  
% 0.20/0.51  tff(u188,negated_conjecture,
% 0.20/0.51      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  tff(u187,axiom,
% 0.20/0.51      (![X1, X0, X2] : ((~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | v2_struct_0(X0) | ~r3_lattices(X0,X1,X2))))).
% 0.20/0.51  
% 0.20/0.51  tff(u186,negated_conjecture,
% 0.20/0.51      ((~v10_lattices(sK0)) | v10_lattices(sK0))).
% 0.20/0.51  
% 0.20/0.51  tff(u185,axiom,
% 0.20/0.51      (![X0] : ((v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u184,axiom,
% 0.20/0.51      (![X0] : ((v5_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u183,axiom,
% 0.20/0.51      (![X0] : ((v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u182,negated_conjecture,
% 0.20/0.51      ((~v6_lattices(sK0)) | v6_lattices(sK0))).
% 0.20/0.51  
% 0.20/0.51  tff(u181,axiom,
% 0.20/0.51      (![X0] : ((v7_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u180,axiom,
% 0.20/0.51      (![X0] : ((v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u179,negated_conjecture,
% 0.20/0.51      ((~v8_lattices(sK0)) | v8_lattices(sK0))).
% 0.20/0.51  
% 0.20/0.51  tff(u178,axiom,
% 0.20/0.51      (![X1, X0, X2] : ((~v9_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u177,axiom,
% 0.20/0.51      (![X0] : ((v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u176,negated_conjecture,
% 0.20/0.51      ((~v9_lattices(sK0)) | v9_lattices(sK0))).
% 0.20/0.51  
% 0.20/0.51  tff(u175,axiom,
% 0.20/0.51      (![X0] : ((l1_lattices(X0) | ~l3_lattices(X0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u174,axiom,
% 0.20/0.51      (![X0] : ((l2_lattices(X0) | ~l3_lattices(X0))))).
% 0.20/0.51  
% 0.20/0.51  tff(u173,axiom,
% 0.20/0.51      (![X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP3(X0))))).
% 0.20/0.51  
% 0.20/0.51  % (28555)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (28555)Refutation not found, incomplete strategy% (28555)------------------------------
% 0.20/0.51  % (28555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28555)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (28555)Memory used [KB]: 6140
% 0.20/0.51  % (28555)Time elapsed: 0.091 s
% 0.20/0.51  % (28555)------------------------------
% 0.20/0.51  % (28555)------------------------------
% 0.20/0.51  % (28559)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (28564)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (28567)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (28575)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (28566)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (28553)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (28561)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (28569)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (28563)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (28569)Refutation not found, incomplete strategy% (28569)------------------------------
% 0.20/0.52  % (28569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (28568)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (28563)Refutation not found, incomplete strategy% (28563)------------------------------
% 0.20/0.52  % (28563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  tff(u172,negated_conjecture,
% 0.20/0.52      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X0))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X0)))))).
% 0.20/0.52  
% 0.20/0.52  tff(u171,negated_conjecture,
% 0.20/0.52      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 0.20/0.52  
% 0.20/0.52  tff(u170,negated_conjecture,
% 0.20/0.52      ((~m1_subset_1(sK2,u1_struct_0(sK0))) | m1_subset_1(sK2,u1_struct_0(sK0)))).
% 0.20/0.52  
% 0.20/0.52  tff(u169,negated_conjecture,
% 0.20/0.52      ((~(![X1, X0] : ((~r3_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))))) | (![X1, X0] : ((~r3_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 0.20/0.52  
% 0.20/0.52  tff(u168,axiom,
% 0.20/0.52      (![X1, X0] : ((r3_lattices(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u167,axiom,
% 0.20/0.52      (![X1, X0, X2] : ((~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u166,axiom,
% 0.20/0.52      (![X1, X0, X2] : ((~r1_lattices(X0,X2,X1) | (X1 = X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u165,negated_conjecture,
% 0.20/0.52      ((~r1_lattices(sK0,sK1,sK1)) | r1_lattices(sK0,sK1,sK1))).
% 0.20/0.52  
% 0.20/0.52  tff(u164,negated_conjecture,
% 0.20/0.52      ((~r1_lattices(sK0,sK2,sK2)) | r1_lattices(sK0,sK2,sK2))).
% 0.20/0.52  
% 0.20/0.52  tff(u163,negated_conjecture,
% 0.20/0.52      ((~sP3(sK0)) | sP3(sK0))).
% 0.20/0.52  
% 0.20/0.52  % (28552)# SZS output end Saturation.
% 0.20/0.52  % (28552)------------------------------
% 0.20/0.52  % (28552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (28552)Termination reason: Satisfiable
% 0.20/0.52  
% 0.20/0.52  % (28552)Memory used [KB]: 6268
% 0.20/0.52  % (28552)Time elapsed: 0.095 s
% 0.20/0.52  % (28552)------------------------------
% 0.20/0.52  % (28552)------------------------------
% 0.20/0.52  % (28563)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (28563)Memory used [KB]: 6140
% 0.20/0.52  % (28563)Time elapsed: 0.107 s
% 0.20/0.52  % (28563)------------------------------
% 0.20/0.52  % (28563)------------------------------
% 0.20/0.52  % (28561)Refutation not found, incomplete strategy% (28561)------------------------------
% 0.20/0.52  % (28561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (28561)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (28561)Memory used [KB]: 10490
% 0.20/0.52  % (28561)Time elapsed: 0.114 s
% 0.20/0.52  % (28561)------------------------------
% 0.20/0.52  % (28561)------------------------------
% 0.20/0.52  % (28569)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (28569)Memory used [KB]: 1663
% 0.20/0.52  % (28569)Time elapsed: 0.108 s
% 0.20/0.52  % (28569)------------------------------
% 0.20/0.52  % (28569)------------------------------
% 0.20/0.52  % (28549)Success in time 0.156 s
%------------------------------------------------------------------------------
