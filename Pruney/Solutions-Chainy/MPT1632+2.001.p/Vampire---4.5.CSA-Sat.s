%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:56 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    0
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u65,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u64,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u63,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u62,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u61,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u60,negated_conjecture,(
    l1_waybel_0(sK1,sK0) )).

tff(u59,negated_conjecture,
    ( ~ ~ v11_waybel_0(sK1,sK0)
    | ~ v11_waybel_0(sK1,sK0) )).

tff(u58,negated_conjecture,
    ( ~ ! [X5] :
          ( m1_subset_1(sK4(X5),u1_struct_0(sK1))
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
    | ! [X5] :
        ( m1_subset_1(sK4(X5),u1_struct_0(sK1))
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) )).

tff(u57,negated_conjecture,
    ( ~ ! [X5,X7] :
          ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5))
          | ~ m1_subset_1(X5,u1_struct_0(sK1))
          | ~ m1_subset_1(X7,u1_struct_0(sK1))
          | ~ r1_orders_2(sK1,sK4(X5),X7) )
    | ! [X5,X7] :
        ( r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5))
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ m1_subset_1(X7,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK4(X5),X7) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:35:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (878)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.48  % (886)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.49  % (879)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.49  % (890)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (886)Refutation not found, incomplete strategy% (886)------------------------------
% 0.21/0.50  % (886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (886)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (886)Memory used [KB]: 9850
% 0.21/0.50  % (886)Time elapsed: 0.070 s
% 0.21/0.50  % (886)------------------------------
% 0.21/0.50  % (886)------------------------------
% 0.21/0.51  % (882)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.51  % (882)Refutation not found, incomplete strategy% (882)------------------------------
% 0.21/0.51  % (882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (882)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (882)Memory used [KB]: 895
% 0.21/0.51  % (882)Time elapsed: 0.088 s
% 0.21/0.51  % (882)------------------------------
% 0.21/0.51  % (882)------------------------------
% 0.21/0.51  % (880)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.51  % (887)WARNING: option uwaf not known.
% 0.21/0.52  % (880)Refutation not found, incomplete strategy% (880)------------------------------
% 0.21/0.52  % (880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (880)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (880)Memory used [KB]: 9850
% 0.21/0.52  % (880)Time elapsed: 0.082 s
% 0.21/0.52  % (880)------------------------------
% 0.21/0.52  % (880)------------------------------
% 0.21/0.52  % (887)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.52  % (877)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (893)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.52  % (877)Refutation not found, incomplete strategy% (877)------------------------------
% 0.21/0.52  % (877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (877)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (877)Memory used [KB]: 5245
% 0.21/0.52  % (877)Time elapsed: 0.072 s
% 0.21/0.52  % (877)------------------------------
% 0.21/0.52  % (877)------------------------------
% 0.21/0.52  % (893)Refutation not found, incomplete strategy% (893)------------------------------
% 0.21/0.52  % (893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (893)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (893)Memory used [KB]: 767
% 0.21/0.52  % (893)Time elapsed: 0.041 s
% 0.21/0.52  % (893)------------------------------
% 0.21/0.52  % (893)------------------------------
% 0.21/0.52  % (889)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.21/0.53  % (896)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (897)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.53  % (888)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (897)# SZS output start Saturation.
% 0.21/0.53  tff(u65,axiom,
% 0.21/0.53      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.21/0.53  
% 0.21/0.53  tff(u64,negated_conjecture,
% 0.21/0.53      l1_orders_2(sK0)).
% 0.21/0.53  
% 0.21/0.53  tff(u63,negated_conjecture,
% 0.21/0.53      l1_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  tff(u62,negated_conjecture,
% 0.21/0.53      ~v2_struct_0(sK0)).
% 0.21/0.53  
% 0.21/0.53  tff(u61,negated_conjecture,
% 0.21/0.53      ~v2_struct_0(sK1)).
% 0.21/0.53  
% 0.21/0.53  tff(u60,negated_conjecture,
% 0.21/0.53      l1_waybel_0(sK1,sK0)).
% 0.21/0.53  
% 0.21/0.53  tff(u59,negated_conjecture,
% 0.21/0.53      ((~~v11_waybel_0(sK1,sK0)) | ~v11_waybel_0(sK1,sK0))).
% 0.21/0.53  
% 0.21/0.53  tff(u58,negated_conjecture,
% 0.21/0.53      ((~(![X5] : ((m1_subset_1(sK4(X5),u1_struct_0(sK1)) | ~m1_subset_1(X5,u1_struct_0(sK1)))))) | (![X5] : ((m1_subset_1(sK4(X5),u1_struct_0(sK1)) | ~m1_subset_1(X5,u1_struct_0(sK1))))))).
% 0.21/0.53  
% 0.21/0.53  tff(u57,negated_conjecture,
% 0.21/0.53      ((~(![X5, X7] : ((r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_subset_1(X7,u1_struct_0(sK1)) | ~r1_orders_2(sK1,sK4(X5),X7))))) | (![X5, X7] : ((r1_orders_2(sK0,k2_waybel_0(sK0,sK1,X7),k2_waybel_0(sK0,sK1,X5)) | ~m1_subset_1(X5,u1_struct_0(sK1)) | ~m1_subset_1(X7,u1_struct_0(sK1)) | ~r1_orders_2(sK1,sK4(X5),X7)))))).
% 0.21/0.53  
% 0.21/0.53  % (897)# SZS output end Saturation.
% 0.21/0.53  % (897)------------------------------
% 0.21/0.53  % (897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (897)Termination reason: Satisfiable
% 0.21/0.53  
% 0.21/0.53  % (897)Memory used [KB]: 5373
% 0.21/0.53  % (897)Time elapsed: 0.090 s
% 0.21/0.53  % (897)------------------------------
% 0.21/0.53  % (897)------------------------------
% 0.21/0.53  % (888)Refutation not found, incomplete strategy% (888)------------------------------
% 0.21/0.53  % (888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (888)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (888)Memory used [KB]: 5373
% 0.21/0.53  % (888)Time elapsed: 0.094 s
% 0.21/0.53  % (888)------------------------------
% 0.21/0.53  % (888)------------------------------
% 0.21/0.53  % (876)Success in time 0.167 s
%------------------------------------------------------------------------------
