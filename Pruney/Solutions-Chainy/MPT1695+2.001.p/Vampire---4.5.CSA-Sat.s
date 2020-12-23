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
% DateTime   : Thu Dec  3 13:17:25 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of leaves         :   38 (  38 expanded)
%              Depth                    :    0
%              Number of atoms          :  191 ( 191 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   13 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u136,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u135,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u134,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u133,negated_conjecture,
    ( ~ ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u132,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
          | v1_xboole_0(X2)
          | ~ v1_waybel_0(X2,sK0)
          | r1_yellow_0(sK0,X2) )
    | ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X2)
        | ~ v1_waybel_0(X2,sK0)
        | r1_yellow_0(sK0,X2) ) )).

tff(u131,axiom,(
    ! [X0,X2] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,k1_yellow_0(X0,X2))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u130,axiom,(
    ! [X1,X0,X2] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u129,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u128,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u127,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u126,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | sK2(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u125,axiom,(
    ! [X1,X7,X0] :
      ( ~ r1_orders_2(X0,X7,sK5(X0,X1,X7))
      | sK4(X0,X1) = X7
      | ~ r2_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u124,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,sK6(X0,X1,X2))
      | k1_yellow_0(X0,X2) = X1
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

% (17677)Refutation not found, incomplete strategy% (17677)------------------------------
% (17677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
tff(u123,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,sK6(X0,X1,X2))
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u122,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,sK1)
    | ~ r1_yellow_0(sK0,sK1) )).

tff(u121,axiom,(
    ! [X1,X0] :
      ( ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK4(X0,X1))
      | ~ l1_orders_2(X0) ) )).

tff(u120,axiom,(
    ! [X1,X0] :
      ( ~ r1_yellow_0(X0,X1)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u119,axiom,(
    ! [X9,X1,X0] :
      ( ~ r2_lattice3(X0,X1,X9)
      | r1_orders_2(X0,sK4(X0,X1),X9)
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u118,axiom,(
    ! [X1,X7,X0] :
      ( ~ r2_lattice3(X0,X1,X7)
      | m1_subset_1(sK5(X0,X1,X7),u1_struct_0(X0))
      | sK4(X0,X1) = X7
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u117,axiom,(
    ! [X1,X7,X0] :
      ( ~ r2_lattice3(X0,X1,X7)
      | r2_lattice3(X0,X1,sK5(X0,X1,X7))
      | sK4(X0,X1) = X7
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u116,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u115,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u114,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u113,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u112,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r2_lattice3(X0,X1,X4)
      | r1_orders_2(X0,sK2(X0,X1,X2),X4)
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u111,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r2_lattice3(X0,X1,X4)
      | r1_orders_2(X0,sK2(X0,X1,X2),X4)
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u110,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r2_lattice3(X0,X1,X4)
      | r1_orders_2(X0,sK2(X0,X1,X2),X4)
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u109,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | sK2(X0,X1,X2) != X2
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u108,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | sK2(X0,X1,X2) != X2
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u107,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X2,X1)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X2) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u106,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X2,X1)
      | r2_lattice3(X0,X2,sK6(X0,X1,X2))
      | k1_yellow_0(X0,X2) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u105,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X2,X1)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u104,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X2,X1)
      | r2_lattice3(X0,X2,sK6(X0,X1,X2))
      | r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u103,axiom,(
    ! [X0,X2,X4] :
      ( ~ r2_lattice3(X0,X2,X4)
      | r1_orders_2(X0,k1_yellow_0(X0,X2),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u102,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u101,negated_conjecture,
    ( ~ ~ v24_waybel_0(sK0)
    | ~ v24_waybel_0(sK0) )).

tff(u100,negated_conjecture,
    ( ~ ~ v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK1) )).

tff(u99,negated_conjecture,
    ( ~ ~ v1_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:41:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (17675)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (17678)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (17674)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (17682)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.54  % (17691)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (17681)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.54  % (17694)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (17678)Refutation not found, incomplete strategy% (17678)------------------------------
% 0.21/0.54  % (17678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17678)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17678)Memory used [KB]: 10618
% 0.21/0.54  % (17678)Time elapsed: 0.113 s
% 0.21/0.54  % (17678)------------------------------
% 0.21/0.54  % (17678)------------------------------
% 0.21/0.54  % (17677)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (17695)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (17682)# SZS output start Saturation.
% 0.21/0.54  tff(u136,negated_conjecture,
% 0.21/0.54      ~v2_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  tff(u135,negated_conjecture,
% 0.21/0.54      v3_orders_2(sK0)).
% 0.21/0.54  
% 0.21/0.54  tff(u134,negated_conjecture,
% 0.21/0.54      l1_orders_2(sK0)).
% 0.21/0.54  
% 0.21/0.54  tff(u133,negated_conjecture,
% 0.21/0.54      ((~~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u132,negated_conjecture,
% 0.21/0.54      ((~(![X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X2) | ~v1_waybel_0(X2,sK0) | r1_yellow_0(sK0,X2))))) | (![X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X2) | ~v1_waybel_0(X2,sK0) | r1_yellow_0(sK0,X2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u131,axiom,
% 0.21/0.54      (![X0, X2] : ((~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~r1_yellow_0(X0,X2) | r2_lattice3(X0,X2,k1_yellow_0(X0,X2)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u130,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u129,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u128,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | r2_lattice3(X0,X1,sK2(X0,X1,X2)) | r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u127,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u126,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | (sK2(X0,X1,X2) != X2) | r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u125,axiom,
% 0.21/0.54      (![X1, X7, X0] : ((~r1_orders_2(X0,X7,sK5(X0,X1,X7)) | (sK4(X0,X1) = X7) | ~r2_lattice3(X0,X1,X7) | ~m1_subset_1(X7,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u124,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,sK6(X0,X1,X2)) | (k1_yellow_0(X0,X2) = X1) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  % (17677)Refutation not found, incomplete strategy% (17677)------------------------------
% 0.21/0.54  % (17677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  tff(u123,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,sK6(X0,X1,X2)) | r1_yellow_0(X0,X2) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u122,negated_conjecture,
% 0.21/0.54      ((~~r1_yellow_0(sK0,sK1)) | ~r1_yellow_0(sK0,sK1))).
% 0.21/0.54  
% 0.21/0.54  tff(u121,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_yellow_0(X0,X1) | r2_lattice3(X0,X1,sK4(X0,X1)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u120,axiom,
% 0.21/0.54      (![X1, X0] : ((~r1_yellow_0(X0,X1) | m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u119,axiom,
% 0.21/0.54      (![X9, X1, X0] : ((~r2_lattice3(X0,X1,X9) | r1_orders_2(X0,sK4(X0,X1),X9) | ~m1_subset_1(X9,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u118,axiom,
% 0.21/0.54      (![X1, X7, X0] : ((~r2_lattice3(X0,X1,X7) | m1_subset_1(sK5(X0,X1,X7),u1_struct_0(X0)) | (sK4(X0,X1) = X7) | ~m1_subset_1(X7,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u117,axiom,
% 0.21/0.54      (![X1, X7, X0] : ((~r2_lattice3(X0,X1,X7) | r2_lattice3(X0,X1,sK5(X0,X1,X7)) | (sK4(X0,X1) = X7) | ~m1_subset_1(X7,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u116,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u115,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,sK3(X0,X1,X2)) | r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u114,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | r2_lattice3(X0,X1,sK2(X0,X1,X2)) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u113,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | r2_lattice3(X0,X1,sK2(X0,X1,X2)) | r2_lattice3(X0,X1,sK3(X0,X1,X2)) | r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u112,axiom,
% 0.21/0.54      (![X1, X0, X2, X4] : ((~r2_lattice3(X0,X1,X4) | r1_orders_2(X0,sK2(X0,X1,X2),X4) | r1_yellow_0(X0,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u111,axiom,
% 0.21/0.54      (![X1, X0, X2, X4] : ((~r2_lattice3(X0,X1,X4) | r1_orders_2(X0,sK2(X0,X1,X2),X4) | r1_yellow_0(X0,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r2_lattice3(X0,X1,sK3(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u110,axiom,
% 0.21/0.54      (![X1, X0, X2, X4] : ((~r2_lattice3(X0,X1,X4) | r1_orders_2(X0,sK2(X0,X1,X2),X4) | r1_yellow_0(X0,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u109,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | (sK2(X0,X1,X2) != X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u108,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | (sK2(X0,X1,X2) != X2) | r2_lattice3(X0,X1,sK3(X0,X1,X2)) | r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u107,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X2,X1) | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | (k1_yellow_0(X0,X2) = X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u106,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X2,X1) | r2_lattice3(X0,X2,sK6(X0,X1,X2)) | (k1_yellow_0(X0,X2) = X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u105,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X2,X1) | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u104,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~r2_lattice3(X0,X2,X1) | r2_lattice3(X0,X2,sK6(X0,X1,X2)) | r1_yellow_0(X0,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u103,axiom,
% 0.21/0.54      (![X0, X2, X4] : ((~r2_lattice3(X0,X2,X4) | r1_orders_2(X0,k1_yellow_0(X0,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X2) | ~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u102,negated_conjecture,
% 0.21/0.54      v5_orders_2(sK0)).
% 0.21/0.54  
% 0.21/0.54  tff(u101,negated_conjecture,
% 0.21/0.54      ((~~v24_waybel_0(sK0)) | ~v24_waybel_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  tff(u100,negated_conjecture,
% 0.21/0.54      ((~~v1_xboole_0(sK1)) | ~v1_xboole_0(sK1))).
% 0.21/0.54  
% 0.21/0.54  tff(u99,negated_conjecture,
% 0.21/0.54      ((~~v1_waybel_0(sK1,sK0)) | ~v1_waybel_0(sK1,sK0))).
% 0.21/0.54  
% 0.21/0.54  % (17682)# SZS output end Saturation.
% 0.21/0.54  % (17682)------------------------------
% 0.21/0.54  % (17682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17682)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (17682)Memory used [KB]: 10618
% 0.21/0.54  % (17682)Time elapsed: 0.122 s
% 0.21/0.54  % (17682)------------------------------
% 0.21/0.54  % (17682)------------------------------
% 0.21/0.55  % (17671)Success in time 0.186 s
%------------------------------------------------------------------------------
