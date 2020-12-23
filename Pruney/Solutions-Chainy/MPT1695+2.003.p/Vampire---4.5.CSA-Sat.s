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
% DateTime   : Thu Dec  3 13:17:25 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    0
%              Number of atoms          :   57 (  57 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u51,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u50,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u49,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u48,negated_conjecture,
    ( ~ ~ v24_waybel_0(sK0)
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_0(X1,sK0)
        | v1_xboole_0(X1)
        | r1_yellow_0(sK0,X1) ) )).

tff(u47,axiom,(
    ! [X1,X0,X2] :
      ( ~ r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) )).

tff(u46,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,X1) ) )).

tff(u45,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_orders_2(X0,X1,X2) ) )).

tff(u44,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u43,axiom,(
    ! [X1,X0] :
      ( ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK2(X0,X1))
      | ~ v5_orders_2(X0) ) )).

tff(u42,axiom,(
    ! [X1,X0] :
      ( ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ v5_orders_2(X0) ) )).

tff(u41,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | r1_yellow_0(X0,X1) ) )).

tff(u40,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1) ) )).

tff(u39,axiom,(
    ! [X1,X3,X0] :
      ( ~ r2_lattice3(X0,X1,X3)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_orders_2(X0,sK2(X0,X1),X3)
      | ~ r1_yellow_0(X0,X1) ) )).

tff(u38,negated_conjecture,
    ( ~ ~ v24_waybel_0(sK0)
    | ~ v24_waybel_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:00 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.45  % (17604)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  % (17596)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.47  % (17596)Refutation not found, incomplete strategy% (17596)------------------------------
% 0.20/0.47  % (17596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (17596)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (17596)Memory used [KB]: 895
% 0.20/0.47  % (17596)Time elapsed: 0.072 s
% 0.20/0.47  % (17596)------------------------------
% 0.20/0.47  % (17596)------------------------------
% 0.20/0.47  % (17605)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.48  % (17593)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.20/0.48  % (17608)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.20/0.48  % (17608)Refutation not found, incomplete strategy% (17608)------------------------------
% 0.20/0.48  % (17608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17608)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (17608)Memory used [KB]: 9850
% 0.20/0.48  % (17608)Time elapsed: 0.039 s
% 0.20/0.48  % (17608)------------------------------
% 0.20/0.48  % (17608)------------------------------
% 0.20/0.48  % (17592)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.20/0.49  % (17601)WARNING: option uwaf not known.
% 0.20/0.49  % (17603)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.20/0.49  % (17601)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.20/0.49  % (17598)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.49  % (17601)Refutation not found, incomplete strategy% (17601)------------------------------
% 0.20/0.49  % (17601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (17601)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (17601)Memory used [KB]: 895
% 0.20/0.49  % (17601)Time elapsed: 0.074 s
% 0.20/0.49  % (17601)------------------------------
% 0.20/0.49  % (17601)------------------------------
% 0.20/0.49  % (17605)Refutation not found, incomplete strategy% (17605)------------------------------
% 0.20/0.49  % (17605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (17605)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (17605)Memory used [KB]: 5373
% 0.20/0.49  % (17605)Time elapsed: 0.063 s
% 0.20/0.49  % (17605)------------------------------
% 0.20/0.49  % (17605)------------------------------
% 0.20/0.49  % (17606)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.49  % (17597)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.49  % (17606)Refutation not found, incomplete strategy% (17606)------------------------------
% 0.20/0.49  % (17606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (17606)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (17606)Memory used [KB]: 895
% 0.20/0.49  % (17606)Time elapsed: 0.085 s
% 0.20/0.49  % (17606)------------------------------
% 0.20/0.49  % (17606)------------------------------
% 0.20/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.49  % (17597)# SZS output start Saturation.
% 0.20/0.49  tff(u51,negated_conjecture,
% 0.20/0.49      ~v2_struct_0(sK0)).
% 0.20/0.49  
% 0.20/0.49  tff(u50,negated_conjecture,
% 0.20/0.49      v3_orders_2(sK0)).
% 0.20/0.49  
% 0.20/0.49  tff(u49,negated_conjecture,
% 0.20/0.49      l1_orders_2(sK0)).
% 0.20/0.49  
% 0.20/0.49  tff(u48,negated_conjecture,
% 0.20/0.49      ((~~v24_waybel_0(sK0)) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_waybel_0(X1,sK0) | v1_xboole_0(X1) | r1_yellow_0(sK0,X1)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u47,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((~r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u46,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~v5_orders_2(X0) | r1_yellow_0(X0,X1))))).
% 0.20/0.49  
% 0.20/0.49  tff(u45,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_orders_2(X0,X1,X2))))).
% 0.20/0.49  
% 0.20/0.49  tff(u44,negated_conjecture,
% 0.20/0.49      v5_orders_2(sK0)).
% 0.20/0.49  
% 0.20/0.49  tff(u43,axiom,
% 0.20/0.49      (![X1, X0] : ((~r1_yellow_0(X0,X1) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,sK2(X0,X1)) | ~v5_orders_2(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u42,axiom,
% 0.20/0.49      (![X1, X0] : ((~r1_yellow_0(X0,X1) | ~l1_orders_2(X0) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~v5_orders_2(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u41,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | r2_lattice3(X0,X1,sK3(X0,X1,X2)) | r1_yellow_0(X0,X1))))).
% 0.20/0.49  
% 0.20/0.49  tff(u40,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((~r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X1))))).
% 0.20/0.49  
% 0.20/0.49  tff(u39,axiom,
% 0.20/0.49      (![X1, X3, X0] : ((~r2_lattice3(X0,X1,X3) | ~l1_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | r1_orders_2(X0,sK2(X0,X1),X3) | ~r1_yellow_0(X0,X1))))).
% 0.20/0.49  
% 0.20/0.49  tff(u38,negated_conjecture,
% 0.20/0.49      ((~~v24_waybel_0(sK0)) | ~v24_waybel_0(sK0))).
% 0.20/0.49  
% 0.20/0.49  % (17597)# SZS output end Saturation.
% 0.20/0.49  % (17597)------------------------------
% 0.20/0.49  % (17597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (17597)Termination reason: Satisfiable
% 0.20/0.49  
% 0.20/0.49  % (17597)Memory used [KB]: 5373
% 0.20/0.49  % (17597)Time elapsed: 0.071 s
% 0.20/0.49  % (17597)------------------------------
% 0.20/0.49  % (17597)------------------------------
% 0.20/0.49  % (17602)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.20/0.49  % (17590)Success in time 0.134 s
%------------------------------------------------------------------------------
