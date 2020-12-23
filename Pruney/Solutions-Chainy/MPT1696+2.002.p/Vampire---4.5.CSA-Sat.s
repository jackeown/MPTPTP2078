%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:25 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    0
%              Number of atoms          :   42 (  42 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u43,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u42,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u41,axiom,(
    ! [X1,X0] :
      ( ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,sK2(X0,X1))
      | ~ v5_orders_2(X0) ) )).

tff(u40,axiom,(
    ! [X1,X0] :
      ( ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ v5_orders_2(X0) ) )).

tff(u39,negated_conjecture,
    ( ~ ~ v25_waybel_0(sK0)
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X1)
        | r2_yellow_0(sK0,X1) ) )).

tff(u38,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X1) ) )).

tff(u37,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1) ) )).

tff(u36,axiom,(
    ! [X1,X3,X0] :
      ( ~ r1_lattice3(X0,X1,X3)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_orders_2(X0,X3,sK2(X0,X1))
      | ~ r2_yellow_0(X0,X1) ) )).

tff(u35,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,X1) ) )).

tff(u34,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u33,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u32,negated_conjecture,
    ( ~ ~ v25_waybel_0(sK0)
    | ~ v25_waybel_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (4794)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.20/0.47  % (4805)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.47  % (4805)Refutation not found, incomplete strategy% (4805)------------------------------
% 0.20/0.47  % (4805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (4791)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.20/0.47  % (4805)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  % (4797)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.47  
% 0.20/0.47  % (4805)Memory used [KB]: 5373
% 0.20/0.47  % (4805)Time elapsed: 0.053 s
% 0.20/0.47  % (4805)------------------------------
% 0.20/0.47  % (4805)------------------------------
% 0.20/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.47  % (4797)# SZS output start Saturation.
% 0.20/0.47  tff(u43,negated_conjecture,
% 0.20/0.47      v5_orders_2(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u42,negated_conjecture,
% 0.20/0.47      l1_orders_2(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u41,axiom,
% 0.20/0.47      (![X1, X0] : ((~r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,sK2(X0,X1)) | ~v5_orders_2(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u40,axiom,
% 0.20/0.47      (![X1, X0] : ((~r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~v5_orders_2(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u39,negated_conjecture,
% 0.20/0.47      ((~~v25_waybel_0(sK0)) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1) | r2_yellow_0(sK0,X1)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u38,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | r1_lattice3(X0,X1,sK3(X0,X1,X2)) | r2_yellow_0(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u37,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_yellow_0(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u36,axiom,
% 0.20/0.47      (![X1, X3, X0] : ((~r1_lattice3(X0,X1,X3) | ~l1_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_orders_2(X0) | r1_orders_2(X0,X3,sK2(X0,X1)) | ~r2_yellow_0(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u35,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~r1_orders_2(X0,sK3(X0,X1,X2),X2) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~v5_orders_2(X0) | r2_yellow_0(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u34,negated_conjecture,
% 0.20/0.47      ~v2_struct_0(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u33,negated_conjecture,
% 0.20/0.47      v3_orders_2(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u32,negated_conjecture,
% 0.20/0.47      ((~~v25_waybel_0(sK0)) | ~v25_waybel_0(sK0))).
% 0.20/0.47  
% 0.20/0.47  % (4797)# SZS output end Saturation.
% 0.20/0.47  % (4797)------------------------------
% 0.20/0.47  % (4797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (4797)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (4797)Memory used [KB]: 5245
% 0.20/0.47  % (4797)Time elapsed: 0.050 s
% 0.20/0.47  % (4797)------------------------------
% 0.20/0.47  % (4797)------------------------------
% 0.20/0.48  % (4790)Success in time 0.116 s
%------------------------------------------------------------------------------
