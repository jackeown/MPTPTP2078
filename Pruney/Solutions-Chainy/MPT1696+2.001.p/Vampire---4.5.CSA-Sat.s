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

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   33 (  33 expanded)
%              Depth                    :    0
%              Number of atoms          :  171 ( 171 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   13 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u119,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u118,negated_conjecture,
    ( ~ ~ r2_yellow_0(sK0,sK1)
    | ~ r2_yellow_0(sK0,sK1) )).

tff(u117,axiom,(
    ! [X1,X0] :
      ( ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,sK4(X0,X1))
      | ~ l1_orders_2(X0) ) )).

tff(u116,axiom,(
    ! [X1,X0] :
      ( ~ r2_yellow_0(X0,X1)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u115,negated_conjecture,
    ( ~ ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u114,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
          | v1_xboole_0(X2)
          | r2_yellow_0(sK0,X2) )
    | ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X2)
        | r2_yellow_0(sK0,X2) ) )).

tff(u113,axiom,(
    ! [X0,X2] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,k2_yellow_0(X0,X2))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u112,axiom,(
    ! [X9,X1,X0] :
      ( ~ r1_lattice3(X0,X1,X9)
      | r1_orders_2(X0,X9,sK4(X0,X1))
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u111,axiom,(
    ! [X1,X7,X0] :
      ( ~ r1_lattice3(X0,X1,X7)
      | m1_subset_1(sK5(X0,X1,X7),u1_struct_0(X0))
      | sK4(X0,X1) = X7
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u110,axiom,(
    ! [X1,X7,X0] :
      ( ~ r1_lattice3(X0,X1,X7)
      | r1_lattice3(X0,X1,sK5(X0,X1,X7))
      | sK4(X0,X1) = X7
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u109,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u108,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u107,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u106,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u105,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r1_lattice3(X0,X1,X4)
      | r1_orders_2(X0,X4,sK2(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u104,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r1_lattice3(X0,X1,X4)
      | r1_orders_2(X0,X4,sK2(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u103,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r1_lattice3(X0,X1,X4)
      | r1_orders_2(X0,X4,sK2(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u102,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | sK2(X0,X1,X2) != X2
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u101,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X1,X2)
      | sK2(X0,X1,X2) != X2
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u100,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X2,X1)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X2) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u99,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X2,X1)
      | r1_lattice3(X0,X2,sK6(X0,X1,X2))
      | k2_yellow_0(X0,X2) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u98,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X2,X1)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u97,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(X0,X2,X1)
      | r1_lattice3(X0,X2,sK6(X0,X1,X2))
      | r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u96,axiom,(
    ! [X0,X2,X4] :
      ( ~ r1_lattice3(X0,X2,X4)
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X2))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u95,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X1)
      | k2_yellow_0(X0,X2) = X1
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u94,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X1)
      | r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u93,axiom,(
    ! [X1,X7,X0] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X7),X7)
      | sK4(X0,X1) = X7
      | ~ r1_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) )).

tff(u92,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u91,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u90,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | sK2(X0,X1,X2) != X2
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u89,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u88,negated_conjecture,
    ( ~ ~ v25_waybel_0(sK0)
    | ~ v25_waybel_0(sK0) )).

tff(u87,negated_conjecture,
    ( ~ ~ v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:51:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (19025)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (19025)# SZS output start Saturation.
% 0.22/0.51  tff(u119,negated_conjecture,
% 0.22/0.51      l1_orders_2(sK0)).
% 0.22/0.51  
% 0.22/0.51  tff(u118,negated_conjecture,
% 0.22/0.51      ((~~r2_yellow_0(sK0,sK1)) | ~r2_yellow_0(sK0,sK1))).
% 0.22/0.51  
% 0.22/0.51  tff(u117,axiom,
% 0.22/0.51      (![X1, X0] : ((~r2_yellow_0(X0,X1) | r1_lattice3(X0,X1,sK4(X0,X1)) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u116,axiom,
% 0.22/0.51      (![X1, X0] : ((~r2_yellow_0(X0,X1) | m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u115,negated_conjecture,
% 0.22/0.51      ((~~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u114,negated_conjecture,
% 0.22/0.51      ((~(![X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X2) | r2_yellow_0(sK0,X2))))) | (![X2] : ((~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X2) | r2_yellow_0(sK0,X2)))))).
% 0.22/0.51  
% 0.22/0.51  tff(u113,axiom,
% 0.22/0.51      (![X0, X2] : ((~m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0)) | ~r2_yellow_0(X0,X2) | r1_lattice3(X0,X2,k2_yellow_0(X0,X2)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u112,axiom,
% 0.22/0.51      (![X9, X1, X0] : ((~r1_lattice3(X0,X1,X9) | r1_orders_2(X0,X9,sK4(X0,X1)) | ~m1_subset_1(X9,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u111,axiom,
% 0.22/0.51      (![X1, X7, X0] : ((~r1_lattice3(X0,X1,X7) | m1_subset_1(sK5(X0,X1,X7),u1_struct_0(X0)) | (sK4(X0,X1) = X7) | ~m1_subset_1(X7,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u110,axiom,
% 0.22/0.51      (![X1, X7, X0] : ((~r1_lattice3(X0,X1,X7) | r1_lattice3(X0,X1,sK5(X0,X1,X7)) | (sK4(X0,X1) = X7) | ~m1_subset_1(X7,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u109,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u108,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,sK3(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u107,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | r1_lattice3(X0,X1,sK2(X0,X1,X2)) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u106,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | r1_lattice3(X0,X1,sK2(X0,X1,X2)) | r1_lattice3(X0,X1,sK3(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u105,axiom,
% 0.22/0.51      (![X1, X0, X2, X4] : ((~r1_lattice3(X0,X1,X4) | r1_orders_2(X0,X4,sK2(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u104,axiom,
% 0.22/0.51      (![X1, X0, X2, X4] : ((~r1_lattice3(X0,X1,X4) | r1_orders_2(X0,X4,sK2(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_lattice3(X0,X1,sK3(X0,X1,X2)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u103,axiom,
% 0.22/0.51      (![X1, X0, X2, X4] : ((~r1_lattice3(X0,X1,X4) | r1_orders_2(X0,X4,sK2(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_orders_2(X0,sK3(X0,X1,X2),X2) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u102,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | (sK2(X0,X1,X2) != X2) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u101,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r1_lattice3(X0,X1,X2) | (sK2(X0,X1,X2) != X2) | r1_lattice3(X0,X1,sK3(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u100,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r1_lattice3(X0,X2,X1) | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | (k2_yellow_0(X0,X2) = X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u99,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r1_lattice3(X0,X2,X1) | r1_lattice3(X0,X2,sK6(X0,X1,X2)) | (k2_yellow_0(X0,X2) = X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u98,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r1_lattice3(X0,X2,X1) | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | r2_yellow_0(X0,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u97,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r1_lattice3(X0,X2,X1) | r1_lattice3(X0,X2,sK6(X0,X1,X2)) | r2_yellow_0(X0,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u96,axiom,
% 0.22/0.51      (![X0, X2, X4] : ((~r1_lattice3(X0,X2,X4) | r1_orders_2(X0,X4,k2_yellow_0(X0,X2)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X2) | ~m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u95,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r1_orders_2(X0,sK6(X0,X1,X2),X1) | (k2_yellow_0(X0,X2) = X1) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u94,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r1_orders_2(X0,sK6(X0,X1,X2),X1) | r2_yellow_0(X0,X2) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u93,axiom,
% 0.22/0.51      (![X1, X7, X0] : ((~r1_orders_2(X0,sK5(X0,X1,X7),X7) | (sK4(X0,X1) = X7) | ~r1_lattice3(X0,X1,X7) | ~m1_subset_1(X7,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u92,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r1_orders_2(X0,sK3(X0,X1,X2),X2) | r1_lattice3(X0,X1,sK2(X0,X1,X2)) | r2_yellow_0(X0,X1) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u91,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r1_orders_2(X0,sK3(X0,X1,X2),X2) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r2_yellow_0(X0,X1) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u90,axiom,
% 0.22/0.51      (![X1, X0, X2] : ((~r1_orders_2(X0,sK3(X0,X1,X2),X2) | (sK2(X0,X1,X2) != X2) | r2_yellow_0(X0,X1) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.51  
% 0.22/0.51  tff(u89,negated_conjecture,
% 0.22/0.51      v5_orders_2(sK0)).
% 0.22/0.51  
% 0.22/0.51  tff(u88,negated_conjecture,
% 0.22/0.51      ((~~v25_waybel_0(sK0)) | ~v25_waybel_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  tff(u87,negated_conjecture,
% 0.22/0.51      ((~~v1_xboole_0(sK1)) | ~v1_xboole_0(sK1))).
% 0.22/0.51  
% 0.22/0.51  % (19025)# SZS output end Saturation.
% 0.22/0.51  % (19025)------------------------------
% 0.22/0.51  % (19025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19025)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (19025)Memory used [KB]: 10618
% 0.22/0.51  % (19025)Time elapsed: 0.065 s
% 0.22/0.51  % (19025)------------------------------
% 0.22/0.51  % (19025)------------------------------
% 0.22/0.51  % (19033)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (19014)Success in time 0.145 s
%------------------------------------------------------------------------------
