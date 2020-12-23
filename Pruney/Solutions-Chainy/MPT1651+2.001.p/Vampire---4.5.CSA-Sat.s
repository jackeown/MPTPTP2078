%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:05 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   35 (  35 expanded)
%              Depth                    :    0
%              Number of atoms          :  106 ( 106 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u137,negated_conjecture,(
    ~ v2_struct_0(sK2) )).

tff(u136,negated_conjecture,(
    v3_orders_2(sK2) )).

tff(u135,negated_conjecture,(
    l1_orders_2(sK2) )).

tff(u134,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u133,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u132,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK5(X0,X1,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
        | r1_orders_2(sK2,sK5(X0,X1,k3_waybel_0(sK2,sK3)),sK4)
        | sP0(X0,X1,k3_waybel_0(sK2,sK3)) ) )).

tff(u131,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK2)) )).

tff(u130,negated_conjecture,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) )).

tff(u129,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u128,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,sK5(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) )).

tff(u127,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X3,X2] :
        ( ~ r1_orders_2(sK2,sK4,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ r1_orders_2(sK2,X2,X3)
        | r2_lattice3(sK2,k3_waybel_0(sK2,sK3),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) )).

tff(u126,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X3,X2,X4] :
        ( ~ r1_orders_2(sK2,sK4,sK5(X2,sK2,X3))
        | sP0(X2,sK2,X3)
        | ~ r2_hidden(X4,k3_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X4,u1_struct_0(sK2))
        | r1_orders_2(sK2,X4,sK5(X2,sK2,X3)) ) )).

tff(u125,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X3,X2,X4] :
        ( ~ r1_orders_2(sK2,sK5(X2,sK2,X3),X4)
        | sP0(X2,sK2,X3)
        | ~ r1_orders_2(sK2,sK4,sK5(X2,sK2,X3))
        | r2_lattice3(sK2,k3_waybel_0(sK2,sK3),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) )).

tff(u124,negated_conjecture,(
    r1_orders_2(sK2,sK4,sK4) )).

tff(u123,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( r1_orders_2(sK2,sK5(X0,sK2,k3_waybel_0(sK2,sK3)),sK4)
        | sP0(X0,sK2,k3_waybel_0(sK2,sK3)) ) )).

tff(u122,axiom,(
    ! [X1,X0,X2] :
      ( r1_orders_2(X0,sK5(X1,X0,X2),sK5(X1,X0,X2))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | sP0(X1,X0,X2) ) )).

tff(u121,negated_conjecture,
    ( ~ ~ r2_lattice3(sK2,sK3,sK4)
    | ~ r2_lattice3(sK2,sK3,sK4) )).

tff(u120,negated_conjecture,(
    ! [X0] :
      ( ~ r2_lattice3(sK2,X0,sK4)
      | sP0(sK4,sK2,X0) ) )).

tff(u119,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK5(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK5(X4,X5,X6),X5,X7) ) )).

tff(u118,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u117,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4) )).

tff(u116,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( r2_lattice3(sK2,k3_waybel_0(sK2,sK3),X0)
        | ~ r1_orders_2(sK2,sK4,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) )).

tff(u115,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK5(X0,sK2,X1))
        | ~ r1_orders_2(sK2,sK4,sK5(X0,sK2,X1))
        | sP0(X0,sK2,X1) ) )).

tff(u114,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( ~ r2_hidden(X0,k3_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,sK4) ) )).

tff(u113,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u112,negated_conjecture,(
    v4_orders_2(sK2) )).

tff(u111,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK4,sK2,X0)
      | r2_lattice3(sK2,X0,sK4) ) )).

tff(u110,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) )).

tff(u109,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK5(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r2_lattice3(X1,X3,sK5(X0,X1,X2)) ) )).

tff(u108,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | sP0(sK4,sK2,k3_waybel_0(sK2,sK3)) )).

tff(u107,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( sP0(sK5(X0,sK2,X1),sK2,k3_waybel_0(sK2,sK3))
        | sP0(X0,sK2,X1)
        | ~ r1_orders_2(sK2,sK4,sK5(X0,sK2,X1)) ) )).

tff(u106,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) )).

tff(u105,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u104,negated_conjecture,(
    ! [X0] : sP1(X0,sK2,sK4) )).

tff(u103,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (20053)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.47  % (20054)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.47  % (20054)# SZS output start Saturation.
% 0.20/0.47  tff(u137,negated_conjecture,
% 0.20/0.47      ~v2_struct_0(sK2)).
% 0.20/0.47  
% 0.20/0.47  tff(u136,negated_conjecture,
% 0.20/0.47      v3_orders_2(sK2)).
% 0.20/0.47  
% 0.20/0.47  tff(u135,negated_conjecture,
% 0.20/0.47      l1_orders_2(sK2)).
% 0.20/0.47  
% 0.20/0.47  tff(u134,axiom,
% 0.20/0.47      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u133,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u132,negated_conjecture,
% 0.20/0.47      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((~m1_subset_1(sK5(X0,X1,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2)) | r1_orders_2(sK2,sK5(X0,X1,k3_waybel_0(sK2,sK3)),sK4) | sP0(X0,X1,k3_waybel_0(sK2,sK3))))))).
% 0.20/0.47  
% 0.20/0.47  tff(u131,negated_conjecture,
% 0.20/0.47      m1_subset_1(sK4,u1_struct_0(sK2))).
% 0.20/0.47  
% 0.20/0.47  tff(u130,negated_conjecture,
% 0.20/0.47      m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))).
% 0.20/0.47  
% 0.20/0.47  tff(u129,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u128,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~r1_orders_2(X1,sK5(X0,X1,X2),X0) | sP0(X0,X1,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u127,negated_conjecture,
% 0.20/0.47      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X3, X2] : ((~r1_orders_2(sK2,sK4,X2) | ~m1_subset_1(X2,u1_struct_0(sK2)) | ~r1_orders_2(sK2,X2,X3) | r2_lattice3(sK2,k3_waybel_0(sK2,sK3),X3) | ~m1_subset_1(X3,u1_struct_0(sK2))))))).
% 0.20/0.47  
% 0.20/0.47  tff(u126,negated_conjecture,
% 0.20/0.47      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X3, X2, X4] : ((~r1_orders_2(sK2,sK4,sK5(X2,sK2,X3)) | sP0(X2,sK2,X3) | ~r2_hidden(X4,k3_waybel_0(sK2,sK3)) | ~m1_subset_1(X4,u1_struct_0(sK2)) | r1_orders_2(sK2,X4,sK5(X2,sK2,X3))))))).
% 0.20/0.47  
% 0.20/0.47  tff(u125,negated_conjecture,
% 0.20/0.47      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X3, X2, X4] : ((~r1_orders_2(sK2,sK5(X2,sK2,X3),X4) | sP0(X2,sK2,X3) | ~r1_orders_2(sK2,sK4,sK5(X2,sK2,X3)) | r2_lattice3(sK2,k3_waybel_0(sK2,sK3),X4) | ~m1_subset_1(X4,u1_struct_0(sK2))))))).
% 0.20/0.47  
% 0.20/0.47  tff(u124,negated_conjecture,
% 0.20/0.47      r1_orders_2(sK2,sK4,sK4)).
% 0.20/0.47  
% 0.20/0.47  tff(u123,negated_conjecture,
% 0.20/0.47      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X0] : ((r1_orders_2(sK2,sK5(X0,sK2,k3_waybel_0(sK2,sK3)),sK4) | sP0(X0,sK2,k3_waybel_0(sK2,sK3))))))).
% 0.20/0.47  
% 0.20/0.47  tff(u122,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((r1_orders_2(X0,sK5(X1,X0,X2),sK5(X1,X0,X2)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | sP0(X1,X0,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u121,negated_conjecture,
% 0.20/0.47      ((~~r2_lattice3(sK2,sK3,sK4)) | ~r2_lattice3(sK2,sK3,sK4))).
% 0.20/0.47  
% 0.20/0.47  tff(u120,negated_conjecture,
% 0.20/0.47      (![X0] : ((~r2_lattice3(sK2,X0,sK4) | sP0(sK4,sK2,X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u119,axiom,
% 0.20/0.47      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK5(X4,X5,X6),X5,X7))))).
% 0.20/0.47  
% 0.20/0.47  tff(u118,axiom,
% 0.20/0.47      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,X3) | r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u117,negated_conjecture,
% 0.20/0.47      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4))).
% 0.20/0.47  
% 0.20/0.47  tff(u116,negated_conjecture,
% 0.20/0.47      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X0] : ((r2_lattice3(sK2,k3_waybel_0(sK2,sK3),X0) | ~r1_orders_2(sK2,sK4,X0) | ~m1_subset_1(X0,u1_struct_0(sK2))))))).
% 0.20/0.47  
% 0.20/0.47  tff(u115,negated_conjecture,
% 0.20/0.47      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK5(X0,sK2,X1)) | ~r1_orders_2(sK2,sK4,sK5(X0,sK2,X1)) | sP0(X0,sK2,X1)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u114,negated_conjecture,
% 0.20/0.47      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X0] : ((~r2_hidden(X0,k3_waybel_0(sK2,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,sK4)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u113,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u112,negated_conjecture,
% 0.20/0.47      v4_orders_2(sK2)).
% 0.20/0.47  
% 0.20/0.47  tff(u111,negated_conjecture,
% 0.20/0.47      (![X0] : ((~sP0(sK4,sK2,X0) | r2_lattice3(sK2,X0,sK4))))).
% 0.20/0.47  
% 0.20/0.47  tff(u110,axiom,
% 0.20/0.47      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u109,axiom,
% 0.20/0.47      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r2_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u108,negated_conjecture,
% 0.20/0.47      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | sP0(sK4,sK2,k3_waybel_0(sK2,sK3)))).
% 0.20/0.47  
% 0.20/0.47  tff(u107,negated_conjecture,
% 0.20/0.47      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((sP0(sK5(X0,sK2,X1),sK2,k3_waybel_0(sK2,sK3)) | sP0(X0,sK2,X1) | ~r1_orders_2(sK2,sK4,sK5(X0,sK2,X1))))))).
% 0.20/0.47  
% 0.20/0.47  tff(u106,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_lattice3(X1,X0,X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u105,axiom,
% 0.20/0.47      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u104,negated_conjecture,
% 0.20/0.47      (![X0] : (sP1(X0,sK2,sK4)))).
% 0.20/0.47  
% 0.20/0.47  tff(u103,axiom,
% 0.20/0.47      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.20/0.47  
% 0.20/0.47  % (20054)# SZS output end Saturation.
% 0.20/0.47  % (20054)------------------------------
% 0.20/0.47  % (20054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (20054)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (20054)Memory used [KB]: 5373
% 0.20/0.47  % (20054)Time elapsed: 0.058 s
% 0.20/0.47  % (20054)------------------------------
% 0.20/0.47  % (20054)------------------------------
% 0.20/0.48  % (20062)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.48  % (20062)Refutation not found, incomplete strategy% (20062)------------------------------
% 0.20/0.48  % (20062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (20062)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (20062)Memory used [KB]: 895
% 0.20/0.48  % (20062)Time elapsed: 0.069 s
% 0.20/0.48  % (20062)------------------------------
% 0.20/0.48  % (20062)------------------------------
% 0.20/0.48  % (20046)Success in time 0.122 s
%------------------------------------------------------------------------------
