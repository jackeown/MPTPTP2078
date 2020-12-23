%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:10 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   32 (  32 expanded)
%              Depth                    :    0
%              Number of atoms          :  106 ( 106 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u129,negated_conjecture,(
    v4_orders_2(sK2) )).

tff(u128,negated_conjecture,(
    l1_orders_2(sK2) )).

tff(u127,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u126,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK5(X1,X2,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_orders_2(sK2,X0,sK4)
        | r1_orders_2(sK2,X0,sK5(X1,X2,k4_waybel_0(sK2,sK3)))
        | sP0(X1,X2,k4_waybel_0(sK2,sK3)) ) )).

tff(u125,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK5(X0,X1,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
        | r1_orders_2(sK2,sK4,sK5(X0,X1,k4_waybel_0(sK2,sK3)))
        | sP0(X0,X1,k4_waybel_0(sK2,sK3)) ) )).

tff(u124,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK2)) )).

tff(u123,negated_conjecture,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) )).

tff(u122,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u121,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,X0,sK5(X0,X1,X2))
      | sP0(X0,X1,X2) ) )).

tff(u120,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u119,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X3,X2,X4] :
        ( ~ r1_orders_2(sK2,sK5(X2,sK2,X3),sK4)
        | sP0(X2,sK2,X3)
        | ~ r2_hidden(X4,k4_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X4,u1_struct_0(sK2))
        | r1_orders_2(sK2,sK5(X2,sK2,X3),X4) ) )).

tff(u118,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X3,X2] :
        ( ~ r1_orders_2(sK2,X3,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | sP0(X2,sK2,k4_waybel_0(sK2,sK3))
        | r1_orders_2(sK2,X3,sK5(X2,sK2,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X1,sK4)
        | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) )).

tff(u117,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( r1_orders_2(sK2,sK4,sK5(X0,sK2,k4_waybel_0(sK2,sK3)))
        | sP0(X0,sK2,k4_waybel_0(sK2,sK3)) ) )).

tff(u116,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( r1_orders_2(sK2,X0,sK5(X1,sK2,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | sP0(X1,sK2,k4_waybel_0(sK2,sK3)) ) )).

tff(u115,negated_conjecture,
    ( ~ ~ r1_lattice3(sK2,sK3,sK4)
    | ~ r1_lattice3(sK2,sK3,sK4) )).

tff(u114,negated_conjecture,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,X0,sK4)
      | sP0(sK4,sK2,X0) ) )).

tff(u113,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK5(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK5(X4,X5,X6),X5,X7) ) )).

tff(u112,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4) )).

tff(u111,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X3,X2] :
        ( r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK5(X2,sK2,X3))
        | sP0(X2,sK2,X3)
        | ~ r1_orders_2(sK2,sK5(X2,sK2,X3),sK4) ) )).

tff(u110,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( ~ r2_hidden(X1,k4_waybel_0(sK2,sK3))
        | ~ r1_orders_2(sK2,X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,X1) ) )).

tff(u109,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( ~ r2_hidden(X0,k4_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,sK4,X0) ) )).

tff(u108,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u107,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK4,sK2,X0)
      | r1_lattice3(sK2,X0,sK4) ) )).

tff(u106,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) )).

tff(u105,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK5(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r1_lattice3(X1,X3,sK5(X0,X1,X2)) ) )).

tff(u104,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | sP0(sK4,sK2,k4_waybel_0(sK2,sK3)) )).

tff(u103,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( sP0(X0,sK2,k4_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_orders_2(sK2,X0,sK4) ) )).

tff(u102,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( sP0(sK5(X0,sK2,X1),sK2,k4_waybel_0(sK2,sK3))
        | ~ r1_orders_2(sK2,sK5(X0,sK2,X1),sK4)
        | sP0(X0,sK2,X1) ) )).

tff(u101,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) )).

tff(u100,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u99,negated_conjecture,(
    ! [X0] : sP1(X0,sK2,sK4) )).

tff(u98,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:04:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.41  % (18304)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.19/0.41  % (18304)Refutation not found, incomplete strategy% (18304)------------------------------
% 0.19/0.41  % (18304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (18304)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.41  
% 0.19/0.41  % (18304)Memory used [KB]: 5373
% 0.19/0.41  % (18304)Time elapsed: 0.006 s
% 0.19/0.41  % (18304)------------------------------
% 0.19/0.41  % (18304)------------------------------
% 0.19/0.41  % (18296)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.19/0.45  % (18297)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.19/0.45  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.45  % (18297)# SZS output start Saturation.
% 0.19/0.45  tff(u129,negated_conjecture,
% 0.19/0.45      v4_orders_2(sK2)).
% 0.19/0.45  
% 0.19/0.45  tff(u128,negated_conjecture,
% 0.19/0.45      l1_orders_2(sK2)).
% 0.19/0.45  
% 0.19/0.45  tff(u127,axiom,
% 0.19/0.45      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.19/0.45  
% 0.19/0.45  tff(u126,negated_conjecture,
% 0.19/0.45      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X0, X2] : ((~m1_subset_1(sK5(X1,X2,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_orders_2(sK2,X0,sK4) | r1_orders_2(sK2,X0,sK5(X1,X2,k4_waybel_0(sK2,sK3))) | sP0(X1,X2,k4_waybel_0(sK2,sK3))))))).
% 0.19/0.45  
% 0.19/0.45  tff(u125,negated_conjecture,
% 0.19/0.45      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((~m1_subset_1(sK5(X0,X1,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2)) | r1_orders_2(sK2,sK4,sK5(X0,X1,k4_waybel_0(sK2,sK3))) | sP0(X0,X1,k4_waybel_0(sK2,sK3))))))).
% 0.19/0.45  
% 0.19/0.45  tff(u124,negated_conjecture,
% 0.19/0.45      m1_subset_1(sK4,u1_struct_0(sK2))).
% 0.19/0.45  
% 0.19/0.45  tff(u123,negated_conjecture,
% 0.19/0.45      m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))).
% 0.19/0.45  
% 0.19/0.45  tff(u122,axiom,
% 0.19/0.45      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.19/0.45  
% 0.19/0.45  tff(u121,axiom,
% 0.19/0.45      (![X1, X0, X2] : ((~r1_orders_2(X1,X0,sK5(X0,X1,X2)) | sP0(X0,X1,X2))))).
% 0.19/0.45  
% 0.19/0.45  tff(u120,axiom,
% 0.19/0.45      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.19/0.45  
% 0.19/0.45  tff(u119,negated_conjecture,
% 0.19/0.45      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X3, X2, X4] : ((~r1_orders_2(sK2,sK5(X2,sK2,X3),sK4) | sP0(X2,sK2,X3) | ~r2_hidden(X4,k4_waybel_0(sK2,sK3)) | ~m1_subset_1(X4,u1_struct_0(sK2)) | r1_orders_2(sK2,sK5(X2,sK2,X3),X4)))))).
% 0.19/0.45  
% 0.19/0.45  tff(u118,negated_conjecture,
% 0.19/0.45      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X3, X2] : ((~r1_orders_2(sK2,X3,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | sP0(X2,sK2,k4_waybel_0(sK2,sK3)) | r1_orders_2(sK2,X3,sK5(X2,sK2,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X1,sK4) | ~m1_subset_1(X3,u1_struct_0(sK2))))))).
% 0.19/0.45  
% 0.19/0.45  tff(u117,negated_conjecture,
% 0.19/0.45      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X0] : ((r1_orders_2(sK2,sK4,sK5(X0,sK2,k4_waybel_0(sK2,sK3))) | sP0(X0,sK2,k4_waybel_0(sK2,sK3))))))).
% 0.19/0.45  
% 0.19/0.45  tff(u116,negated_conjecture,
% 0.19/0.45      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((r1_orders_2(sK2,X0,sK5(X1,sK2,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK2)) | sP0(X1,sK2,k4_waybel_0(sK2,sK3))))))).
% 0.19/0.45  
% 0.19/0.45  tff(u115,negated_conjecture,
% 0.19/0.45      ((~~r1_lattice3(sK2,sK3,sK4)) | ~r1_lattice3(sK2,sK3,sK4))).
% 0.19/0.45  
% 0.19/0.45  tff(u114,negated_conjecture,
% 0.19/0.45      (![X0] : ((~r1_lattice3(sK2,X0,sK4) | sP0(sK4,sK2,X0))))).
% 0.19/0.45  
% 0.19/0.45  tff(u113,axiom,
% 0.19/0.45      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK5(X4,X5,X6),X5,X7))))).
% 0.19/0.45  
% 0.19/0.45  tff(u112,negated_conjecture,
% 0.19/0.45      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4))).
% 0.19/0.45  
% 0.19/0.45  tff(u111,negated_conjecture,
% 0.19/0.45      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X3, X2] : ((r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK5(X2,sK2,X3)) | sP0(X2,sK2,X3) | ~r1_orders_2(sK2,sK5(X2,sK2,X3),sK4)))))).
% 0.19/0.45  
% 0.19/0.45  tff(u110,negated_conjecture,
% 0.19/0.45      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((~r2_hidden(X1,k4_waybel_0(sK2,sK3)) | ~r1_orders_2(sK2,X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,X1)))))).
% 0.19/0.45  
% 0.19/0.45  tff(u109,negated_conjecture,
% 0.19/0.45      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X0] : ((~r2_hidden(X0,k4_waybel_0(sK2,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,sK4,X0)))))).
% 0.19/0.45  
% 0.19/0.45  tff(u108,axiom,
% 0.19/0.45      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.19/0.45  
% 0.19/0.45  tff(u107,negated_conjecture,
% 0.19/0.45      (![X0] : ((~sP0(sK4,sK2,X0) | r1_lattice3(sK2,X0,sK4))))).
% 0.19/0.45  
% 0.19/0.45  tff(u106,axiom,
% 0.19/0.45      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4))))).
% 0.19/0.45  
% 0.19/0.45  tff(u105,axiom,
% 0.19/0.45      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r1_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.19/0.45  
% 0.19/0.45  tff(u104,negated_conjecture,
% 0.19/0.45      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | sP0(sK4,sK2,k4_waybel_0(sK2,sK3)))).
% 0.19/0.45  
% 0.19/0.45  tff(u103,negated_conjecture,
% 0.19/0.45      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X0] : ((sP0(X0,sK2,k4_waybel_0(sK2,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_orders_2(sK2,X0,sK4)))))).
% 0.19/0.45  
% 0.19/0.45  tff(u102,negated_conjecture,
% 0.19/0.45      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((sP0(sK5(X0,sK2,X1),sK2,k4_waybel_0(sK2,sK3)) | ~r1_orders_2(sK2,sK5(X0,sK2,X1),sK4) | sP0(X0,sK2,X1)))))).
% 0.19/0.45  
% 0.19/0.45  tff(u101,axiom,
% 0.19/0.45      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r1_lattice3(X1,X0,X2))))).
% 0.19/0.45  
% 0.19/0.45  tff(u100,axiom,
% 0.19/0.45      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r1_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.19/0.45  
% 0.19/0.45  tff(u99,negated_conjecture,
% 0.19/0.45      (![X0] : (sP1(X0,sK2,sK4)))).
% 0.19/0.45  
% 0.19/0.45  tff(u98,axiom,
% 0.19/0.45      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.19/0.45  
% 0.19/0.45  % (18297)# SZS output end Saturation.
% 0.19/0.45  % (18297)------------------------------
% 0.19/0.45  % (18297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (18297)Termination reason: Satisfiable
% 0.19/0.45  
% 0.19/0.45  % (18297)Memory used [KB]: 5373
% 0.19/0.45  % (18297)Time elapsed: 0.005 s
% 0.19/0.45  % (18297)------------------------------
% 0.19/0.45  % (18297)------------------------------
% 0.19/0.46  % (18281)Success in time 0.111 s
%------------------------------------------------------------------------------
