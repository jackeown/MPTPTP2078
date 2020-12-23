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
% DateTime   : Thu Dec  3 13:17:09 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  43 expanded)
%              Number of leaves         :   43 (  43 expanded)
%              Depth                    :    0
%              Number of atoms          :  119 ( 119 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u141,negated_conjecture,(
    l1_orders_2(sK4) )).

tff(u140,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP3(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u139,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u138,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK7(X0,X1,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4))
        | r1_orders_2(sK4,sK6,sK7(X0,X1,k4_waybel_0(sK4,sK5)))
        | sP0(X0,X1,k4_waybel_0(sK4,sK5)) ) )).

tff(u137,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X3,X2] :
        ( ~ m1_subset_1(sK8(X2,X3,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4))
        | r1_orders_2(sK4,sK6,sK8(X2,X3,k4_waybel_0(sK4,sK5)))
        | sP2(X2,X3,k4_waybel_0(sK4,sK5)) ) )).

tff(u136,negated_conjecture,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) )).

tff(u135,negated_conjecture,(
    m1_subset_1(sK6,u1_struct_0(sK4)) )).

tff(u134,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u133,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
      | sP2(X0,X1,X2) ) )).

tff(u132,negated_conjecture,
    ( ~ ~ r1_lattice3(sK4,sK5,sK6)
    | ~ r1_lattice3(sK4,sK5,sK6) )).

tff(u131,negated_conjecture,(
    ! [X0] :
      ( ~ r1_lattice3(sK4,X0,sK6)
      | sP2(sK6,sK4,X0) ) )).

tff(u130,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK7(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP2(sK7(X4,X5,X6),X5,X7) ) )).

tff(u129,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK8(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP2(X4,X5,X6)
      | sP2(sK8(X4,X5,X6),X5,X7) ) )).

tff(u128,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6) )).

tff(u127,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X0] :
        ( ~ r2_hidden(X0,k4_waybel_0(sK4,sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | r1_orders_2(sK4,sK6,X0) ) )).

tff(u126,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u125,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK8(X0,X1,X2),X2)
      | sP2(X0,X1,X2) ) )).

tff(u124,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,sK7(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) )).

tff(u123,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,X0,sK8(X0,X1,X2))
      | sP2(X0,X1,X2) ) )).

tff(u122,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X0] :
        ( r1_orders_2(sK4,sK6,sK7(X0,sK4,k4_waybel_0(sK4,sK5)))
        | sP0(X0,sK4,k4_waybel_0(sK4,sK5)) ) )).

tff(u121,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | ! [X0] :
        ( r1_orders_2(sK4,sK6,sK8(X0,sK4,k4_waybel_0(sK4,sK5)))
        | sP2(X0,sK4,k4_waybel_0(sK4,sK5)) ) )).

tff(u120,negated_conjecture,(
    ! [X0] :
      ( ~ r2_lattice3(sK4,X0,sK6)
      | sP0(sK6,sK4,X0) ) )).

tff(u119,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK7(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK7(X4,X5,X6),X5,X7) ) )).

tff(u118,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK8(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP2(X4,X5,X6)
      | sP0(sK8(X4,X5,X6),X5,X7) ) )).

tff(u117,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) )).

tff(u116,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK6,sK4,X0)
      | r2_lattice3(sK4,X0,sK6) ) )).

tff(u115,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK7(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r2_lattice3(X1,X3,sK7(X0,X1,X2)) ) )).

tff(u114,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK8(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP2(X0,X1,X2)
      | r2_lattice3(X1,X3,sK8(X0,X1,X2)) ) )).

tff(u113,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) )).

tff(u112,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u111,negated_conjecture,(
    ! [X0] : sP1(X0,sK4,sK6) )).

tff(u110,axiom,(
    ! [X5,X7,X4,X6] :
      ( sP1(X7,X5,sK7(X4,X5,X6))
      | sP0(X4,X5,X6)
      | ~ l1_orders_2(X5) ) )).

tff(u109,axiom,(
    ! [X5,X7,X4,X6] :
      ( sP1(X7,X5,sK8(X4,X5,X6))
      | sP2(X4,X5,X6)
      | ~ l1_orders_2(X5) ) )).

tff(u108,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) )).

tff(u107,negated_conjecture,(
    ! [X0] :
      ( ~ sP2(sK6,sK4,X0)
      | r1_lattice3(sK4,X0,sK6) ) )).

tff(u106,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP2(sK7(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r1_lattice3(X1,X3,sK7(X0,X1,X2)) ) )).

tff(u105,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP2(sK8(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP2(X0,X1,X2)
      | r1_lattice3(X1,X3,sK8(X0,X1,X2)) ) )).

tff(u104,negated_conjecture,
    ( ~ r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)
    | sP2(sK6,sK4,k4_waybel_0(sK4,sK5)) )).

tff(u103,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP3(X0,X1,X2)
      | ~ sP2(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) )).

tff(u102,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP3(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP2(X2,X1,X0) ) )).

tff(u101,negated_conjecture,(
    ! [X0] : sP3(X0,sK4,sK6) )).

tff(u100,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP3(X3,X1,sK7(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

tff(u99,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP3(X3,X1,sK8(X0,X1,X2))
      | sP2(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:22:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (16635)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.49  % (16635)Refutation not found, incomplete strategy% (16635)------------------------------
% 0.21/0.49  % (16635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (16635)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (16635)Memory used [KB]: 9850
% 0.21/0.49  % (16635)Time elapsed: 0.074 s
% 0.21/0.49  % (16635)------------------------------
% 0.21/0.49  % (16635)------------------------------
% 0.21/0.50  % (16634)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.50  % (16627)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.50  % (16626)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (16631)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (16633)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.50  % (16634)Refutation not found, incomplete strategy% (16634)------------------------------
% 0.21/0.50  % (16634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16633)Refutation not found, incomplete strategy% (16633)------------------------------
% 0.21/0.50  % (16633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16633)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (16633)Memory used [KB]: 895
% 0.21/0.50  % (16633)Time elapsed: 0.088 s
% 0.21/0.50  % (16633)------------------------------
% 0.21/0.50  % (16633)------------------------------
% 0.21/0.50  % (16625)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.50  % (16618)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (16628)WARNING: option uwaf not known.
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (16625)# SZS output start Saturation.
% 0.21/0.51  tff(u141,negated_conjecture,
% 0.21/0.51      l1_orders_2(sK4)).
% 0.21/0.51  
% 0.21/0.51  tff(u140,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP3(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u139,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u138,negated_conjecture,
% 0.21/0.51      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X1, X0] : ((~m1_subset_1(sK7(X0,X1,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4)) | r1_orders_2(sK4,sK6,sK7(X0,X1,k4_waybel_0(sK4,sK5))) | sP0(X0,X1,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.51  
% 0.21/0.51  tff(u137,negated_conjecture,
% 0.21/0.51      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X3, X2] : ((~m1_subset_1(sK8(X2,X3,k4_waybel_0(sK4,sK5)),u1_struct_0(sK4)) | r1_orders_2(sK4,sK6,sK8(X2,X3,k4_waybel_0(sK4,sK5))) | sP2(X2,X3,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.51  
% 0.21/0.51  tff(u136,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))).
% 0.21/0.51  
% 0.21/0.51  tff(u135,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK6,u1_struct_0(sK4))).
% 0.21/0.51  
% 0.21/0.51  tff(u134,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u133,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) | sP2(X0,X1,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u132,negated_conjecture,
% 0.21/0.51      ((~~r1_lattice3(sK4,sK5,sK6)) | ~r1_lattice3(sK4,sK5,sK6))).
% 0.21/0.51  
% 0.21/0.51  tff(u131,negated_conjecture,
% 0.21/0.51      (![X0] : ((~r1_lattice3(sK4,X0,sK6) | sP2(sK6,sK4,X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u130,axiom,
% 0.21/0.51      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK7(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP2(sK7(X4,X5,X6),X5,X7))))).
% 0.21/0.51  
% 0.21/0.51  tff(u129,axiom,
% 0.21/0.51      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK8(X4,X5,X6)) | ~l1_orders_2(X5) | sP2(X4,X5,X6) | sP2(sK8(X4,X5,X6),X5,X7))))).
% 0.21/0.51  
% 0.21/0.51  tff(u128,negated_conjecture,
% 0.21/0.51      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6))).
% 0.21/0.51  
% 0.21/0.51  tff(u127,negated_conjecture,
% 0.21/0.51      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X0] : ((~r2_hidden(X0,k4_waybel_0(sK4,sK5)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | r1_orders_2(sK4,sK6,X0)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u126,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((r2_hidden(sK7(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u125,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((r2_hidden(sK8(X0,X1,X2),X2) | sP2(X0,X1,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u124,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~r1_orders_2(X1,sK7(X0,X1,X2),X0) | sP0(X0,X1,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u123,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~r1_orders_2(X1,X0,sK8(X0,X1,X2)) | sP2(X0,X1,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u122,negated_conjecture,
% 0.21/0.51      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X0] : ((r1_orders_2(sK4,sK6,sK7(X0,sK4,k4_waybel_0(sK4,sK5))) | sP0(X0,sK4,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.51  
% 0.21/0.51  tff(u121,negated_conjecture,
% 0.21/0.51      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | (![X0] : ((r1_orders_2(sK4,sK6,sK8(X0,sK4,k4_waybel_0(sK4,sK5))) | sP2(X0,sK4,k4_waybel_0(sK4,sK5))))))).
% 0.21/0.51  
% 0.21/0.51  tff(u120,negated_conjecture,
% 0.21/0.51      (![X0] : ((~r2_lattice3(sK4,X0,sK6) | sP0(sK6,sK4,X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u119,axiom,
% 0.21/0.51      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK7(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK7(X4,X5,X6),X5,X7))))).
% 0.21/0.51  
% 0.21/0.51  tff(u118,axiom,
% 0.21/0.51      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK8(X4,X5,X6)) | ~l1_orders_2(X5) | sP2(X4,X5,X6) | sP0(sK8(X4,X5,X6),X5,X7))))).
% 0.21/0.51  
% 0.21/0.51  tff(u117,axiom,
% 0.21/0.51      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u116,negated_conjecture,
% 0.21/0.51      (![X0] : ((~sP0(sK6,sK4,X0) | r2_lattice3(sK4,X0,sK6))))).
% 0.21/0.51  
% 0.21/0.51  tff(u115,axiom,
% 0.21/0.51      (![X1, X3, X0, X2] : ((~sP0(sK7(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r2_lattice3(X1,X3,sK7(X0,X1,X2)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u114,axiom,
% 0.21/0.51      (![X1, X3, X0, X2] : ((~sP0(sK8(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP2(X0,X1,X2) | r2_lattice3(X1,X3,sK8(X0,X1,X2)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u113,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_lattice3(X1,X0,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u112,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u111,negated_conjecture,
% 0.21/0.51      (![X0] : (sP1(X0,sK4,sK6)))).
% 0.21/0.51  
% 0.21/0.51  tff(u110,axiom,
% 0.21/0.51      (![X5, X7, X4, X6] : ((sP1(X7,X5,sK7(X4,X5,X6)) | sP0(X4,X5,X6) | ~l1_orders_2(X5))))).
% 0.21/0.51  
% 0.21/0.51  tff(u109,axiom,
% 0.21/0.51      (![X5, X7, X4, X6] : ((sP1(X7,X5,sK8(X4,X5,X6)) | sP2(X4,X5,X6) | ~l1_orders_2(X5))))).
% 0.21/0.51  
% 0.21/0.51  tff(u108,axiom,
% 0.21/0.51      (![X1, X0, X2, X4] : ((~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4))))).
% 0.21/0.51  
% 0.21/0.51  tff(u107,negated_conjecture,
% 0.21/0.51      (![X0] : ((~sP2(sK6,sK4,X0) | r1_lattice3(sK4,X0,sK6))))).
% 0.21/0.51  
% 0.21/0.51  tff(u106,axiom,
% 0.21/0.51      (![X1, X3, X0, X2] : ((~sP2(sK7(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r1_lattice3(X1,X3,sK7(X0,X1,X2)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u105,axiom,
% 0.21/0.51      (![X1, X3, X0, X2] : ((~sP2(sK8(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP2(X0,X1,X2) | r1_lattice3(X1,X3,sK8(X0,X1,X2)))))).
% 0.21/0.51  
% 0.21/0.51  tff(u104,negated_conjecture,
% 0.21/0.51      ((~r1_lattice3(sK4,k4_waybel_0(sK4,sK5),sK6)) | sP2(sK6,sK4,k4_waybel_0(sK4,sK5)))).
% 0.21/0.51  
% 0.21/0.51  tff(u103,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~sP3(X0,X1,X2) | ~sP2(X2,X1,X0) | r1_lattice3(X1,X0,X2))))).
% 0.21/0.51  
% 0.21/0.51  tff(u102,axiom,
% 0.21/0.51      (![X1, X0, X2] : ((~sP3(X0,X1,X2) | ~r1_lattice3(X1,X0,X2) | sP2(X2,X1,X0))))).
% 0.21/0.51  
% 0.21/0.51  tff(u101,negated_conjecture,
% 0.21/0.51      (![X0] : (sP3(X0,sK4,sK6)))).
% 0.21/0.51  
% 0.21/0.51  tff(u100,axiom,
% 0.21/0.51      (![X1, X3, X0, X2] : ((sP3(X3,X1,sK7(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.51  
% 0.21/0.51  tff(u99,axiom,
% 0.21/0.51      (![X1, X3, X0, X2] : ((sP3(X3,X1,sK8(X0,X1,X2)) | sP2(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.51  
% 0.21/0.51  % (16625)# SZS output end Saturation.
% 0.21/0.51  % (16625)------------------------------
% 0.21/0.51  % (16625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16625)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (16625)Memory used [KB]: 5373
% 0.21/0.51  % (16625)Time elapsed: 0.083 s
% 0.21/0.51  % (16625)------------------------------
% 0.21/0.51  % (16625)------------------------------
% 0.21/0.51  % (16622)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.51  % (16617)Success in time 0.142 s
%------------------------------------------------------------------------------
