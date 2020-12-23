%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:10 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  50 expanded)
%              Number of leaves         :   50 (  50 expanded)
%              Depth                    :    0
%              Number of atoms          :  190 ( 190 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u213,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u212,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u211,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) )).

tff(u210,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X3,X2,X4] :
        ( ~ m1_subset_1(sK5(X2,X3,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | sP0(X2,X3,k4_waybel_0(sK2,sK3))
        | ~ r2_hidden(sK5(X2,X3,k4_waybel_0(sK2,sK3)),sK3)
        | r1_orders_2(sK2,X4,sK5(X2,X3,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X4,X1)
        | ~ r1_orders_2(sK2,X1,sK4)
        | ~ m1_subset_1(X4,u1_struct_0(sK2)) ) )).

tff(u209,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK5(X1,X2,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_orders_2(sK2,X0,sK4)
        | r1_orders_2(sK2,X0,sK5(X1,X2,k4_waybel_0(sK2,sK3)))
        | sP0(X1,X2,k4_waybel_0(sK2,sK3)) ) )).

tff(u208,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK5(X1,X2,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
        | ~ r2_hidden(X0,sK3)
        | ~ r1_orders_2(sK2,X0,sK4)
        | r1_orders_2(sK2,X0,sK5(X1,X2,k4_waybel_0(sK2,sK3)))
        | sP0(X1,X2,k4_waybel_0(sK2,sK3)) ) )).

tff(u207,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK5(X0,X1,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
        | r1_orders_2(sK2,sK4,sK5(X0,X1,k4_waybel_0(sK2,sK3)))
        | sP0(X0,X1,k4_waybel_0(sK2,sK3)) ) )).

tff(u206,negated_conjecture,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK3) ) )).

tff(u205,negated_conjecture,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) )).

tff(u204,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK2)) )).

tff(u203,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u202,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X2] :
        ( ~ r2_hidden(X2,k4_waybel_0(sK2,sK3))
        | ~ r1_orders_2(sK2,X1,sK4)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | r1_orders_2(sK2,X1,X2) ) )).

tff(u201,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X2] :
        ( ~ r2_hidden(X2,k4_waybel_0(sK2,sK3))
        | ~ r1_orders_2(sK2,X1,sK4)
        | ~ r2_hidden(X1,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | r1_orders_2(sK2,X1,X2) ) )).

tff(u200,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( ~ r2_hidden(X0,k4_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,sK4,X0) ) )).

tff(u199,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X3,X5,X4,X6] :
        ( ~ r2_hidden(sK5(X4,X5,k4_waybel_0(sK2,sK3)),sK3)
        | sP0(X4,X5,k4_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK2))
        | r1_orders_2(sK2,X6,sK5(X4,X5,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X6,X3)
        | ~ r1_orders_2(sK2,X3,sK4)
        | ~ m1_subset_1(X6,u1_struct_0(sK2)) ) )).

tff(u198,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X5,X7,X8,X6] :
        ( ~ r2_hidden(sK5(X6,X7,k4_waybel_0(sK2,sK3)),sK3)
        | ~ r2_hidden(X5,sK3)
        | sP0(X6,X7,k4_waybel_0(sK2,sK3))
        | ~ r1_orders_2(sK2,X5,sK4)
        | r1_orders_2(sK2,X8,sK5(X6,X7,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X8,X5)
        | ~ m1_subset_1(X8,u1_struct_0(sK2)) ) )).

tff(u197,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u196,negated_conjecture,(
    ! [X0] :
      ( r2_hidden(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK3) ) )).

tff(u195,negated_conjecture,(
    v4_orders_2(sK2) )).

tff(u194,negated_conjecture,(
    l1_orders_2(sK2) )).

tff(u193,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,X0,sK5(X0,X1,X2))
      | sP0(X0,X1,X2) ) )).

tff(u192,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u191,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X5,X4,X6] :
        ( ~ r1_orders_2(sK2,sK5(X4,sK2,X5),sK4)
        | sP0(X4,sK2,X5)
        | ~ r2_hidden(X6,k4_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X6,u1_struct_0(sK2))
        | r1_orders_2(sK2,sK5(X4,sK2,X5),X6) ) )).

tff(u190,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X3,X2] :
        ( ~ r1_orders_2(sK2,X3,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | sP0(X2,sK2,k4_waybel_0(sK2,sK3))
        | r1_orders_2(sK2,X3,sK5(X2,sK2,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X1,sK4)
        | ~ m1_subset_1(X3,u1_struct_0(sK2)) ) )).

tff(u189,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( r1_orders_2(sK2,sK4,sK5(X0,sK2,k4_waybel_0(sK2,sK3)))
        | sP0(X0,sK2,k4_waybel_0(sK2,sK3)) ) )).

tff(u188,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X2] :
        ( r1_orders_2(sK2,sK4,sK5(X1,X2,k4_waybel_0(sK2,sK3)))
        | sP0(X1,X2,k4_waybel_0(sK2,sK3))
        | ~ r2_hidden(sK5(X1,X2,k4_waybel_0(sK2,sK3)),sK3) ) )).

tff(u187,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( r1_orders_2(sK2,X0,sK5(X1,sK2,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X0,sK4)
        | ~ r2_hidden(X0,sK3)
        | sP0(X1,sK2,k4_waybel_0(sK2,sK3)) ) )).

tff(u186,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( r1_orders_2(sK2,X0,sK5(X1,sK2,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | sP0(X1,sK2,k4_waybel_0(sK2,sK3)) ) )).

tff(u185,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X3,X2,X4] :
        ( r1_orders_2(sK2,X2,sK5(X3,X4,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X2,sK4)
        | ~ r2_hidden(X2,sK3)
        | sP0(X3,X4,k4_waybel_0(sK2,sK3))
        | ~ r2_hidden(sK5(X3,X4,k4_waybel_0(sK2,sK3)),sK3) ) )).

tff(u184,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X3,X2,X4] :
        ( r1_orders_2(sK2,X2,sK5(X3,X4,k4_waybel_0(sK2,sK3)))
        | ~ r1_orders_2(sK2,X2,sK4)
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | sP0(X3,X4,k4_waybel_0(sK2,sK3))
        | ~ r2_hidden(sK5(X3,X4,k4_waybel_0(sK2,sK3)),sK3) ) )).

tff(u183,negated_conjecture,
    ( ~ ~ r1_lattice3(sK2,sK3,sK4)
    | ~ r1_lattice3(sK2,sK3,sK4) )).

tff(u182,negated_conjecture,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,X0,sK4)
      | sP0(sK4,sK2,X0) ) )).

tff(u181,negated_conjecture,(
    ! [X1,X2] :
      ( ~ r1_lattice3(sK2,X1,X2)
      | sP0(X2,sK2,X1)
      | ~ r2_hidden(X2,sK3) ) )).

tff(u180,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK5(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK5(X4,X5,X6),X5,X7) ) )).

tff(u179,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4) )).

tff(u178,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( r1_lattice3(sK2,k4_waybel_0(sK2,sK3),X0)
        | ~ r1_orders_2(sK2,X0,sK4)
        | ~ r2_hidden(X0,sK3) ) )).

tff(u177,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X3,X4] :
        ( r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK5(X3,sK2,X4))
        | sP0(X3,sK2,X4)
        | ~ r1_orders_2(sK2,sK5(X3,sK2,X4),sK4) ) )).

tff(u176,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK4,sK2,X0)
      | r1_lattice3(sK2,X0,sK4) ) )).

tff(u175,negated_conjecture,(
    ! [X1,X2] :
      ( ~ sP0(X1,sK2,X2)
      | r1_lattice3(sK2,X2,X1)
      | ~ r2_hidden(X1,sK3) ) )).

tff(u174,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) )).

tff(u173,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK5(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r1_lattice3(X1,X3,sK5(X0,X1,X2)) ) )).

tff(u172,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | sP0(sK4,sK2,k4_waybel_0(sK2,sK3)) )).

tff(u171,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( sP0(X0,sK2,k4_waybel_0(sK2,sK3))
        | ~ r2_hidden(X0,sK3)
        | ~ r1_orders_2(sK2,X0,sK4) ) )).

tff(u170,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( sP0(X0,sK2,k4_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_orders_2(sK2,X0,sK4) ) )).

tff(u169,negated_conjecture,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)
    | ! [X3,X2] :
        ( sP0(sK5(X2,sK2,X3),sK2,k4_waybel_0(sK2,sK3))
        | ~ r1_orders_2(sK2,sK5(X2,sK2,X3),sK4)
        | sP0(X2,sK2,X3) ) )).

tff(u168,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) )).

tff(u167,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u166,negated_conjecture,(
    ! [X0] : sP1(X0,sK2,sK4) )).

tff(u165,negated_conjecture,(
    ! [X1,X0] :
      ( sP1(X1,sK2,X0)
      | ~ r2_hidden(X0,sK3) ) )).

tff(u164,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:20:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (8762)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.47  % (8768)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.47  % (8768)Refutation not found, incomplete strategy% (8768)------------------------------
% 0.21/0.47  % (8768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (8768)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (8768)Memory used [KB]: 895
% 0.21/0.47  % (8768)Time elapsed: 0.006 s
% 0.21/0.47  % (8768)------------------------------
% 0.21/0.47  % (8768)------------------------------
% 0.21/0.47  % (8760)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.47  % (8760)# SZS output start Saturation.
% 0.21/0.47  tff(u213,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u212,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1))))).
% 0.21/0.47  
% 0.21/0.47  tff(u211,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u210,negated_conjecture,
% 0.21/0.47      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X3, X2, X4] : ((~m1_subset_1(sK5(X2,X3,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | sP0(X2,X3,k4_waybel_0(sK2,sK3)) | ~r2_hidden(sK5(X2,X3,k4_waybel_0(sK2,sK3)),sK3) | r1_orders_2(sK2,X4,sK5(X2,X3,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X4,X1) | ~r1_orders_2(sK2,X1,sK4) | ~m1_subset_1(X4,u1_struct_0(sK2))))))).
% 0.21/0.47  
% 0.21/0.47  tff(u209,negated_conjecture,
% 0.21/0.47      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X0, X2] : ((~m1_subset_1(sK5(X1,X2,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_orders_2(sK2,X0,sK4) | r1_orders_2(sK2,X0,sK5(X1,X2,k4_waybel_0(sK2,sK3))) | sP0(X1,X2,k4_waybel_0(sK2,sK3))))))).
% 0.21/0.47  
% 0.21/0.47  tff(u208,negated_conjecture,
% 0.21/0.47      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X0, X2] : ((~m1_subset_1(sK5(X1,X2,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2)) | ~r2_hidden(X0,sK3) | ~r1_orders_2(sK2,X0,sK4) | r1_orders_2(sK2,X0,sK5(X1,X2,k4_waybel_0(sK2,sK3))) | sP0(X1,X2,k4_waybel_0(sK2,sK3))))))).
% 0.21/0.47  
% 0.21/0.47  tff(u207,negated_conjecture,
% 0.21/0.47      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((~m1_subset_1(sK5(X0,X1,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2)) | r1_orders_2(sK2,sK4,sK5(X0,X1,k4_waybel_0(sK2,sK3))) | sP0(X0,X1,k4_waybel_0(sK2,sK3))))))).
% 0.21/0.47  
% 0.21/0.47  tff(u206,negated_conjecture,
% 0.21/0.47      (![X0] : ((m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,sK3))))).
% 0.21/0.47  
% 0.21/0.47  tff(u205,negated_conjecture,
% 0.21/0.47      m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))).
% 0.21/0.47  
% 0.21/0.47  tff(u204,negated_conjecture,
% 0.21/0.47      m1_subset_1(sK4,u1_struct_0(sK2))).
% 0.21/0.47  
% 0.21/0.47  tff(u203,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.21/0.47  
% 0.21/0.47  tff(u202,negated_conjecture,
% 0.21/0.47      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X2] : ((~r2_hidden(X2,k4_waybel_0(sK2,sK3)) | ~r1_orders_2(sK2,X1,sK4) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK2)) | r1_orders_2(sK2,X1,X2)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u201,negated_conjecture,
% 0.21/0.47      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X2] : ((~r2_hidden(X2,k4_waybel_0(sK2,sK3)) | ~r1_orders_2(sK2,X1,sK4) | ~r2_hidden(X1,sK3) | ~m1_subset_1(X2,u1_struct_0(sK2)) | r1_orders_2(sK2,X1,X2)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u200,negated_conjecture,
% 0.21/0.47      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X0] : ((~r2_hidden(X0,k4_waybel_0(sK2,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,sK4,X0)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u199,negated_conjecture,
% 0.21/0.47      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X3, X5, X4, X6] : ((~r2_hidden(sK5(X4,X5,k4_waybel_0(sK2,sK3)),sK3) | sP0(X4,X5,k4_waybel_0(sK2,sK3)) | ~m1_subset_1(X3,u1_struct_0(sK2)) | r1_orders_2(sK2,X6,sK5(X4,X5,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X6,X3) | ~r1_orders_2(sK2,X3,sK4) | ~m1_subset_1(X6,u1_struct_0(sK2))))))).
% 0.21/0.47  
% 0.21/0.47  tff(u198,negated_conjecture,
% 0.21/0.47      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X5, X7, X8, X6] : ((~r2_hidden(sK5(X6,X7,k4_waybel_0(sK2,sK3)),sK3) | ~r2_hidden(X5,sK3) | sP0(X6,X7,k4_waybel_0(sK2,sK3)) | ~r1_orders_2(sK2,X5,sK4) | r1_orders_2(sK2,X8,sK5(X6,X7,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X8,X5) | ~m1_subset_1(X8,u1_struct_0(sK2))))))).
% 0.21/0.47  
% 0.21/0.47  tff(u197,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.21/0.47  
% 0.21/0.48  tff(u196,negated_conjecture,
% 0.21/0.48      (![X0] : ((r2_hidden(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,sK3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u195,negated_conjecture,
% 0.21/0.48      v4_orders_2(sK2)).
% 0.21/0.48  
% 0.21/0.48  tff(u194,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK2)).
% 0.21/0.48  
% 0.21/0.48  tff(u193,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r1_orders_2(X1,X0,sK5(X0,X1,X2)) | sP0(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u192,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u191,negated_conjecture,
% 0.21/0.48      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X5, X4, X6] : ((~r1_orders_2(sK2,sK5(X4,sK2,X5),sK4) | sP0(X4,sK2,X5) | ~r2_hidden(X6,k4_waybel_0(sK2,sK3)) | ~m1_subset_1(X6,u1_struct_0(sK2)) | r1_orders_2(sK2,sK5(X4,sK2,X5),X6)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u190,negated_conjecture,
% 0.21/0.48      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X3, X2] : ((~r1_orders_2(sK2,X3,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | sP0(X2,sK2,k4_waybel_0(sK2,sK3)) | r1_orders_2(sK2,X3,sK5(X2,sK2,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X1,sK4) | ~m1_subset_1(X3,u1_struct_0(sK2))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u189,negated_conjecture,
% 0.21/0.48      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X0] : ((r1_orders_2(sK2,sK4,sK5(X0,sK2,k4_waybel_0(sK2,sK3))) | sP0(X0,sK2,k4_waybel_0(sK2,sK3))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u188,negated_conjecture,
% 0.21/0.48      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X2] : ((r1_orders_2(sK2,sK4,sK5(X1,X2,k4_waybel_0(sK2,sK3))) | sP0(X1,X2,k4_waybel_0(sK2,sK3)) | ~r2_hidden(sK5(X1,X2,k4_waybel_0(sK2,sK3)),sK3)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u187,negated_conjecture,
% 0.21/0.48      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((r1_orders_2(sK2,X0,sK5(X1,sK2,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X0,sK4) | ~r2_hidden(X0,sK3) | sP0(X1,sK2,k4_waybel_0(sK2,sK3))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u186,negated_conjecture,
% 0.21/0.48      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((r1_orders_2(sK2,X0,sK5(X1,sK2,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK2)) | sP0(X1,sK2,k4_waybel_0(sK2,sK3))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u185,negated_conjecture,
% 0.21/0.48      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X3, X2, X4] : ((r1_orders_2(sK2,X2,sK5(X3,X4,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X2,sK4) | ~r2_hidden(X2,sK3) | sP0(X3,X4,k4_waybel_0(sK2,sK3)) | ~r2_hidden(sK5(X3,X4,k4_waybel_0(sK2,sK3)),sK3)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u184,negated_conjecture,
% 0.21/0.48      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X3, X2, X4] : ((r1_orders_2(sK2,X2,sK5(X3,X4,k4_waybel_0(sK2,sK3))) | ~r1_orders_2(sK2,X2,sK4) | ~m1_subset_1(X2,u1_struct_0(sK2)) | sP0(X3,X4,k4_waybel_0(sK2,sK3)) | ~r2_hidden(sK5(X3,X4,k4_waybel_0(sK2,sK3)),sK3)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u183,negated_conjecture,
% 0.21/0.48      ((~~r1_lattice3(sK2,sK3,sK4)) | ~r1_lattice3(sK2,sK3,sK4))).
% 0.21/0.48  
% 0.21/0.48  tff(u182,negated_conjecture,
% 0.21/0.48      (![X0] : ((~r1_lattice3(sK2,X0,sK4) | sP0(sK4,sK2,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u181,negated_conjecture,
% 0.21/0.48      (![X1, X2] : ((~r1_lattice3(sK2,X1,X2) | sP0(X2,sK2,X1) | ~r2_hidden(X2,sK3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u180,axiom,
% 0.21/0.48      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK5(X4,X5,X6),X5,X7))))).
% 0.21/0.48  
% 0.21/0.48  tff(u179,negated_conjecture,
% 0.21/0.48      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4))).
% 0.21/0.48  
% 0.21/0.48  tff(u178,negated_conjecture,
% 0.21/0.48      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X0] : ((r1_lattice3(sK2,k4_waybel_0(sK2,sK3),X0) | ~r1_orders_2(sK2,X0,sK4) | ~r2_hidden(X0,sK3)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u177,negated_conjecture,
% 0.21/0.48      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X3, X4] : ((r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK5(X3,sK2,X4)) | sP0(X3,sK2,X4) | ~r1_orders_2(sK2,sK5(X3,sK2,X4),sK4)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u176,negated_conjecture,
% 0.21/0.48      (![X0] : ((~sP0(sK4,sK2,X0) | r1_lattice3(sK2,X0,sK4))))).
% 0.21/0.48  
% 0.21/0.48  tff(u175,negated_conjecture,
% 0.21/0.48      (![X1, X2] : ((~sP0(X1,sK2,X2) | r1_lattice3(sK2,X2,X1) | ~r2_hidden(X1,sK3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u174,axiom,
% 0.21/0.48      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4))))).
% 0.21/0.48  
% 0.21/0.48  tff(u173,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r1_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u172,negated_conjecture,
% 0.21/0.48      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | sP0(sK4,sK2,k4_waybel_0(sK2,sK3)))).
% 0.21/0.48  
% 0.21/0.48  tff(u171,negated_conjecture,
% 0.21/0.48      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X0] : ((sP0(X0,sK2,k4_waybel_0(sK2,sK3)) | ~r2_hidden(X0,sK3) | ~r1_orders_2(sK2,X0,sK4)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u170,negated_conjecture,
% 0.21/0.48      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X0] : ((sP0(X0,sK2,k4_waybel_0(sK2,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_orders_2(sK2,X0,sK4)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u169,negated_conjecture,
% 0.21/0.48      ((~r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK4)) | (![X3, X2] : ((sP0(sK5(X2,sK2,X3),sK2,k4_waybel_0(sK2,sK3)) | ~r1_orders_2(sK2,sK5(X2,sK2,X3),sK4) | sP0(X2,sK2,X3)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u168,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r1_lattice3(X1,X0,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u167,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r1_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u166,negated_conjecture,
% 0.21/0.48      (![X0] : (sP1(X0,sK2,sK4)))).
% 0.21/0.48  
% 0.21/0.48  tff(u165,negated_conjecture,
% 0.21/0.48      (![X1, X0] : ((sP1(X1,sK2,X0) | ~r2_hidden(X0,sK3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u164,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.48  
% 0.21/0.48  % (8760)# SZS output end Saturation.
% 0.21/0.48  % (8760)------------------------------
% 0.21/0.48  % (8760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8760)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (8760)Memory used [KB]: 5373
% 0.21/0.48  % (8760)Time elapsed: 0.006 s
% 0.21/0.48  % (8760)------------------------------
% 0.21/0.48  % (8760)------------------------------
% 0.21/0.48  % (8752)Success in time 0.119 s
%------------------------------------------------------------------------------
