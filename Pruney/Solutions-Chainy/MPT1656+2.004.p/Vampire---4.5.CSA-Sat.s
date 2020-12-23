%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:09 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    0
%              Number of atoms          :  116 ( 116 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u115,negated_conjecture,(
    v4_orders_2(sK0) )).

tff(u114,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u113,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK3(X1,k4_waybel_0(sK0,sK1),X2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3(X1,k4_waybel_0(sK0,sK1),X2))
        | r1_lattice3(X1,k4_waybel_0(sK0,sK1),X2)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ l1_orders_2(X1) ) )).

tff(u112,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK3(X0,k4_waybel_0(sK0,sK1),X1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,sK3(X0,k4_waybel_0(sK0,sK1),X1))
        | r1_lattice3(X0,k4_waybel_0(sK0,sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) )).

tff(u111,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X1,X3,X2] :
        ( ~ m1_subset_1(sK3(sK0,k4_waybel_0(sK0,sK1),X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,sK2)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,sK3(sK0,k4_waybel_0(sK0,sK1),X1))
        | ~ r1_orders_2(sK0,X3,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) )).

tff(u110,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK3(sK0,k4_waybel_0(sK0,sK1),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),X0))
        | ~ r1_orders_2(sK0,X1,sK2)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) )).

tff(u109,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u108,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u107,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u106,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u105,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u104,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,X2,X0)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK3(sK0,k4_waybel_0(sK0,sK1),X1))
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) )).

tff(u103,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( r1_orders_2(sK0,sK2,sK3(sK0,k4_waybel_0(sK0,sK1),X0))
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u102,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X1,X0] :
        ( r1_orders_2(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,sK2)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) )).

tff(u101,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK1,sK2)
    | ~ r1_lattice3(sK0,sK1,sK2) )).

tff(u100,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u99,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,X2,X3)
      | r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u98,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2) )).

tff(u97,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X0)
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u96,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X1,X0] :
        ( ~ r2_hidden(X1,k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1) ) )).

tff(u95,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0) ) )).

tff(u94,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u93,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X3,X2] :
        ( ~ r1_tarski(X3,k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattice3(sK0,X3,X2)
        | ~ r1_orders_2(sK0,X2,sK2) ) )).

tff(u92,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( ~ r1_tarski(X0,k4_waybel_0(sK0,sK1))
        | r1_lattice3(sK0,X0,sK2) ) )).

tff(u91,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,X2,X3)
      | r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u90,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u89,negated_conjecture,(
    v3_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (24172)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (24174)WARNING: option uwaf not known.
% 0.20/0.48  % (24183)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.20/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.48  % (24183)# SZS output start Saturation.
% 0.20/0.48  tff(u115,negated_conjecture,
% 0.20/0.48      v4_orders_2(sK0)).
% 0.20/0.48  
% 0.20/0.48  tff(u114,negated_conjecture,
% 0.20/0.48      l1_orders_2(sK0)).
% 0.20/0.48  
% 0.20/0.48  tff(u113,negated_conjecture,
% 0.20/0.48      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X1, X0, X2] : ((~m1_subset_1(sK3(X1,k4_waybel_0(sK0,sK1),X2),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK3(X1,k4_waybel_0(sK0,sK1),X2)) | r1_lattice3(X1,k4_waybel_0(sK0,sK1),X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1)))))).
% 0.20/0.48  
% 0.20/0.48  tff(u112,negated_conjecture,
% 0.20/0.48      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X1, X0] : ((~m1_subset_1(sK3(X0,k4_waybel_0(sK0,sK1),X1),u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,sK3(X0,k4_waybel_0(sK0,sK1),X1)) | r1_lattice3(X0,k4_waybel_0(sK0,sK1),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))))).
% 0.20/0.48  
% 0.20/0.48  tff(u111,negated_conjecture,
% 0.20/0.48      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X1, X3, X2] : ((~m1_subset_1(sK3(sK0,k4_waybel_0(sK0,sK1),X1),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,sK2) | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_orders_2(sK0,X3,sK3(sK0,k4_waybel_0(sK0,sK1),X1)) | ~r1_orders_2(sK0,X3,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))))))).
% 0.20/0.48  
% 0.20/0.48  tff(u110,negated_conjecture,
% 0.20/0.48      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X1, X0] : ((~m1_subset_1(sK3(sK0,k4_waybel_0(sK0,sK1),X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),X0)) | ~r1_orders_2(sK0,X1,sK2) | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0))))))).
% 0.20/0.48  
% 0.20/0.48  tff(u109,negated_conjecture,
% 0.20/0.48      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.48  
% 0.20/0.48  tff(u108,negated_conjecture,
% 0.20/0.48      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.48  
% 0.20/0.48  tff(u107,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u106,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u105,axiom,
% 0.20/0.48      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u104,negated_conjecture,
% 0.20/0.48      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X1, X0, X2] : ((~r1_orders_2(sK0,X2,X0) | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X2,sK3(sK0,k4_waybel_0(sK0,sK1),X1)) | ~r1_orders_2(sK0,X0,sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))))))).
% 0.20/0.48  
% 0.20/0.48  tff(u103,negated_conjecture,
% 0.20/0.48      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X0] : ((r1_orders_2(sK0,sK2,sK3(sK0,k4_waybel_0(sK0,sK1),X0)) | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 0.20/0.48  
% 0.20/0.48  tff(u102,negated_conjecture,
% 0.20/0.48      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X1, X0] : ((r1_orders_2(sK0,X1,sK3(sK0,k4_waybel_0(sK0,sK1),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK2) | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0))))))).
% 0.20/0.48  
% 0.20/0.48  tff(u101,negated_conjecture,
% 0.20/0.48      ((~~r1_lattice3(sK0,sK1,sK2)) | ~r1_lattice3(sK0,sK1,sK2))).
% 0.20/0.48  
% 0.20/0.48  tff(u100,axiom,
% 0.20/0.48      (![X1, X0, X2, X4] : ((~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u99,axiom,
% 0.20/0.48      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u98,negated_conjecture,
% 0.20/0.48      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2))).
% 0.20/0.48  
% 0.20/0.48  tff(u97,negated_conjecture,
% 0.20/0.48      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X0] : ((r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X0) | ~r1_orders_2(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 0.20/0.48  
% 0.20/0.48  tff(u96,negated_conjecture,
% 0.20/0.48      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X1, X0] : ((~r2_hidden(X1,k4_waybel_0(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1)))))).
% 0.20/0.48  
% 0.20/0.48  tff(u95,negated_conjecture,
% 0.20/0.48      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X0] : ((~r2_hidden(X0,k4_waybel_0(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,X0)))))).
% 0.20/0.48  
% 0.20/0.48  tff(u94,axiom,
% 0.20/0.48      (![X1, X0, X2] : ((r2_hidden(sK3(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u93,negated_conjecture,
% 0.20/0.48      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X3, X2] : ((~r1_tarski(X3,k4_waybel_0(sK0,sK1)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattice3(sK0,X3,X2) | ~r1_orders_2(sK0,X2,sK2)))))).
% 0.20/0.48  
% 0.20/0.48  tff(u92,negated_conjecture,
% 0.20/0.48      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X0] : ((~r1_tarski(X0,k4_waybel_0(sK0,sK1)) | r1_lattice3(sK0,X0,sK2)))))).
% 0.20/0.48  
% 0.20/0.48  tff(u91,axiom,
% 0.20/0.48      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0))))).
% 0.20/0.48  
% 0.20/0.48  tff(u90,negated_conjecture,
% 0.20/0.48      ~v2_struct_0(sK0)).
% 0.20/0.48  
% 0.20/0.48  tff(u89,negated_conjecture,
% 0.20/0.48      v3_orders_2(sK0)).
% 0.20/0.48  
% 0.20/0.48  % (24183)# SZS output end Saturation.
% 0.20/0.48  % (24183)------------------------------
% 0.20/0.48  % (24183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (24183)Termination reason: Satisfiable
% 0.20/0.48  
% 0.20/0.48  % (24183)Memory used [KB]: 5373
% 0.20/0.48  % (24183)Time elapsed: 0.068 s
% 0.20/0.48  % (24183)------------------------------
% 0.20/0.48  % (24183)------------------------------
% 0.20/0.48  % (24163)Success in time 0.127 s
%------------------------------------------------------------------------------
