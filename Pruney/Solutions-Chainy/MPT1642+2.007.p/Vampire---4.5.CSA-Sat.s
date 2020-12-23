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
% DateTime   : Thu Dec  3 13:17:03 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   29 (  29 expanded)
%              Depth                    :    0
%              Number of atoms          :  128 ( 128 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u131,negated_conjecture,(
    ~ r1_tarski(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1)) )).

tff(u130,axiom,(
    ! [X3,X5,X2,X4] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK3(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) )).

tff(u129,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u128,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u127,axiom,(
    ! [X1,X3,X0] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u126,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u125,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK3(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) )).

tff(u124,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u123,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u122,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u121,negated_conjecture,(
    v4_orders_2(sK0) )).

tff(u120,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u119,axiom,(
    ! [X9,X11,X8,X10,X12] :
      ( ~ r1_orders_2(X8,X11,X10)
      | ~ r1_orders_2(X8,X9,X10)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | r2_lattice3(X8,k2_tarski(X11,X9),X12)
      | ~ r1_orders_2(X8,X10,X12)
      | ~ m1_subset_1(X12,u1_struct_0(X8))
      | ~ v4_orders_2(X8) ) )).

tff(u118,axiom,(
    ! [X9,X11,X8,X10,X12] :
      ( ~ r1_orders_2(X8,X12,X9)
      | ~ r1_orders_2(X8,X9,X11)
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | r1_lattice3(X8,k2_tarski(X11,X10),X12)
      | ~ r1_orders_2(X8,X9,X10)
      | ~ m1_subset_1(X12,u1_struct_0(X8))
      | ~ v4_orders_2(X8) ) )).

tff(u117,negated_conjecture,(
    ! [X9,X7,X8,X6] :
      ( ~ r1_orders_2(sK0,sK2,X7)
      | ~ r1_orders_2(sK0,sK2,X6)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X8,sK1)
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | r1_lattice3(sK0,k2_tarski(X6,X7),X9)
      | ~ r1_orders_2(sK0,X9,X8)
      | ~ m1_subset_1(X9,u1_struct_0(sK0)) ) )).

tff(u116,negated_conjecture,
    ( ~ ! [X1] :
          ( ~ r1_orders_2(sK0,sK2,X1)
          | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ! [X1] :
        ( ~ r1_orders_2(sK0,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) )).

tff(u115,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r1_orders_2(sK0,sK2,X0)
          | r1_orders_2(sK0,sK1,X0)
          | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u114,negated_conjecture,(
    r1_orders_2(sK0,sK1,sK2) )).

tff(u113,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u112,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u111,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_lattice3(X0,X3,X2)
      | r1_lattice3(X0,X3,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u110,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u109,negated_conjecture,(
    ! [X1,X0] :
      ( r1_lattice3(sK0,k2_tarski(X0,X1),sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK2,X0)
      | ~ r1_orders_2(sK0,sK2,X1) ) )).

tff(u108,negated_conjecture,(
    ! [X5,X4,X6] :
      ( r1_lattice3(sK0,k2_tarski(X5,X4),X6)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK2,X5)
      | ~ r1_orders_2(sK0,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X6,sK1)
      | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) )).

tff(u107,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u106,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u105,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,X3,X1)
      | r2_lattice3(X0,X3,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u104,axiom,(
    ! [X1,X3,X0,X2] :
      ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u103,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (22860)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.20/0.45  % (22860)Refutation not found, incomplete strategy% (22860)------------------------------
% 0.20/0.45  % (22860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (22870)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.20/0.46  % (22864)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  % (22860)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (22860)Memory used [KB]: 9850
% 0.20/0.46  % (22860)Time elapsed: 0.049 s
% 0.20/0.46  % (22860)------------------------------
% 0.20/0.46  % (22860)------------------------------
% 0.20/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.46  % (22870)# SZS output start Saturation.
% 0.20/0.46  tff(u131,negated_conjecture,
% 0.20/0.46      ~r1_tarski(k6_waybel_0(sK0,sK2),k6_waybel_0(sK0,sK1))).
% 0.20/0.46  
% 0.20/0.46  tff(u130,axiom,
% 0.20/0.46      (![X3, X5, X2, X4] : ((~r1_tarski(X3,X5) | r1_tarski(X2,X4) | r2_hidden(sK3(X2,X4),X5) | ~r1_tarski(X2,X3))))).
% 0.20/0.46  
% 0.20/0.46  tff(u129,axiom,
% 0.20/0.46      (![X0] : (r1_tarski(X0,X0)))).
% 0.20/0.46  
% 0.20/0.46  tff(u128,axiom,
% 0.20/0.46      (![X1, X0] : ((~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.20/0.46  
% 0.20/0.46  tff(u127,axiom,
% 0.20/0.46      (![X1, X3, X0] : ((~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1))))).
% 0.20/0.46  
% 0.20/0.46  tff(u126,axiom,
% 0.20/0.46      (![X1, X0] : ((r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.20/0.46  
% 0.20/0.46  tff(u125,axiom,
% 0.20/0.46      (![X1, X0, X2] : ((r2_hidden(sK3(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1))))).
% 0.20/0.46  
% 0.20/0.46  tff(u124,axiom,
% 0.20/0.46      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1))))).
% 0.20/0.46  
% 0.20/0.46  tff(u123,negated_conjecture,
% 0.20/0.46      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  tff(u122,negated_conjecture,
% 0.20/0.46      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  tff(u121,negated_conjecture,
% 0.20/0.46      v4_orders_2(sK0)).
% 0.20/0.46  
% 0.20/0.46  tff(u120,negated_conjecture,
% 0.20/0.46      l1_orders_2(sK0)).
% 0.20/0.46  
% 0.20/0.46  tff(u119,axiom,
% 0.20/0.46      (![X9, X11, X8, X10, X12] : ((~r1_orders_2(X8,X11,X10) | ~r1_orders_2(X8,X9,X10) | ~m1_subset_1(X9,u1_struct_0(X8)) | ~m1_subset_1(X11,u1_struct_0(X8)) | ~m1_subset_1(X10,u1_struct_0(X8)) | ~l1_orders_2(X8) | r2_lattice3(X8,k2_tarski(X11,X9),X12) | ~r1_orders_2(X8,X10,X12) | ~m1_subset_1(X12,u1_struct_0(X8)) | ~v4_orders_2(X8))))).
% 0.20/0.46  
% 0.20/0.46  tff(u118,axiom,
% 0.20/0.46      (![X9, X11, X8, X10, X12] : ((~r1_orders_2(X8,X12,X9) | ~r1_orders_2(X8,X9,X11) | ~m1_subset_1(X10,u1_struct_0(X8)) | ~m1_subset_1(X11,u1_struct_0(X8)) | ~m1_subset_1(X9,u1_struct_0(X8)) | ~l1_orders_2(X8) | r1_lattice3(X8,k2_tarski(X11,X10),X12) | ~r1_orders_2(X8,X9,X10) | ~m1_subset_1(X12,u1_struct_0(X8)) | ~v4_orders_2(X8))))).
% 0.20/0.46  
% 0.20/0.46  tff(u117,negated_conjecture,
% 0.20/0.46      (![X9, X7, X8, X6] : ((~r1_orders_2(sK0,sK2,X7) | ~r1_orders_2(sK0,sK2,X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X8,sK1) | ~m1_subset_1(X8,u1_struct_0(sK0)) | r1_lattice3(sK0,k2_tarski(X6,X7),X9) | ~r1_orders_2(sK0,X9,X8) | ~m1_subset_1(X9,u1_struct_0(sK0)))))).
% 0.20/0.46  
% 0.20/0.46  tff(u116,negated_conjecture,
% 0.20/0.46      ((~(![X1] : ((~r1_orders_2(sK0,sK2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))))) | (![X1] : ((~r1_orders_2(sK0,sK2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))))))).
% 0.20/0.46  
% 0.20/0.46  tff(u115,negated_conjecture,
% 0.20/0.46      ((~(![X0] : ((~r1_orders_2(sK0,sK2,X0) | r1_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))))) | (![X0] : ((~r1_orders_2(sK0,sK2,X0) | r1_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 0.20/0.46  
% 0.20/0.46  tff(u114,negated_conjecture,
% 0.20/0.46      r1_orders_2(sK0,sK1,sK2)).
% 0.20/0.46  
% 0.20/0.46  tff(u113,axiom,
% 0.20/0.46      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,k2_tarski(X2,X3),X1) | r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u112,axiom,
% 0.20/0.46      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,k2_tarski(X2,X3),X1) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u111,axiom,
% 0.20/0.46      (![X1, X3, X0, X2] : ((~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X3,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u110,axiom,
% 0.20/0.46      (![X1, X3, X0, X2] : ((r1_lattice3(X0,k2_tarski(X2,X3),X1) | ~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u109,negated_conjecture,
% 0.20/0.46      (![X1, X0] : ((r1_lattice3(sK0,k2_tarski(X0,X1),sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X0) | ~r1_orders_2(sK0,sK2,X1))))).
% 0.20/0.46  
% 0.20/0.46  tff(u108,negated_conjecture,
% 0.20/0.46      (![X5, X4, X6] : ((r1_lattice3(sK0,k2_tarski(X5,X4),X6) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X5) | ~r1_orders_2(sK0,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X6,sK1) | ~m1_subset_1(X6,u1_struct_0(sK0)))))).
% 0.20/0.46  
% 0.20/0.46  tff(u107,axiom,
% 0.20/0.46      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,k2_tarski(X2,X3),X1) | r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u106,axiom,
% 0.20/0.46      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,k2_tarski(X2,X3),X1) | r1_orders_2(X0,X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u105,axiom,
% 0.20/0.46      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u104,axiom,
% 0.20/0.46      (![X1, X3, X0, X2] : ((r2_lattice3(X0,k2_tarski(X2,X3),X1) | ~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u103,negated_conjecture,
% 0.20/0.46      ~v2_struct_0(sK0)).
% 0.20/0.46  
% 0.20/0.46  % (22870)# SZS output end Saturation.
% 0.20/0.46  % (22870)------------------------------
% 0.20/0.46  % (22870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (22870)Termination reason: Satisfiable
% 0.20/0.46  
% 0.20/0.46  % (22870)Memory used [KB]: 5373
% 0.20/0.46  % (22870)Time elapsed: 0.057 s
% 0.20/0.46  % (22870)------------------------------
% 0.20/0.46  % (22870)------------------------------
% 0.20/0.46  % (22850)Success in time 0.113 s
%------------------------------------------------------------------------------
