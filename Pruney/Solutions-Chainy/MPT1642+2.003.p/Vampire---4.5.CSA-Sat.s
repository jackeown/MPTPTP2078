%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:02 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    0
%              Number of atoms          :   63 (  63 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u95,negated_conjecture,(
    ~ r1_tarski(k6_waybel_0(sK2,sK4),k6_waybel_0(sK2,sK3)) )).

tff(u94,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u93,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) )).

tff(u92,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) )).

tff(u91,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u90,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u89,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u88,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK2)) )).

tff(u87,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK2)) )).

tff(u86,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u85,negated_conjecture,(
    l1_orders_2(sK2) )).

tff(u84,negated_conjecture,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,X0,sK3)
      | sP0(sK3,sK2,X0) ) )).

tff(u83,negated_conjecture,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,X0,sK4)
      | r1_lattice3(sK2,X0,sK3) ) )).

tff(u82,negated_conjecture,(
    ! [X1] :
      ( ~ r1_lattice3(sK2,X1,sK4)
      | sP0(sK4,sK2,X1) ) )).

tff(u81,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK5(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK5(X4,X5,X6),X5,X7) ) )).

tff(u80,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,X0,sK5(X0,X1,X2))
      | sP0(X0,X1,X2) ) )).

tff(u79,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X3,X2)
      | r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u78,negated_conjecture,(
    r1_orders_2(sK2,sK3,sK4) )).

tff(u77,negated_conjecture,(
    v4_orders_2(sK2) )).

tff(u76,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK3,sK2,X0)
      | r1_lattice3(sK2,X0,sK3) ) )).

tff(u75,negated_conjecture,(
    ! [X1] :
      ( ~ sP0(sK4,sK2,X1)
      | r1_lattice3(sK2,X1,sK4) ) )).

tff(u74,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) )).

tff(u73,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK5(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r1_lattice3(X1,X3,sK5(X0,X1,X2)) ) )).

tff(u72,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) )).

tff(u71,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u70,negated_conjecture,(
    ! [X0] : sP1(X0,sK2,sK3) )).

tff(u69,negated_conjecture,(
    ! [X1] : sP1(X1,sK2,sK4) )).

tff(u68,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:04:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (748224512)
% 0.13/0.37  ipcrm: permission denied for id (748912644)
% 0.13/0.37  ipcrm: permission denied for id (748945413)
% 0.13/0.37  ipcrm: permission denied for id (748257286)
% 0.13/0.37  ipcrm: permission denied for id (749043721)
% 0.13/0.37  ipcrm: permission denied for id (749076490)
% 0.13/0.38  ipcrm: permission denied for id (749207566)
% 0.13/0.38  ipcrm: permission denied for id (749273104)
% 0.13/0.39  ipcrm: permission denied for id (749371411)
% 0.13/0.39  ipcrm: permission denied for id (749404180)
% 0.13/0.39  ipcrm: permission denied for id (749436949)
% 0.13/0.39  ipcrm: permission denied for id (749535256)
% 0.13/0.39  ipcrm: permission denied for id (749600794)
% 0.13/0.40  ipcrm: permission denied for id (749764639)
% 0.13/0.40  ipcrm: permission denied for id (749830177)
% 0.13/0.40  ipcrm: permission denied for id (749862946)
% 0.13/0.41  ipcrm: permission denied for id (748355620)
% 0.21/0.41  ipcrm: permission denied for id (749994023)
% 0.21/0.41  ipcrm: permission denied for id (750092330)
% 0.21/0.42  ipcrm: permission denied for id (750190637)
% 0.21/0.42  ipcrm: permission denied for id (750223406)
% 0.21/0.42  ipcrm: permission denied for id (748421167)
% 0.21/0.42  ipcrm: permission denied for id (748453937)
% 0.21/0.43  ipcrm: permission denied for id (750321715)
% 0.21/0.43  ipcrm: permission denied for id (750354484)
% 0.21/0.43  ipcrm: permission denied for id (750387253)
% 0.21/0.43  ipcrm: permission denied for id (750420022)
% 0.21/0.43  ipcrm: permission denied for id (750452791)
% 0.21/0.43  ipcrm: permission denied for id (748486712)
% 0.21/0.43  ipcrm: permission denied for id (750485561)
% 0.21/0.44  ipcrm: permission denied for id (750551099)
% 0.21/0.44  ipcrm: permission denied for id (750583868)
% 0.21/0.44  ipcrm: permission denied for id (748519485)
% 0.21/0.44  ipcrm: permission denied for id (750649407)
% 0.21/0.44  ipcrm: permission denied for id (750682176)
% 0.21/0.44  ipcrm: permission denied for id (750714945)
% 0.21/0.44  ipcrm: permission denied for id (750747714)
% 0.21/0.45  ipcrm: permission denied for id (748552259)
% 0.21/0.45  ipcrm: permission denied for id (750780484)
% 0.21/0.45  ipcrm: permission denied for id (750878791)
% 0.21/0.46  ipcrm: permission denied for id (751075405)
% 0.21/0.46  ipcrm: permission denied for id (748617808)
% 0.21/0.46  ipcrm: permission denied for id (751206481)
% 0.21/0.47  ipcrm: permission denied for id (751370326)
% 0.21/0.47  ipcrm: permission denied for id (748650583)
% 0.21/0.47  ipcrm: permission denied for id (751468634)
% 0.21/0.47  ipcrm: permission denied for id (751501403)
% 0.21/0.48  ipcrm: permission denied for id (751730785)
% 0.21/0.48  ipcrm: permission denied for id (751763554)
% 0.21/0.49  ipcrm: permission denied for id (751829092)
% 0.21/0.49  ipcrm: permission denied for id (751894630)
% 0.21/0.49  ipcrm: permission denied for id (751927399)
% 0.21/0.49  ipcrm: permission denied for id (751960168)
% 0.21/0.49  ipcrm: permission denied for id (752025706)
% 0.21/0.50  ipcrm: permission denied for id (752124013)
% 0.21/0.50  ipcrm: permission denied for id (748683378)
% 0.21/0.50  ipcrm: permission denied for id (752287859)
% 0.21/0.51  ipcrm: permission denied for id (748716148)
% 0.21/0.51  ipcrm: permission denied for id (752320629)
% 0.21/0.51  ipcrm: permission denied for id (748748919)
% 0.21/0.62  % (12778)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.62  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.62  % (12778)# SZS output start Saturation.
% 0.21/0.62  tff(u95,negated_conjecture,
% 0.21/0.62      ~r1_tarski(k6_waybel_0(sK2,sK4),k6_waybel_0(sK2,sK3))).
% 0.21/0.62  
% 0.21/0.62  tff(u94,axiom,
% 0.21/0.62      (![X0] : (r1_tarski(X0,X0)))).
% 0.21/0.62  
% 0.21/0.62  tff(u93,axiom,
% 0.21/0.62      (![X1, X0] : ((~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.21/0.62  
% 0.21/0.62  tff(u92,axiom,
% 0.21/0.62      (![X1, X0] : ((r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.21/0.62  
% 0.21/0.62  tff(u91,axiom,
% 0.21/0.62      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.21/0.62  
% 0.21/0.62  tff(u90,axiom,
% 0.21/0.62      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.62  
% 0.21/0.62  tff(u89,axiom,
% 0.21/0.62      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1))))).
% 0.21/0.62  
% 0.21/0.62  tff(u88,negated_conjecture,
% 0.21/0.62      m1_subset_1(sK3,u1_struct_0(sK2))).
% 0.21/0.62  
% 0.21/0.62  tff(u87,negated_conjecture,
% 0.21/0.62      m1_subset_1(sK4,u1_struct_0(sK2))).
% 0.21/0.62  
% 0.21/0.62  tff(u86,axiom,
% 0.21/0.62      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.21/0.62  
% 0.21/0.62  tff(u85,negated_conjecture,
% 0.21/0.62      l1_orders_2(sK2)).
% 0.21/0.62  
% 0.21/0.62  tff(u84,negated_conjecture,
% 0.21/0.62      (![X0] : ((~r1_lattice3(sK2,X0,sK3) | sP0(sK3,sK2,X0))))).
% 0.21/0.62  
% 0.21/0.62  tff(u83,negated_conjecture,
% 0.21/0.62      (![X0] : ((~r1_lattice3(sK2,X0,sK4) | r1_lattice3(sK2,X0,sK3))))).
% 0.21/0.62  
% 0.21/0.62  tff(u82,negated_conjecture,
% 0.21/0.62      (![X1] : ((~r1_lattice3(sK2,X1,sK4) | sP0(sK4,sK2,X1))))).
% 0.21/0.62  
% 0.21/0.62  tff(u81,axiom,
% 0.21/0.62      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK5(X4,X5,X6),X5,X7))))).
% 0.21/0.62  
% 0.21/0.62  tff(u80,axiom,
% 0.21/0.62      (![X1, X0, X2] : ((~r1_orders_2(X1,X0,sK5(X0,X1,X2)) | sP0(X0,X1,X2))))).
% 0.21/0.62  
% 0.21/0.62  tff(u79,axiom,
% 0.21/0.62      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X3,X2) | r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.21/0.62  
% 0.21/0.62  tff(u78,negated_conjecture,
% 0.21/0.62      r1_orders_2(sK2,sK3,sK4)).
% 0.21/0.62  
% 0.21/0.62  tff(u77,negated_conjecture,
% 0.21/0.62      v4_orders_2(sK2)).
% 0.21/0.62  
% 0.21/0.62  tff(u76,negated_conjecture,
% 0.21/0.62      (![X0] : ((~sP0(sK3,sK2,X0) | r1_lattice3(sK2,X0,sK3))))).
% 0.21/0.62  
% 0.21/0.62  tff(u75,negated_conjecture,
% 0.21/0.62      (![X1] : ((~sP0(sK4,sK2,X1) | r1_lattice3(sK2,X1,sK4))))).
% 0.21/0.62  
% 0.21/0.62  tff(u74,axiom,
% 0.21/0.62      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4))))).
% 0.21/0.62  
% 0.21/0.62  tff(u73,axiom,
% 0.21/0.62      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r1_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.21/0.62  
% 0.21/0.62  tff(u72,axiom,
% 0.21/0.62      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r1_lattice3(X1,X0,X2))))).
% 0.21/0.62  
% 0.21/0.62  tff(u71,axiom,
% 0.21/0.62      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r1_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.21/0.62  
% 0.21/0.62  tff(u70,negated_conjecture,
% 0.21/0.62      (![X0] : (sP1(X0,sK2,sK3)))).
% 0.21/0.62  
% 0.21/0.62  tff(u69,negated_conjecture,
% 0.21/0.62      (![X1] : (sP1(X1,sK2,sK4)))).
% 0.21/0.62  
% 0.21/0.62  tff(u68,axiom,
% 0.21/0.62      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.62  
% 0.21/0.62  % (12778)# SZS output end Saturation.
% 0.21/0.62  % (12778)------------------------------
% 0.21/0.62  % (12778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.62  % (12778)Termination reason: Satisfiable
% 0.21/0.62  
% 0.21/0.62  % (12778)Memory used [KB]: 5373
% 0.21/0.62  % (12778)Time elapsed: 0.004 s
% 0.21/0.62  % (12778)------------------------------
% 0.21/0.62  % (12778)------------------------------
% 0.21/0.62  % (12613)Success in time 0.266 s
%------------------------------------------------------------------------------
