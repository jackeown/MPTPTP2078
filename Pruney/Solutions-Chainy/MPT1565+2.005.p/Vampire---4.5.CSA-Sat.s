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
% DateTime   : Thu Dec  3 13:16:15 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 (  71 expanded)
%              Number of leaves         :   71 (  71 expanded)
%              Depth                    :    0
%              Number of atoms          :  223 ( 223 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u240,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u239,axiom,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) )).

tff(u238,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) )).

tff(u237,axiom,(
    ! [X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u236,axiom,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) )).

tff(u235,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u234,axiom,(
    ! [X9,X8,X10] :
      ( r2_hidden(sK5(X8,X9,X10),u1_struct_0(X9))
      | v1_xboole_0(u1_struct_0(X9))
      | sP0(X8,X9,X10) ) )).

tff(u233,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | sP2(X0,X1,X2) ) )).

tff(u232,axiom,(
    ! [X9,X8,X10] :
      ( r2_hidden(sK6(X8,X9,X10),u1_struct_0(X9))
      | v1_xboole_0(u1_struct_0(X9))
      | sP2(X8,X9,X10) ) )).

tff(u231,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) )).

tff(u230,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP3(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u229,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u228,axiom,(
    ! [X0] :
      ( m1_subset_1(sK7(X0),X0)
      | v1_xboole_0(X0) ) )).

tff(u227,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u226,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u225,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK6(X0,X1,X2),X2)
      | sP2(X0,X1,X2) ) )).

tff(u224,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | sP2(X0,X1,X2) ) )).

tff(u223,negated_conjecture,(
    ~ v2_struct_0(sK4) )).

tff(u222,negated_conjecture,(
    l1_struct_0(sK4) )).

tff(u221,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u220,negated_conjecture,(
    l1_orders_2(sK4) )).

tff(u219,axiom,(
    ! [X1,X0] :
      ( ~ r1_lattice3(X0,X1,sK7(u1_struct_0(X0)))
      | sP2(sK7(u1_struct_0(X0)),X0,X1)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) )).

tff(u218,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK5(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP2(sK5(X4,X5,X6),X5,X7) ) )).

tff(u217,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X6,X7,sK5(X4,X5,u1_struct_0(X6)))
      | ~ l1_orders_2(X6)
      | sP0(X4,X5,u1_struct_0(X6))
      | sP2(sK5(X4,X5,u1_struct_0(X6)),X6,X7) ) )).

tff(u216,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X5,X7,sK6(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP2(X4,X5,X6)
      | sP2(sK6(X4,X5,X6),X5,X7) ) )).

tff(u215,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_lattice3(X6,X7,sK6(X4,X5,u1_struct_0(X6)))
      | ~ l1_orders_2(X6)
      | sP2(X4,X5,u1_struct_0(X6))
      | sP2(sK6(X4,X5,u1_struct_0(X6)),X6,X7) ) )).

tff(u214,axiom,(
    ! [X1,X0] :
      ( r1_lattice3(X0,X1,sK7(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | ~ v1_xboole_0(X1) ) )).

tff(u213,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_lattice3(X0,X3,sK5(X1,X0,X2))
      | sP0(X1,X0,X2)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u212,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_lattice3(X0,X3,sK5(X1,X2,u1_struct_0(X0)))
      | sP0(X1,X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u211,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_lattice3(X0,X3,sK6(X1,X0,X2))
      | sP2(X1,X0,X2)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u210,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_lattice3(X0,X3,sK6(X1,X2,u1_struct_0(X0)))
      | sP2(X1,X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u209,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,sK5(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) )).

tff(u208,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,X0,sK6(X0,X1,X2))
      | sP2(X0,X1,X2) ) )).

tff(u207,axiom,(
    ! [X1,X0] :
      ( ~ r2_lattice3(X0,X1,sK7(u1_struct_0(X0)))
      | sP0(sK7(u1_struct_0(X0)),X0,X1)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) )).

tff(u206,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK5(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK5(X4,X5,X6),X5,X7) ) )).

tff(u205,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X6,X7,sK5(X4,X5,u1_struct_0(X6)))
      | ~ l1_orders_2(X6)
      | sP0(X4,X5,u1_struct_0(X6))
      | sP0(sK5(X4,X5,u1_struct_0(X6)),X6,X7) ) )).

tff(u204,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK6(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP2(X4,X5,X6)
      | sP0(sK6(X4,X5,X6),X5,X7) ) )).

tff(u203,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X6,X7,sK6(X4,X5,u1_struct_0(X6)))
      | ~ l1_orders_2(X6)
      | sP2(X4,X5,u1_struct_0(X6))
      | sP0(sK6(X4,X5,u1_struct_0(X6)),X6,X7) ) )).

tff(u202,axiom,(
    ! [X1,X0] :
      ( r2_lattice3(X0,X1,sK7(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0))
      | ~ v1_xboole_0(X1) ) )).

% (9297)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
tff(u201,axiom,(
    ! [X1,X3,X0,X2] :
      ( r2_lattice3(X0,X3,sK5(X1,X0,X2))
      | sP0(X1,X0,X2)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u200,axiom,(
    ! [X1,X3,X0,X2] :
      ( r2_lattice3(X0,X3,sK5(X1,X2,u1_struct_0(X0)))
      | sP0(X1,X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u199,axiom,(
    ! [X1,X3,X0,X2] :
      ( r2_lattice3(X0,X3,sK6(X1,X0,X2))
      | sP2(X1,X0,X2)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u198,axiom,(
    ! [X1,X3,X0,X2] :
      ( r2_lattice3(X0,X3,sK6(X1,X2,u1_struct_0(X0)))
      | sP2(X1,X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u197,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) )).

tff(u196,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK5(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r2_lattice3(X1,X3,sK5(X0,X1,X2)) ) )).

tff(u195,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK5(X0,X1,u1_struct_0(X2)),X2,X3)
      | ~ l1_orders_2(X2)
      | sP0(X0,X1,u1_struct_0(X2))
      | r2_lattice3(X2,X3,sK5(X0,X1,u1_struct_0(X2))) ) )).

tff(u194,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK6(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP2(X0,X1,X2)
      | r2_lattice3(X1,X3,sK6(X0,X1,X2)) ) )).

tff(u193,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK6(X0,X1,u1_struct_0(X2)),X2,X3)
      | ~ l1_orders_2(X2)
      | sP2(X0,X1,u1_struct_0(X2))
      | r2_lattice3(X2,X3,sK6(X0,X1,u1_struct_0(X2))) ) )).

tff(u192,axiom,(
    ! [X1,X0] :
      ( ~ sP0(sK7(u1_struct_0(X0)),X0,X1)
      | r2_lattice3(X0,X1,sK7(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) )).

tff(u191,axiom,(
    ! [X3,X5,X4] :
      ( sP0(X3,X4,X5)
      | ~ v1_xboole_0(X5) ) )).

tff(u190,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) )).

tff(u189,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u188,axiom,(
    ! [X1,X0] :
      ( sP1(X0,X1,sK7(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v1_xboole_0(u1_struct_0(X1)) ) )).

tff(u187,axiom,(
    ! [X5,X7,X4,X6] :
      ( sP1(X7,X5,sK5(X4,X5,X6))
      | sP0(X4,X5,X6)
      | ~ l1_orders_2(X5) ) )).

tff(u186,axiom,(
    ! [X9,X7,X8,X10] :
      ( sP1(X10,X9,sK5(X7,X8,u1_struct_0(X9)))
      | sP0(X7,X8,u1_struct_0(X9))
      | ~ l1_orders_2(X9) ) )).

tff(u185,axiom,(
    ! [X5,X7,X4,X6] :
      ( sP1(X7,X5,sK6(X4,X5,X6))
      | sP2(X4,X5,X6)
      | ~ l1_orders_2(X5) ) )).

tff(u184,axiom,(
    ! [X9,X7,X8,X10] :
      ( sP1(X10,X9,sK6(X7,X8,u1_struct_0(X9)))
      | sP2(X7,X8,u1_struct_0(X9))
      | ~ l1_orders_2(X9) ) )).

tff(u183,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) )).

% (9296)Refutation not found, incomplete strategy% (9296)------------------------------
% (9296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9293)Refutation not found, incomplete strategy% (9293)------------------------------
% (9293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
tff(u182,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP2(sK5(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r1_lattice3(X1,X3,sK5(X0,X1,X2)) ) )).

tff(u181,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP2(sK5(X0,X1,u1_struct_0(X2)),X2,X3)
      | ~ l1_orders_2(X2)
      | sP0(X0,X1,u1_struct_0(X2))
      | r1_lattice3(X2,X3,sK5(X0,X1,u1_struct_0(X2))) ) )).

tff(u180,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP2(sK6(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP2(X0,X1,X2)
      | r1_lattice3(X1,X3,sK6(X0,X1,X2)) ) )).

tff(u179,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP2(sK6(X0,X1,u1_struct_0(X2)),X2,X3)
      | ~ l1_orders_2(X2)
      | sP2(X0,X1,u1_struct_0(X2))
      | r1_lattice3(X2,X3,sK6(X0,X1,u1_struct_0(X2))) ) )).

tff(u178,axiom,(
    ! [X1,X0] :
      ( ~ sP2(sK7(u1_struct_0(X0)),X0,X1)
      | r1_lattice3(X0,X1,sK7(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) )).

tff(u177,axiom,(
    ! [X3,X5,X4] :
      ( sP2(X3,X4,X5)
      | ~ v1_xboole_0(X5) ) )).

tff(u176,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP3(X0,X1,X2)
      | ~ sP2(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) )).

tff(u175,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP3(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP2(X2,X1,X0) ) )).

tff(u174,axiom,(
    ! [X1,X0] :
      ( sP3(X0,X1,sK7(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v1_xboole_0(u1_struct_0(X1)) ) )).

tff(u173,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP3(X3,X1,sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

tff(u172,axiom,(
    ! [X3,X5,X4,X6] :
      ( sP3(X6,X5,sK5(X3,X4,u1_struct_0(X5)))
      | sP0(X3,X4,u1_struct_0(X5))
      | ~ l1_orders_2(X5) ) )).

tff(u171,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP3(X3,X1,sK6(X0,X1,X2))
      | sP2(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

tff(u170,axiom,(
    ! [X3,X5,X4,X6] :
      ( sP3(X6,X5,sK6(X3,X4,u1_struct_0(X5)))
      | sP2(X3,X4,u1_struct_0(X5))
      | ~ l1_orders_2(X5) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:28:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (9301)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.47  % (9296)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.47  % (9293)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.48  % (9309)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (9301)# SZS output start Saturation.
% 0.21/0.48  tff(u240,axiom,
% 0.21/0.48      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u239,axiom,
% 0.21/0.48      (![X0] : ((v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u238,axiom,
% 0.21/0.48      (![X1, X0] : ((~r2_hidden(X0,X1) | m1_subset_1(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u237,axiom,
% 0.21/0.48      (![X0, X2] : ((~r2_hidden(X2,X0) | ~v1_xboole_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u236,axiom,
% 0.21/0.48      (![X0] : ((r2_hidden(sK7(X0),X0) | v1_xboole_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u235,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u234,axiom,
% 0.21/0.48      (![X9, X8, X10] : ((r2_hidden(sK5(X8,X9,X10),u1_struct_0(X9)) | v1_xboole_0(u1_struct_0(X9)) | sP0(X8,X9,X10))))).
% 0.21/0.48  
% 0.21/0.48  tff(u233,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((r2_hidden(sK6(X0,X1,X2),X2) | sP2(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u232,axiom,
% 0.21/0.48      (![X9, X8, X10] : ((r2_hidden(sK6(X8,X9,X10),u1_struct_0(X9)) | v1_xboole_0(u1_struct_0(X9)) | sP2(X8,X9,X10))))).
% 0.21/0.48  
% 0.21/0.48  tff(u231,axiom,
% 0.21/0.48      (![X1, X0] : ((~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u230,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP3(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u229,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u228,axiom,
% 0.21/0.48      (![X0] : ((m1_subset_1(sK7(X0),X0) | v1_xboole_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u227,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u226,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u225,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((m1_subset_1(sK6(X0,X1,X2),X2) | sP2(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u224,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) | sP2(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u223,negated_conjecture,
% 0.21/0.48      ~v2_struct_0(sK4)).
% 0.21/0.48  
% 0.21/0.48  tff(u222,negated_conjecture,
% 0.21/0.48      l1_struct_0(sK4)).
% 0.21/0.48  
% 0.21/0.48  tff(u221,axiom,
% 0.21/0.48      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u220,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK4)).
% 0.21/0.48  
% 0.21/0.48  tff(u219,axiom,
% 0.21/0.48      (![X1, X0] : ((~r1_lattice3(X0,X1,sK7(u1_struct_0(X0))) | sP2(sK7(u1_struct_0(X0)),X0,X1) | ~l1_orders_2(X0) | v1_xboole_0(u1_struct_0(X0)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u218,axiom,
% 0.21/0.48      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP2(sK5(X4,X5,X6),X5,X7))))).
% 0.21/0.48  
% 0.21/0.48  tff(u217,axiom,
% 0.21/0.48      (![X5, X7, X4, X6] : ((~r1_lattice3(X6,X7,sK5(X4,X5,u1_struct_0(X6))) | ~l1_orders_2(X6) | sP0(X4,X5,u1_struct_0(X6)) | sP2(sK5(X4,X5,u1_struct_0(X6)),X6,X7))))).
% 0.21/0.48  
% 0.21/0.48  tff(u216,axiom,
% 0.21/0.48      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK6(X4,X5,X6)) | ~l1_orders_2(X5) | sP2(X4,X5,X6) | sP2(sK6(X4,X5,X6),X5,X7))))).
% 0.21/0.48  
% 0.21/0.48  tff(u215,axiom,
% 0.21/0.48      (![X5, X7, X4, X6] : ((~r1_lattice3(X6,X7,sK6(X4,X5,u1_struct_0(X6))) | ~l1_orders_2(X6) | sP2(X4,X5,u1_struct_0(X6)) | sP2(sK6(X4,X5,u1_struct_0(X6)),X6,X7))))).
% 0.21/0.48  
% 0.21/0.48  tff(u214,axiom,
% 0.21/0.48      (![X1, X0] : ((r1_lattice3(X0,X1,sK7(u1_struct_0(X0))) | ~l1_orders_2(X0) | v1_xboole_0(u1_struct_0(X0)) | ~v1_xboole_0(X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u213,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((r1_lattice3(X0,X3,sK5(X1,X0,X2)) | sP0(X1,X0,X2) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u212,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((r1_lattice3(X0,X3,sK5(X1,X2,u1_struct_0(X0))) | sP0(X1,X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u211,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((r1_lattice3(X0,X3,sK6(X1,X0,X2)) | sP2(X1,X0,X2) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u210,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((r1_lattice3(X0,X3,sK6(X1,X2,u1_struct_0(X0))) | sP2(X1,X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u209,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r1_orders_2(X1,sK5(X0,X1,X2),X0) | sP0(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u208,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r1_orders_2(X1,X0,sK6(X0,X1,X2)) | sP2(X0,X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u207,axiom,
% 0.21/0.48      (![X1, X0] : ((~r2_lattice3(X0,X1,sK7(u1_struct_0(X0))) | sP0(sK7(u1_struct_0(X0)),X0,X1) | ~l1_orders_2(X0) | v1_xboole_0(u1_struct_0(X0)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u206,axiom,
% 0.21/0.48      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK5(X4,X5,X6),X5,X7))))).
% 0.21/0.48  
% 0.21/0.48  tff(u205,axiom,
% 0.21/0.48      (![X5, X7, X4, X6] : ((~r2_lattice3(X6,X7,sK5(X4,X5,u1_struct_0(X6))) | ~l1_orders_2(X6) | sP0(X4,X5,u1_struct_0(X6)) | sP0(sK5(X4,X5,u1_struct_0(X6)),X6,X7))))).
% 0.21/0.48  
% 0.21/0.48  tff(u204,axiom,
% 0.21/0.48      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK6(X4,X5,X6)) | ~l1_orders_2(X5) | sP2(X4,X5,X6) | sP0(sK6(X4,X5,X6),X5,X7))))).
% 0.21/0.48  
% 0.21/0.48  tff(u203,axiom,
% 0.21/0.48      (![X5, X7, X4, X6] : ((~r2_lattice3(X6,X7,sK6(X4,X5,u1_struct_0(X6))) | ~l1_orders_2(X6) | sP2(X4,X5,u1_struct_0(X6)) | sP0(sK6(X4,X5,u1_struct_0(X6)),X6,X7))))).
% 0.21/0.48  
% 0.21/0.48  tff(u202,axiom,
% 0.21/0.48      (![X1, X0] : ((r2_lattice3(X0,X1,sK7(u1_struct_0(X0))) | ~l1_orders_2(X0) | v1_xboole_0(u1_struct_0(X0)) | ~v1_xboole_0(X1))))).
% 0.21/0.48  
% 0.21/0.48  % (9297)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.48  tff(u201,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((r2_lattice3(X0,X3,sK5(X1,X0,X2)) | sP0(X1,X0,X2) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u200,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((r2_lattice3(X0,X3,sK5(X1,X2,u1_struct_0(X0))) | sP0(X1,X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u199,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((r2_lattice3(X0,X3,sK6(X1,X0,X2)) | sP2(X1,X0,X2) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u198,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((r2_lattice3(X0,X3,sK6(X1,X2,u1_struct_0(X0))) | sP2(X1,X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u197,axiom,
% 0.21/0.48      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u196,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r2_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u195,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,u1_struct_0(X2)),X2,X3) | ~l1_orders_2(X2) | sP0(X0,X1,u1_struct_0(X2)) | r2_lattice3(X2,X3,sK5(X0,X1,u1_struct_0(X2))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u194,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~sP0(sK6(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP2(X0,X1,X2) | r2_lattice3(X1,X3,sK6(X0,X1,X2)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u193,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~sP0(sK6(X0,X1,u1_struct_0(X2)),X2,X3) | ~l1_orders_2(X2) | sP2(X0,X1,u1_struct_0(X2)) | r2_lattice3(X2,X3,sK6(X0,X1,u1_struct_0(X2))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u192,axiom,
% 0.21/0.48      (![X1, X0] : ((~sP0(sK7(u1_struct_0(X0)),X0,X1) | r2_lattice3(X0,X1,sK7(u1_struct_0(X0))) | ~l1_orders_2(X0) | v1_xboole_0(u1_struct_0(X0)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u191,axiom,
% 0.21/0.48      (![X3, X5, X4] : ((sP0(X3,X4,X5) | ~v1_xboole_0(X5))))).
% 0.21/0.48  
% 0.21/0.48  tff(u190,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_lattice3(X1,X0,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u189,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u188,axiom,
% 0.21/0.48      (![X1, X0] : ((sP1(X0,X1,sK7(u1_struct_0(X1))) | ~l1_orders_2(X1) | v1_xboole_0(u1_struct_0(X1)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u187,axiom,
% 0.21/0.48      (![X5, X7, X4, X6] : ((sP1(X7,X5,sK5(X4,X5,X6)) | sP0(X4,X5,X6) | ~l1_orders_2(X5))))).
% 0.21/0.48  
% 0.21/0.48  tff(u186,axiom,
% 0.21/0.48      (![X9, X7, X8, X10] : ((sP1(X10,X9,sK5(X7,X8,u1_struct_0(X9))) | sP0(X7,X8,u1_struct_0(X9)) | ~l1_orders_2(X9))))).
% 0.21/0.48  
% 0.21/0.48  tff(u185,axiom,
% 0.21/0.48      (![X5, X7, X4, X6] : ((sP1(X7,X5,sK6(X4,X5,X6)) | sP2(X4,X5,X6) | ~l1_orders_2(X5))))).
% 0.21/0.48  
% 0.21/0.48  tff(u184,axiom,
% 0.21/0.48      (![X9, X7, X8, X10] : ((sP1(X10,X9,sK6(X7,X8,u1_struct_0(X9))) | sP2(X7,X8,u1_struct_0(X9)) | ~l1_orders_2(X9))))).
% 0.21/0.48  
% 0.21/0.48  tff(u183,axiom,
% 0.21/0.48      (![X1, X0, X2, X4] : ((~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4))))).
% 0.21/0.48  
% 0.21/0.48  % (9296)Refutation not found, incomplete strategy% (9296)------------------------------
% 0.21/0.48  % (9296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9293)Refutation not found, incomplete strategy% (9293)------------------------------
% 0.21/0.48  % (9293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  tff(u182,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~sP2(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r1_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u181,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~sP2(sK5(X0,X1,u1_struct_0(X2)),X2,X3) | ~l1_orders_2(X2) | sP0(X0,X1,u1_struct_0(X2)) | r1_lattice3(X2,X3,sK5(X0,X1,u1_struct_0(X2))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u180,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~sP2(sK6(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP2(X0,X1,X2) | r1_lattice3(X1,X3,sK6(X0,X1,X2)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u179,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((~sP2(sK6(X0,X1,u1_struct_0(X2)),X2,X3) | ~l1_orders_2(X2) | sP2(X0,X1,u1_struct_0(X2)) | r1_lattice3(X2,X3,sK6(X0,X1,u1_struct_0(X2))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u178,axiom,
% 0.21/0.48      (![X1, X0] : ((~sP2(sK7(u1_struct_0(X0)),X0,X1) | r1_lattice3(X0,X1,sK7(u1_struct_0(X0))) | ~l1_orders_2(X0) | v1_xboole_0(u1_struct_0(X0)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u177,axiom,
% 0.21/0.48      (![X3, X5, X4] : ((sP2(X3,X4,X5) | ~v1_xboole_0(X5))))).
% 0.21/0.48  
% 0.21/0.48  tff(u176,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~sP3(X0,X1,X2) | ~sP2(X2,X1,X0) | r1_lattice3(X1,X0,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u175,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~sP3(X0,X1,X2) | ~r1_lattice3(X1,X0,X2) | sP2(X2,X1,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u174,axiom,
% 0.21/0.48      (![X1, X0] : ((sP3(X0,X1,sK7(u1_struct_0(X1))) | ~l1_orders_2(X1) | v1_xboole_0(u1_struct_0(X1)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u173,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((sP3(X3,X1,sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u172,axiom,
% 0.21/0.48      (![X3, X5, X4, X6] : ((sP3(X6,X5,sK5(X3,X4,u1_struct_0(X5))) | sP0(X3,X4,u1_struct_0(X5)) | ~l1_orders_2(X5))))).
% 0.21/0.48  
% 0.21/0.48  tff(u171,axiom,
% 0.21/0.48      (![X1, X3, X0, X2] : ((sP3(X3,X1,sK6(X0,X1,X2)) | sP2(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u170,axiom,
% 0.21/0.48      (![X3, X5, X4, X6] : ((sP3(X6,X5,sK6(X3,X4,u1_struct_0(X5))) | sP2(X3,X4,u1_struct_0(X5)) | ~l1_orders_2(X5))))).
% 0.21/0.48  
% 0.21/0.48  % (9301)# SZS output end Saturation.
% 0.21/0.48  % (9301)------------------------------
% 0.21/0.48  % (9301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9301)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (9301)Memory used [KB]: 5373
% 0.21/0.48  % (9301)Time elapsed: 0.068 s
% 0.21/0.48  % (9301)------------------------------
% 0.21/0.48  % (9301)------------------------------
% 0.21/0.49  % (9298)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.49  % (9292)Success in time 0.132 s
%------------------------------------------------------------------------------
