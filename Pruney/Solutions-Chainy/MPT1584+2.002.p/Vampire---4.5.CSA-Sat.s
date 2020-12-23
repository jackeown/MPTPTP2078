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
% DateTime   : Thu Dec  3 13:16:23 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 (  76 expanded)
%              Number of leaves         :   76 (  76 expanded)
%              Depth                    :    0
%              Number of atoms          :  208 ( 208 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u243,negated_conjecture,(
    sK3 = sK4 )).

tff(u242,negated_conjecture,(
    ! [X3,X5,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | r2_lattice3(sK0,X4,X3)
      | r2_hidden(sK6(sK0,X4,X3),X5)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) )).

tff(u241,negated_conjecture,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | r2_lattice3(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK6(sK0,X1,X0),X2) ) )).

tff(u240,negated_conjecture,(
    ! [X3,X5,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | r1_lattice3(sK0,X4,X3)
      | r2_hidden(sK5(sK0,X4,X3),X5)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) )).

tff(u239,negated_conjecture,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | r1_lattice3(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(sK5(sK0,X1,X0),X2) ) )).

tff(u238,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u237,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
        | r2_hidden(sK6(sK0,sK2,sK3),X1) ) )).

tff(u236,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | m1_subset_1(sK6(sK0,sK2,sK3),X0) ) )).

tff(u235,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
        | r2_hidden(sK5(sK0,sK2,sK3),X1) ) )).

tff(u234,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | m1_subset_1(sK5(sK0,sK2,sK3),X0) ) )).

tff(u233,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0))
        | m1_subset_1(sK5(sK0,sK2,sK3),X0) ) )).

tff(u232,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | ! [X1] :
        ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1))
        | r2_hidden(sK5(sK0,sK2,sK3),X1) ) )).

tff(u231,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0))
        | m1_subset_1(sK6(sK0,sK2,sK3),X0) ) )).

tff(u230,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | ! [X1] :
        ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1))
        | r2_hidden(sK6(sK0,sK2,sK3),X1) ) )).

tff(u229,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattice3(sK0,sK2,X0)
      | m1_subset_1(sK5(sK0,sK2,X0),X1) ) )).

tff(u228,negated_conjecture,(
    ! [X3,X2] :
      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(sK5(sK0,sK2,X2),X3)
      | r1_lattice3(sK0,sK2,X2) ) )).

tff(u227,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,sK2,X0)
      | m1_subset_1(sK6(sK0,sK2,X0),X1) ) )).

tff(u226,negated_conjecture,(
    ! [X3,X2] :
      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(sK6(sK0,sK2,X2),X3)
      | r2_lattice3(sK0,sK2,X2) ) )).

tff(u225,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0))
        | m1_subset_1(sK5(sK0,u1_struct_0(sK1),sK3),X0) ) )).

tff(u224,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | ! [X1] :
        ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1))
        | r2_hidden(sK5(sK0,u1_struct_0(sK1),sK3),X1) ) )).

tff(u223,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0))
        | m1_subset_1(sK6(sK0,u1_struct_0(sK1),sK3),X0) ) )).

tff(u222,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | ! [X1] :
        ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1))
        | r2_hidden(sK6(sK0,u1_struct_0(sK1),sK3),X1) ) )).

tff(u221,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK0)) )).

tff(u220,negated_conjecture,(
    m1_subset_1(sK3,u1_struct_0(sK1)) )).

tff(u219,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK1)) )).

tff(u218,negated_conjecture,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK2,X0),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattice3(sK0,sK2,X0) ) )).

tff(u217,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u216,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) )).

tff(u215,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK5(sK0,u1_struct_0(sK1),sK3),u1_struct_0(sK0)) )).

tff(u214,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK1)) )).

tff(u213,negated_conjecture,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK2,X0),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_lattice3(sK0,sK2,X0) ) )).

tff(u212,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u211,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) )).

tff(u210,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK6(sK0,u1_struct_0(sK1),sK3),u1_struct_0(sK0)) )).

tff(u209,negated_conjecture,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u208,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) )).

tff(u207,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u206,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u205,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK3),sK3),u1_orders_2(sK0)) )).

tff(u204,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r2_hidden(k4_tarski(sK6(sK0,u1_struct_0(sK1),sK3),sK3),u1_orders_2(sK0)) )).

tff(u203,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r2_hidden(k4_tarski(sK3,sK5(sK0,sK2,sK3)),u1_orders_2(sK0)) )).

tff(u202,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r2_hidden(k4_tarski(sK3,sK5(sK0,u1_struct_0(sK1),sK3)),u1_orders_2(sK0)) )).

tff(u201,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | r2_hidden(sK5(sK0,sK2,sK3),sK2) )).

tff(u200,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | r2_hidden(sK6(sK0,sK2,sK3),sK2) )).

tff(u199,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | r2_hidden(sK5(sK0,sK2,sK3),u1_struct_0(sK1)) )).

tff(u198,negated_conjecture,(
    ! [X0] :
      ( r2_hidden(sK5(sK0,sK2,X0),u1_struct_0(sK1))
      | r1_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u197,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | r2_hidden(sK5(sK0,u1_struct_0(sK1),sK3),u1_struct_0(sK1)) )).

tff(u196,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | r2_hidden(sK6(sK0,sK2,sK3),u1_struct_0(sK1)) )).

tff(u195,negated_conjecture,(
    ! [X0] :
      ( r2_hidden(sK6(sK0,sK2,X0),u1_struct_0(sK1))
      | r2_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u194,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | r2_hidden(sK6(sK0,u1_struct_0(sK1),sK3),u1_struct_0(sK1)) )).

tff(u193,negated_conjecture,(
    ! [X1,X0] :
      ( r2_hidden(sK5(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattice3(sK0,X0,X1) ) )).

tff(u192,negated_conjecture,(
    ! [X1,X0] :
      ( r2_hidden(sK6(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_lattice3(sK0,X0,X1) ) )).

tff(u191,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u190,negated_conjecture,(
    r1_tarski(sK2,u1_struct_0(sK1)) )).

tff(u189,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4) ) )).

tff(u188,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) )).

tff(u187,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) )).

tff(u186,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u185,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u184,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3)) )).

tff(u183,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK3,sK5(sK0,u1_struct_0(sK1),sK3)) )).

tff(u182,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u181,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u180,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3) )).

tff(u179,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK6(sK0,u1_struct_0(sK1),sK3),sK3) )).

tff(u178,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK2,sK3) )).

tff(u177,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,u1_struct_0(sK1),sK3) )).

tff(u176,negated_conjecture,(
    ! [X1,X0,X2] :
      ( ~ r1_lattice3(sK0,X1,X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_orders_2(sK0,X2,X0) ) )).

tff(u175,negated_conjecture,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    | r1_lattice3(sK1,sK2,sK3) )).

tff(u174,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK2,sK3) )).

tff(u173,negated_conjecture,
    ( ~ ~ r2_lattice3(sK1,sK2,sK4)
    | ~ r2_lattice3(sK1,sK2,sK3) )).

tff(u172,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u171,negated_conjecture,
    ( ~ ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,u1_struct_0(sK1),sK3) )).

tff(u170,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u169,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u168,negated_conjecture,(
    m1_yellow_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:57:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (29945)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.48  % (29953)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.49  % (29943)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (29935)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (29936)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (29938)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (29934)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (29937)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (29937)Refutation not found, incomplete strategy% (29937)------------------------------
% 0.22/0.51  % (29937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (29956)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (29937)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (29937)Memory used [KB]: 10618
% 0.22/0.51  % (29937)Time elapsed: 0.096 s
% 0.22/0.51  % (29937)------------------------------
% 0.22/0.51  % (29937)------------------------------
% 0.22/0.51  % (29951)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.51  % (29948)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.51  % (29949)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (29946)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.51  % (29952)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.51  % (29947)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.51  % (29944)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.51  % (29941)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (29948)# SZS output start Saturation.
% 0.22/0.52  tff(u243,negated_conjecture,
% 0.22/0.52      (sK3 = sK4)).
% 0.22/0.52  
% 0.22/0.52  tff(u242,negated_conjecture,
% 0.22/0.52      (![X3, X5, X4] : ((~m1_subset_1(X4,k1_zfmisc_1(X5)) | r2_lattice3(sK0,X4,X3) | r2_hidden(sK6(sK0,X4,X3),X5) | ~m1_subset_1(X3,u1_struct_0(sK0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u241,negated_conjecture,
% 0.22/0.52      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | r2_lattice3(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK6(sK0,X1,X0),X2))))).
% 0.22/0.52  
% 0.22/0.52  tff(u240,negated_conjecture,
% 0.22/0.52      (![X3, X5, X4] : ((~m1_subset_1(X4,k1_zfmisc_1(X5)) | r1_lattice3(sK0,X4,X3) | r2_hidden(sK5(sK0,X4,X3),X5) | ~m1_subset_1(X3,u1_struct_0(sK0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u239,negated_conjecture,
% 0.22/0.52      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | r1_lattice3(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(sK5(sK0,X1,X0),X2))))).
% 0.22/0.52  
% 0.22/0.52  tff(u238,axiom,
% 0.22/0.52      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u237,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | (![X1] : ((~m1_subset_1(sK2,k1_zfmisc_1(X1)) | r2_hidden(sK6(sK0,sK2,sK3),X1)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u236,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | (![X0] : ((~m1_subset_1(sK2,k1_zfmisc_1(X0)) | m1_subset_1(sK6(sK0,sK2,sK3),X0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u235,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | (![X1] : ((~m1_subset_1(sK2,k1_zfmisc_1(X1)) | r2_hidden(sK5(sK0,sK2,sK3),X1)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u234,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | (![X0] : ((~m1_subset_1(sK2,k1_zfmisc_1(X0)) | m1_subset_1(sK5(sK0,sK2,sK3),X0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u233,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | (![X0] : ((~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0)) | m1_subset_1(sK5(sK0,sK2,sK3),X0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u232,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | (![X1] : ((~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1)) | r2_hidden(sK5(sK0,sK2,sK3),X1)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u231,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | (![X0] : ((~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0)) | m1_subset_1(sK6(sK0,sK2,sK3),X0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u230,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | (![X1] : ((~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1)) | r2_hidden(sK6(sK0,sK2,sK3),X1)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u229,negated_conjecture,
% 0.22/0.52      (![X1, X0] : ((~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,X0) | m1_subset_1(sK5(sK0,sK2,X0),X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u228,negated_conjecture,
% 0.22/0.52      (![X3, X2] : ((~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_hidden(sK5(sK0,sK2,X2),X3) | r1_lattice3(sK0,sK2,X2))))).
% 0.22/0.52  
% 0.22/0.52  tff(u227,negated_conjecture,
% 0.22/0.52      (![X1, X0] : ((~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,sK2,X0) | m1_subset_1(sK6(sK0,sK2,X0),X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u226,negated_conjecture,
% 0.22/0.52      (![X3, X2] : ((~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_hidden(sK6(sK0,sK2,X2),X3) | r2_lattice3(sK0,sK2,X2))))).
% 0.22/0.52  
% 0.22/0.52  tff(u225,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | (![X0] : ((~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0)) | m1_subset_1(sK5(sK0,u1_struct_0(sK1),sK3),X0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u224,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | (![X1] : ((~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1)) | r2_hidden(sK5(sK0,u1_struct_0(sK1),sK3),X1)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u223,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | (![X0] : ((~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0)) | m1_subset_1(sK6(sK0,u1_struct_0(sK1),sK3),X0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u222,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | (![X1] : ((~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X1)) | r2_hidden(sK6(sK0,u1_struct_0(sK1),sK3),X1)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u221,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u220,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK3,u1_struct_0(sK1))).
% 0.22/0.52  
% 0.22/0.52  tff(u219,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK1)))).
% 0.22/0.52  
% 0.22/0.52  tff(u218,negated_conjecture,
% 0.22/0.52      (![X0] : ((m1_subset_1(sK5(sK0,sK2,X0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u217,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u216,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u215,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | m1_subset_1(sK5(sK0,u1_struct_0(sK1),sK3),u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u214,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK1)))).
% 0.22/0.52  
% 0.22/0.52  tff(u213,negated_conjecture,
% 0.22/0.52      (![X0] : ((m1_subset_1(sK6(sK0,sK2,X0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,sK2,X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u212,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u211,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u210,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | m1_subset_1(sK6(sK0,u1_struct_0(sK1),sK3),u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u209,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))).
% 0.22/0.52  
% 0.22/0.52  tff(u208,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))))).
% 0.22/0.52  
% 0.22/0.52  tff(u207,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u206,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u205,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | ~r2_hidden(k4_tarski(sK6(sK0,sK2,sK3),sK3),u1_orders_2(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u204,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | ~r2_hidden(k4_tarski(sK6(sK0,u1_struct_0(sK1),sK3),sK3),u1_orders_2(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u203,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | ~r2_hidden(k4_tarski(sK3,sK5(sK0,sK2,sK3)),u1_orders_2(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u202,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | ~r2_hidden(k4_tarski(sK3,sK5(sK0,u1_struct_0(sK1),sK3)),u1_orders_2(sK0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u201,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | r2_hidden(sK5(sK0,sK2,sK3),sK2))).
% 0.22/0.52  
% 0.22/0.52  tff(u200,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | r2_hidden(sK6(sK0,sK2,sK3),sK2))).
% 0.22/0.52  
% 0.22/0.52  tff(u199,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | r2_hidden(sK5(sK0,sK2,sK3),u1_struct_0(sK1)))).
% 0.22/0.52  
% 0.22/0.52  tff(u198,negated_conjecture,
% 0.22/0.52      (![X0] : ((r2_hidden(sK5(sK0,sK2,X0),u1_struct_0(sK1)) | r1_lattice3(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u197,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | r2_hidden(sK5(sK0,u1_struct_0(sK1),sK3),u1_struct_0(sK1)))).
% 0.22/0.52  
% 0.22/0.52  tff(u196,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | r2_hidden(sK6(sK0,sK2,sK3),u1_struct_0(sK1)))).
% 0.22/0.52  
% 0.22/0.52  tff(u195,negated_conjecture,
% 0.22/0.52      (![X0] : ((r2_hidden(sK6(sK0,sK2,X0),u1_struct_0(sK1)) | r2_lattice3(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u194,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | r2_hidden(sK6(sK0,u1_struct_0(sK1),sK3),u1_struct_0(sK1)))).
% 0.22/0.52  
% 0.22/0.52  tff(u193,negated_conjecture,
% 0.22/0.52      (![X1, X0] : ((r2_hidden(sK5(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u192,negated_conjecture,
% 0.22/0.52      (![X1, X0] : ((r2_hidden(sK6(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u191,axiom,
% 0.22/0.52      (![X1, X0] : ((~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u190,negated_conjecture,
% 0.22/0.52      r1_tarski(sK2,u1_struct_0(sK1))).
% 0.22/0.52  
% 0.22/0.52  tff(u189,axiom,
% 0.22/0.52      (![X1, X0, X2, X4] : ((~l1_orders_2(X0) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4))))).
% 0.22/0.52  
% 0.22/0.52  tff(u188,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~l1_orders_2(X0) | r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2))))).
% 0.22/0.52  
% 0.22/0.52  tff(u187,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~l1_orders_2(X0) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2))))).
% 0.22/0.52  
% 0.22/0.52  tff(u186,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u185,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u184,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | ~r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3)))).
% 0.22/0.52  
% 0.22/0.52  tff(u183,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | ~r1_orders_2(sK0,sK3,sK5(sK0,u1_struct_0(sK1),sK3)))).
% 0.22/0.52  
% 0.22/0.52  tff(u182,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~r1_orders_2(X0,sK6(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u181,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u180,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | ~r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3))).
% 0.22/0.52  
% 0.22/0.52  tff(u179,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | ~r1_orders_2(sK0,sK6(sK0,u1_struct_0(sK1),sK3),sK3))).
% 0.22/0.52  
% 0.22/0.52  tff(u178,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | ~r1_lattice3(sK0,sK2,sK3))).
% 0.22/0.52  
% 0.22/0.52  tff(u177,negated_conjecture,
% 0.22/0.52      ((~~r1_lattice3(sK0,sK2,sK3)) | ~r1_lattice3(sK0,u1_struct_0(sK1),sK3))).
% 0.22/0.52  
% 0.22/0.52  tff(u176,negated_conjecture,
% 0.22/0.52      (![X1, X0, X2] : ((~r1_lattice3(sK0,X1,X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_orders_2(sK0,X2,X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u175,negated_conjecture,
% 0.22/0.52      ((~r1_lattice3(sK1,sK2,sK4)) | r1_lattice3(sK1,sK2,sK3))).
% 0.22/0.52  
% 0.22/0.52  tff(u174,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | ~r2_lattice3(sK0,sK2,sK3))).
% 0.22/0.52  
% 0.22/0.52  tff(u173,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK1,sK2,sK4)) | ~r2_lattice3(sK1,sK2,sK3))).
% 0.22/0.52  
% 0.22/0.52  tff(u172,axiom,
% 0.22/0.52      (![X1, X0, X2, X4] : ((~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u171,negated_conjecture,
% 0.22/0.52      ((~~r2_lattice3(sK0,sK2,sK3)) | ~r2_lattice3(sK0,u1_struct_0(sK1),sK3))).
% 0.22/0.52  
% 0.22/0.52  tff(u170,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u169,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK1)).
% 0.22/0.52  
% 0.22/0.52  tff(u168,negated_conjecture,
% 0.22/0.52      m1_yellow_0(sK1,sK0)).
% 0.22/0.52  
% 0.22/0.52  % (29948)# SZS output end Saturation.
% 0.22/0.52  % (29955)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (29948)------------------------------
% 0.22/0.52  % (29948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (29948)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (29948)Memory used [KB]: 10746
% 0.22/0.52  % (29948)Time elapsed: 0.060 s
% 0.22/0.52  % (29948)------------------------------
% 0.22/0.52  % (29948)------------------------------
% 0.22/0.52  % (29954)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (29933)Success in time 0.153 s
%------------------------------------------------------------------------------
