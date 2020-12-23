%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:01 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   29 (  29 expanded)
%              Depth                    :    0
%              Number of atoms          :  136 ( 136 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   15 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u148,negated_conjecture,
    ( ~ ( sK1 != k13_lattice3(sK0,sK1,sK2) )
    | sK1 != k13_lattice3(sK0,sK1,sK2) )).

tff(u147,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(X1,sK3(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0) ) )).

tff(u146,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(X1,sK3(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ v3_orders_2(X0) ) )).

tff(u145,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(X2,sK3(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0) ) )).

tff(u144,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(X2,sK3(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ v3_orders_2(X0) ) )).

tff(u143,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) )).

tff(u142,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u141,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(X3) ) )).

tff(u140,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v3_orders_2(X1) ) )).

tff(u139,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v3_orders_2(X1) ) )).

tff(u138,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u137,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u136,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0) ) )).

tff(u135,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ v3_orders_2(X0) ) )).

tff(u134,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u133,axiom,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) )).

tff(u132,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u131,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u130,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u129,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u128,axiom,(
    ! [X5,X4,X6] :
      ( ~ r3_orders_2(X5,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ v3_orders_2(X5)
      | ~ l1_orders_2(X5)
      | ~ v1_xboole_0(u1_struct_0(X5))
      | v2_struct_0(X5)
      | ~ m1_subset_1(X4,u1_struct_0(X5)) ) )).

tff(u127,axiom,(
    ! [X1,X0,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) )).

tff(u126,axiom,(
    ! [X1,X0,X2] :
      ( r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) )).

tff(u125,axiom,(
    ! [X3,X5,X4] :
      ( ~ r1_orders_2(X4,X5,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ v3_orders_2(X4)
      | ~ l1_orders_2(X4)
      | ~ v1_xboole_0(u1_struct_0(X4)) ) )).

tff(u124,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK2,sK1) )).

tff(u123,axiom,(
    ! [X1,X0,X2,X4] :
      ( r1_orders_2(X0,X2,X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v6_orders_2(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X2,X4)
      | r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0) ) )).

tff(u122,axiom,(
    ! [X1,X0,X2] :
      ( r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r3_orders_2(X0,X1,X2) ) )).

tff(u121,axiom,(
    ! [X1,X0,X2] :
      ( v6_orders_2(sK3(X0,X1,X2),X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0) ) )).

tff(u120,axiom,(
    ! [X1,X0,X2] :
      ( v6_orders_2(sK3(X0,X1,X2),X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ v3_orders_2(X0) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (15472)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.48  % (15477)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (15472)# SZS output start Saturation.
% 0.21/0.49  tff(u148,negated_conjecture,
% 0.21/0.49      ((~(sK1 != k13_lattice3(sK0,sK1,sK2))) | (sK1 != k13_lattice3(sK0,sK1,sK2)))).
% 0.21/0.49  
% 0.21/0.49  tff(u147,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((r2_hidden(X1,sK3(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u146,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((r2_hidden(X1,sK3(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u145,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((r2_hidden(X2,sK3(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u144,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((r2_hidden(X2,sK3(X0,X1,X2)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u143,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u142,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((~m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X3)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.49  
% 0.21/0.49  tff(u141,axiom,
% 0.21/0.49      (![X1, X3, X0, X2] : ((~m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(X3)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~v1_xboole_0(X3))))).
% 0.21/0.49  
% 0.21/0.49  tff(u140,axiom,
% 0.21/0.49      (![X1, X0] : ((~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v1_xboole_0(u1_struct_0(X1)) | v2_struct_0(X1) | ~v3_orders_2(X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u139,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v1_xboole_0(u1_struct_0(X1)) | v2_struct_0(X1) | ~v3_orders_2(X1))))).
% 0.21/0.49  
% 0.21/0.49  tff(u138,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  tff(u137,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  tff(u136,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u135,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u134,negated_conjecture,
% 0.21/0.49      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.21/0.49  
% 0.21/0.49  tff(u133,axiom,
% 0.21/0.49      (![X0] : ((v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u132,negated_conjecture,
% 0.21/0.49      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  tff(u131,axiom,
% 0.21/0.49      (![X0] : ((l1_struct_0(X0) | ~l1_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u130,negated_conjecture,
% 0.21/0.49      l1_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  tff(u129,negated_conjecture,
% 0.21/0.49      v3_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  tff(u128,axiom,
% 0.21/0.49      (![X5, X4, X6] : ((~r3_orders_2(X5,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X5)) | ~v3_orders_2(X5) | ~l1_orders_2(X5) | ~v1_xboole_0(u1_struct_0(X5)) | v2_struct_0(X5) | ~m1_subset_1(X4,u1_struct_0(X5)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u127,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((r3_orders_2(X0,X1,X1) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u126,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | v2_struct_0(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u125,axiom,
% 0.21/0.49      (![X3, X5, X4] : ((~r1_orders_2(X4,X5,X3) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~m1_subset_1(X3,u1_struct_0(X4)) | ~v3_orders_2(X4) | ~l1_orders_2(X4) | ~v1_xboole_0(u1_struct_0(X4)))))).
% 0.21/0.49  
% 0.21/0.49  tff(u124,negated_conjecture,
% 0.21/0.49      ((~r1_orders_2(sK0,sK2,sK1)) | r1_orders_2(sK0,sK2,sK1))).
% 0.21/0.49  
% 0.21/0.49  tff(u123,axiom,
% 0.21/0.49      (![X1, X0, X2, X4] : ((r1_orders_2(X0,X2,X1) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v6_orders_2(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X4) | ~r2_hidden(X2,X4) | r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u122,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~r3_orders_2(X0,X1,X2))))).
% 0.21/0.49  
% 0.21/0.49  tff(u121,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((v6_orders_2(sK3(X0,X1,X2),X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  tff(u120,axiom,
% 0.21/0.49      (![X1, X0, X2] : ((v6_orders_2(sK3(X0,X1,X2),X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | ~v3_orders_2(X0))))).
% 0.21/0.49  
% 0.21/0.49  % (15472)# SZS output end Saturation.
% 0.21/0.49  % (15472)------------------------------
% 0.21/0.49  % (15472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15472)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (15472)Memory used [KB]: 10618
% 0.21/0.49  % (15472)Time elapsed: 0.067 s
% 0.21/0.49  % (15472)------------------------------
% 0.21/0.49  % (15472)------------------------------
% 0.21/0.49  % (15454)Success in time 0.131 s
%------------------------------------------------------------------------------
