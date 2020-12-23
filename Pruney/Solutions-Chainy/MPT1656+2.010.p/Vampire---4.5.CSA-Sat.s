%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:10 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    0
%              Number of atoms          :  114 ( 114 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u123,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0) ) )).

tff(u122,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u121,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u120,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) )).

tff(u119,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u118,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK3(X0,k4_waybel_0(sK0,sK1),X1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,sK3(X0,k4_waybel_0(sK0,sK1),X1))
        | r1_lattice3(X0,k4_waybel_0(sK0,sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) ) )).

tff(u117,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X3,X2] :
        ( ~ m1_subset_1(sK4(X2,k4_waybel_0(sK0,sK1),X3),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,sK4(X2,k4_waybel_0(sK0,sK1),X3))
        | r2_lattice3(X2,k4_waybel_0(sK0,sK1),X3)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ l1_orders_2(X2) ) )).

tff(u116,negated_conjecture,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1) ) )).

tff(u115,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u114,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u113,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u112,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u111,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u110,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u109,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u108,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u107,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u106,negated_conjecture,(
    r1_orders_2(sK0,sK2,sK2) )).

tff(u105,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( r1_orders_2(sK0,sK2,sK3(sK0,k4_waybel_0(sK0,sK1),X0))
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u104,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X1,X2] :
        ( r1_orders_2(sK0,sK2,sK3(X1,k4_waybel_0(sK0,sK1),X2))
        | r1_lattice3(X1,k4_waybel_0(sK0,sK1),X2)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ r2_hidden(sK3(X1,k4_waybel_0(sK0,sK1),X2),sK1) ) )).

tff(u103,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X0] :
        ( r1_orders_2(sK0,sK2,sK4(sK0,k4_waybel_0(sK0,sK1),X0))
        | r2_lattice3(sK0,k4_waybel_0(sK0,sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u102,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ! [X1,X2] :
        ( r1_orders_2(sK0,sK2,sK4(X1,k4_waybel_0(sK0,sK1),X2))
        | r2_lattice3(X1,k4_waybel_0(sK0,sK1),X2)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ l1_orders_2(X1)
        | ~ r2_hidden(sK4(X1,k4_waybel_0(sK0,sK1),X2),sK1) ) )).

tff(u101,negated_conjecture,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,X0)
      | ~ r2_hidden(X0,sK1) ) )).

tff(u100,axiom,(
    ! [X1,X0,X2] :
      ( r1_orders_2(X0,sK3(X0,X1,X2),sK3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u99,axiom,(
    ! [X1,X0,X2] :
      ( r1_orders_2(X0,sK4(X0,X1,X2),sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u98,negated_conjecture,
    ( ~ ~ r1_lattice3(sK0,sK1,sK2)
    | ~ r1_lattice3(sK0,sK1,sK2) )).

tff(u97,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u96,negated_conjecture,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2) )).

tff(u95,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u94,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u93,negated_conjecture,(
    v4_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (870)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.20/0.45  % (869)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (877)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.20/0.47  % (878)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.20/0.47  % (878)Refutation not found, incomplete strategy% (878)------------------------------
% 0.20/0.47  % (878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (878)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (878)Memory used [KB]: 9850
% 0.20/0.47  % (878)Time elapsed: 0.065 s
% 0.20/0.47  % (878)------------------------------
% 0.20/0.47  % (878)------------------------------
% 0.20/0.47  % (874)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.48  % (877)Refutation not found, incomplete strategy% (877)------------------------------
% 0.20/0.48  % (877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (877)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (877)Memory used [KB]: 5373
% 0.20/0.48  % (877)Time elapsed: 0.063 s
% 0.20/0.48  % (877)------------------------------
% 0.20/0.48  % (877)------------------------------
% 0.20/0.48  % (863)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.20/0.48  % (871)WARNING: option uwaf not known.
% 0.20/0.48  % (871)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.20/0.48  % (872)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.20/0.49  % (867)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.49  % (880)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.20/0.49  % (864)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.20/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.49  % (880)# SZS output start Saturation.
% 0.20/0.49  tff(u123,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X0] : ((~r2_hidden(X0,k4_waybel_0(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,X0)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u122,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((r2_hidden(sK3(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u121,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((r2_hidden(sK4(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u120,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1))))).
% 0.20/0.49  
% 0.20/0.49  tff(u119,axiom,
% 0.20/0.49      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u118,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X1, X0] : ((~m1_subset_1(sK3(X0,k4_waybel_0(sK0,sK1),X1),u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,sK3(X0,k4_waybel_0(sK0,sK1),X1)) | r1_lattice3(X0,k4_waybel_0(sK0,sK1),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u117,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X3, X2] : ((~m1_subset_1(sK4(X2,k4_waybel_0(sK0,sK1),X3),u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,sK4(X2,k4_waybel_0(sK0,sK1),X3)) | r2_lattice3(X2,k4_waybel_0(sK0,sK1),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_orders_2(X2)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u116,negated_conjecture,
% 0.20/0.49      (![X0] : ((m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1))))).
% 0.20/0.49  
% 0.20/0.49  tff(u115,negated_conjecture,
% 0.20/0.49      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.49  
% 0.20/0.49  tff(u114,negated_conjecture,
% 0.20/0.49      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.49  
% 0.20/0.49  tff(u113,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u112,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u111,negated_conjecture,
% 0.20/0.49      ~v2_struct_0(sK0)).
% 0.20/0.49  
% 0.20/0.49  tff(u110,negated_conjecture,
% 0.20/0.49      v3_orders_2(sK0)).
% 0.20/0.49  
% 0.20/0.49  tff(u109,negated_conjecture,
% 0.20/0.49      l1_orders_2(sK0)).
% 0.20/0.49  
% 0.20/0.49  tff(u108,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u107,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((~r1_orders_2(X0,sK4(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u106,negated_conjecture,
% 0.20/0.49      r1_orders_2(sK0,sK2,sK2)).
% 0.20/0.49  
% 0.20/0.49  tff(u105,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X0] : ((r1_orders_2(sK0,sK2,sK3(sK0,k4_waybel_0(sK0,sK1),X0)) | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 0.20/0.49  
% 0.20/0.49  tff(u104,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X1, X2] : ((r1_orders_2(sK0,sK2,sK3(X1,k4_waybel_0(sK0,sK1),X2)) | r1_lattice3(X1,k4_waybel_0(sK0,sK1),X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~r2_hidden(sK3(X1,k4_waybel_0(sK0,sK1),X2),sK1)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u103,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X0] : ((r1_orders_2(sK0,sK2,sK4(sK0,k4_waybel_0(sK0,sK1),X0)) | r2_lattice3(sK0,k4_waybel_0(sK0,sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 0.20/0.49  
% 0.20/0.49  tff(u102,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | (![X1, X2] : ((r1_orders_2(sK0,sK2,sK4(X1,k4_waybel_0(sK0,sK1),X2)) | r2_lattice3(X1,k4_waybel_0(sK0,sK1),X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~r2_hidden(sK4(X1,k4_waybel_0(sK0,sK1),X2),sK1)))))).
% 0.20/0.49  
% 0.20/0.49  tff(u101,negated_conjecture,
% 0.20/0.49      (![X0] : ((r1_orders_2(sK0,X0,X0) | ~r2_hidden(X0,sK1))))).
% 0.20/0.49  
% 0.20/0.49  tff(u100,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((r1_orders_2(X0,sK3(X0,X1,X2),sK3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u99,axiom,
% 0.20/0.49      (![X1, X0, X2] : ((r1_orders_2(X0,sK4(X0,X1,X2),sK4(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u98,negated_conjecture,
% 0.20/0.49      ((~~r1_lattice3(sK0,sK1,sK2)) | ~r1_lattice3(sK0,sK1,sK2))).
% 0.20/0.49  
% 0.20/0.49  tff(u97,axiom,
% 0.20/0.49      (![X1, X0, X2, X4] : ((~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u96,negated_conjecture,
% 0.20/0.49      ((~r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)) | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2))).
% 0.20/0.49  
% 0.20/0.49  tff(u95,axiom,
% 0.20/0.49      (![X1, X3, X0, X2] : ((~r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,X3) | r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u94,axiom,
% 0.20/0.49      (![X1, X0, X2, X4] : ((~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.49  
% 0.20/0.49  tff(u93,negated_conjecture,
% 0.20/0.49      v4_orders_2(sK0)).
% 0.20/0.49  
% 0.20/0.49  % (880)# SZS output end Saturation.
% 0.20/0.49  % (880)------------------------------
% 0.20/0.49  % (880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (880)Termination reason: Satisfiable
% 0.20/0.49  
% 0.20/0.49  % (880)Memory used [KB]: 5373
% 0.20/0.49  % (880)Time elapsed: 0.095 s
% 0.20/0.49  % (880)------------------------------
% 0.20/0.49  % (880)------------------------------
% 0.20/0.49  % (864)Refutation not found, incomplete strategy% (864)------------------------------
% 0.20/0.49  % (864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (864)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (864)Memory used [KB]: 9850
% 0.20/0.49  % (864)Time elapsed: 0.089 s
% 0.20/0.49  % (864)------------------------------
% 0.20/0.49  % (864)------------------------------
% 0.20/0.49  % (860)Success in time 0.141 s
%------------------------------------------------------------------------------
