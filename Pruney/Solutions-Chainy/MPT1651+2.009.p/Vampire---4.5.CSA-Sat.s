%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:06 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    0
%              Number of atoms          :   69 (  69 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u98,negated_conjecture,(
    v4_orders_2(sK2) )).

tff(u97,negated_conjecture,(
    l1_orders_2(sK2) )).

tff(u96,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u95,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( ~ m1_subset_1(sK5(X0,X1,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2))
        | r1_orders_2(sK2,sK5(X0,X1,k3_waybel_0(sK2,sK3)),sK4)
        | sP0(X0,X1,k3_waybel_0(sK2,sK3)) ) )).

tff(u94,negated_conjecture,(
    m1_subset_1(sK4,u1_struct_0(sK2)) )).

tff(u93,negated_conjecture,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) )).

tff(u92,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u91,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,sK5(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) )).

tff(u90,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) )).

tff(u89,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X1,X0] :
        ( ~ r1_orders_2(sK2,X0,sK5(X1,sK2,k3_waybel_0(sK2,sK3)))
        | r1_orders_2(sK2,X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | sP0(X1,sK2,k3_waybel_0(sK2,sK3)) ) )).

tff(u88,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( r1_orders_2(sK2,sK5(X0,sK2,k3_waybel_0(sK2,sK3)),sK4)
        | sP0(X0,sK2,k3_waybel_0(sK2,sK3)) ) )).

tff(u87,negated_conjecture,
    ( ~ ~ r2_lattice3(sK2,sK3,sK4)
    | ~ r2_lattice3(sK2,sK3,sK4) )).

tff(u86,negated_conjecture,(
    ! [X0] :
      ( ~ r2_lattice3(sK2,X0,sK4)
      | sP0(sK4,sK2,X0) ) )).

tff(u85,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK5(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK5(X4,X5,X6),X5,X7) ) )).

tff(u84,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4) )).

tff(u83,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | ! [X0] :
        ( ~ r2_hidden(X0,k3_waybel_0(sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,sK4) ) )).

tff(u82,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u81,negated_conjecture,(
    ! [X0] :
      ( ~ sP0(sK4,sK2,X0)
      | r2_lattice3(sK2,X0,sK4) ) )).

tff(u80,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) )).

tff(u79,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK5(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r2_lattice3(X1,X3,sK5(X0,X1,X2)) ) )).

tff(u78,negated_conjecture,
    ( ~ r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)
    | sP0(sK4,sK2,k3_waybel_0(sK2,sK3)) )).

tff(u77,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) )).

tff(u76,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u75,negated_conjecture,(
    ! [X0] : sP1(X0,sK2,sK4) )).

tff(u74,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:42:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (481)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.47  % (479)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.22/0.47  % (489)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.22/0.48  % (487)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.49  % (481)Refutation not found, incomplete strategy% (481)------------------------------
% 0.22/0.49  % (481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (481)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (481)Memory used [KB]: 9850
% 0.22/0.49  % (481)Time elapsed: 0.062 s
% 0.22/0.49  % (481)------------------------------
% 0.22/0.49  % (481)------------------------------
% 0.22/0.49  % (478)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.49  % (494)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.49  % (494)Refutation not found, incomplete strategy% (494)------------------------------
% 0.22/0.49  % (494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (494)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (494)Memory used [KB]: 895
% 0.22/0.49  % (494)Time elapsed: 0.034 s
% 0.22/0.49  % (494)------------------------------
% 0.22/0.49  % (494)------------------------------
% 0.22/0.49  % (483)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.50  % (483)Refutation not found, incomplete strategy% (483)------------------------------
% 0.22/0.50  % (483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (483)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (483)Memory used [KB]: 895
% 0.22/0.50  % (483)Time elapsed: 0.079 s
% 0.22/0.50  % (483)------------------------------
% 0.22/0.50  % (483)------------------------------
% 0.22/0.50  % (490)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.50  % (491)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.50  % (484)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.50  % (485)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.50  % (485)# SZS output start Saturation.
% 0.22/0.50  tff(u98,negated_conjecture,
% 0.22/0.50      v4_orders_2(sK2)).
% 0.22/0.50  
% 0.22/0.50  tff(u97,negated_conjecture,
% 0.22/0.50      l1_orders_2(sK2)).
% 0.22/0.50  
% 0.22/0.50  tff(u96,axiom,
% 0.22/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u95,negated_conjecture,
% 0.22/0.50      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((~m1_subset_1(sK5(X0,X1,k3_waybel_0(sK2,sK3)),u1_struct_0(sK2)) | r1_orders_2(sK2,sK5(X0,X1,k3_waybel_0(sK2,sK3)),sK4) | sP0(X0,X1,k3_waybel_0(sK2,sK3))))))).
% 0.22/0.50  
% 0.22/0.50  tff(u94,negated_conjecture,
% 0.22/0.50      m1_subset_1(sK4,u1_struct_0(sK2))).
% 0.22/0.50  
% 0.22/0.50  tff(u93,negated_conjecture,
% 0.22/0.50      m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))).
% 0.22/0.50  
% 0.22/0.50  tff(u92,axiom,
% 0.22/0.50      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.22/0.50  
% 0.22/0.50  tff(u91,axiom,
% 0.22/0.50      (![X1, X0, X2] : ((~r1_orders_2(X1,sK5(X0,X1,X2),X0) | sP0(X0,X1,X2))))).
% 0.22/0.50  
% 0.22/0.50  tff(u90,axiom,
% 0.22/0.50      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u89,negated_conjecture,
% 0.22/0.50      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X1, X0] : ((~r1_orders_2(sK2,X0,sK5(X1,sK2,k3_waybel_0(sK2,sK3))) | r1_orders_2(sK2,X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK2)) | sP0(X1,sK2,k3_waybel_0(sK2,sK3))))))).
% 0.22/0.50  
% 0.22/0.50  tff(u88,negated_conjecture,
% 0.22/0.50      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X0] : ((r1_orders_2(sK2,sK5(X0,sK2,k3_waybel_0(sK2,sK3)),sK4) | sP0(X0,sK2,k3_waybel_0(sK2,sK3))))))).
% 0.22/0.50  
% 0.22/0.50  tff(u87,negated_conjecture,
% 0.22/0.50      ((~~r2_lattice3(sK2,sK3,sK4)) | ~r2_lattice3(sK2,sK3,sK4))).
% 0.22/0.50  
% 0.22/0.50  tff(u86,negated_conjecture,
% 0.22/0.50      (![X0] : ((~r2_lattice3(sK2,X0,sK4) | sP0(sK4,sK2,X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u85,axiom,
% 0.22/0.50      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK5(X4,X5,X6),X5,X7))))).
% 0.22/0.50  
% 0.22/0.50  tff(u84,negated_conjecture,
% 0.22/0.50      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4))).
% 0.22/0.50  
% 0.22/0.50  tff(u83,negated_conjecture,
% 0.22/0.50      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | (![X0] : ((~r2_hidden(X0,k3_waybel_0(sK2,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,sK4)))))).
% 0.22/0.50  
% 0.22/0.50  tff(u82,axiom,
% 0.22/0.50      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.22/0.50  
% 0.22/0.50  tff(u81,negated_conjecture,
% 0.22/0.50      (![X0] : ((~sP0(sK4,sK2,X0) | r2_lattice3(sK2,X0,sK4))))).
% 0.22/0.50  
% 0.22/0.50  tff(u80,axiom,
% 0.22/0.50      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u79,axiom,
% 0.22/0.50      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r2_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.22/0.50  
% 0.22/0.50  tff(u78,negated_conjecture,
% 0.22/0.50      ((~r2_lattice3(sK2,k3_waybel_0(sK2,sK3),sK4)) | sP0(sK4,sK2,k3_waybel_0(sK2,sK3)))).
% 0.22/0.50  
% 0.22/0.50  tff(u77,axiom,
% 0.22/0.50      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_lattice3(X1,X0,X2))))).
% 0.22/0.50  
% 0.22/0.50  tff(u76,axiom,
% 0.22/0.50      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u75,negated_conjecture,
% 0.22/0.50      (![X0] : (sP1(X0,sK2,sK4)))).
% 0.22/0.50  
% 0.22/0.50  tff(u74,axiom,
% 0.22/0.50      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.22/0.50  
% 0.22/0.50  % (485)# SZS output end Saturation.
% 0.22/0.50  % (485)------------------------------
% 0.22/0.50  % (485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (485)Termination reason: Satisfiable
% 0.22/0.50  
% 0.22/0.50  % (485)Memory used [KB]: 5373
% 0.22/0.50  % (485)Time elapsed: 0.035 s
% 0.22/0.50  % (485)------------------------------
% 0.22/0.50  % (485)------------------------------
% 0.22/0.50  % (477)Success in time 0.138 s
%------------------------------------------------------------------------------
