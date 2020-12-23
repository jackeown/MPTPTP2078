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
% DateTime   : Thu Dec  3 13:17:01 EST 2020

% Result     : CounterSatisfiable 0.38s
% Output     : Saturation 0.38s
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
    ~ r1_tarski(k5_waybel_0(sK2,sK3),k5_waybel_0(sK2,sK4)) )).

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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:55:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (801013760)
% 0.14/0.37  ipcrm: permission denied for id (802095105)
% 0.14/0.37  ipcrm: permission denied for id (802226181)
% 0.14/0.38  ipcrm: permission denied for id (802291719)
% 0.14/0.38  ipcrm: permission denied for id (802324488)
% 0.14/0.38  ipcrm: permission denied for id (802357257)
% 0.21/0.38  ipcrm: permission denied for id (801046539)
% 0.21/0.38  ipcrm: permission denied for id (802488334)
% 0.21/0.39  ipcrm: permission denied for id (802586641)
% 0.21/0.40  ipcrm: permission denied for id (802783255)
% 0.21/0.40  ipcrm: permission denied for id (802848793)
% 0.21/0.40  ipcrm: permission denied for id (802881562)
% 0.21/0.40  ipcrm: permission denied for id (802914331)
% 0.21/0.40  ipcrm: permission denied for id (802979869)
% 0.21/0.40  ipcrm: permission denied for id (801177630)
% 0.21/0.41  ipcrm: permission denied for id (803045408)
% 0.21/0.41  ipcrm: permission denied for id (803078177)
% 0.21/0.41  ipcrm: permission denied for id (803110946)
% 0.21/0.41  ipcrm: permission denied for id (803209252)
% 0.21/0.41  ipcrm: permission denied for id (803242021)
% 0.21/0.41  ipcrm: permission denied for id (803274790)
% 0.21/0.42  ipcrm: permission denied for id (803307559)
% 0.21/0.42  ipcrm: permission denied for id (803340328)
% 0.21/0.42  ipcrm: permission denied for id (803405866)
% 0.21/0.42  ipcrm: permission denied for id (803471404)
% 0.21/0.42  ipcrm: permission denied for id (803504173)
% 0.21/0.42  ipcrm: permission denied for id (803536942)
% 0.21/0.43  ipcrm: permission denied for id (803602480)
% 0.21/0.43  ipcrm: permission denied for id (801243186)
% 0.21/0.43  ipcrm: permission denied for id (803668019)
% 0.21/0.43  ipcrm: permission denied for id (801275956)
% 0.21/0.44  ipcrm: permission denied for id (803766327)
% 0.21/0.44  ipcrm: permission denied for id (803831865)
% 0.21/0.44  ipcrm: permission denied for id (803864634)
% 0.21/0.44  ipcrm: permission denied for id (803897403)
% 0.21/0.45  ipcrm: permission denied for id (804028479)
% 0.21/0.45  ipcrm: permission denied for id (804061248)
% 0.21/0.45  ipcrm: permission denied for id (801374273)
% 0.21/0.45  ipcrm: permission denied for id (801407042)
% 0.21/0.45  ipcrm: permission denied for id (801439812)
% 0.21/0.45  ipcrm: permission denied for id (804159557)
% 0.21/0.45  ipcrm: permission denied for id (801472582)
% 0.21/0.46  ipcrm: permission denied for id (804225096)
% 0.21/0.46  ipcrm: permission denied for id (804290634)
% 0.21/0.46  ipcrm: permission denied for id (801570892)
% 0.21/0.46  ipcrm: permission denied for id (804356173)
% 0.21/0.47  ipcrm: permission denied for id (804421711)
% 0.21/0.47  ipcrm: permission denied for id (804454480)
% 0.21/0.47  ipcrm: permission denied for id (804487249)
% 0.21/0.47  ipcrm: permission denied for id (804520018)
% 0.21/0.47  ipcrm: permission denied for id (804552787)
% 0.21/0.47  ipcrm: permission denied for id (804585556)
% 0.21/0.47  ipcrm: permission denied for id (801636437)
% 0.21/0.48  ipcrm: permission denied for id (804618326)
% 0.21/0.48  ipcrm: permission denied for id (801669207)
% 0.21/0.48  ipcrm: permission denied for id (804651096)
% 0.21/0.48  ipcrm: permission denied for id (804683865)
% 0.21/0.48  ipcrm: permission denied for id (804716634)
% 0.21/0.48  ipcrm: permission denied for id (801734748)
% 0.21/0.48  ipcrm: permission denied for id (804782173)
% 0.21/0.49  ipcrm: permission denied for id (801767518)
% 0.21/0.49  ipcrm: permission denied for id (804814943)
% 0.21/0.49  ipcrm: permission denied for id (804847712)
% 0.21/0.49  ipcrm: permission denied for id (804913250)
% 0.21/0.49  ipcrm: permission denied for id (804946019)
% 0.21/0.49  ipcrm: permission denied for id (801800293)
% 0.21/0.50  ipcrm: permission denied for id (805044327)
% 0.21/0.50  ipcrm: permission denied for id (801833064)
% 0.21/0.50  ipcrm: permission denied for id (805077097)
% 0.21/0.50  ipcrm: permission denied for id (805208173)
% 0.21/0.51  ipcrm: permission denied for id (805240942)
% 0.21/0.51  ipcrm: permission denied for id (805273711)
% 0.21/0.51  ipcrm: permission denied for id (801931377)
% 0.21/0.51  ipcrm: permission denied for id (805339250)
% 0.21/0.51  ipcrm: permission denied for id (801964148)
% 0.21/0.52  ipcrm: permission denied for id (801996918)
% 0.21/0.52  ipcrm: permission denied for id (805503097)
% 0.21/0.52  ipcrm: permission denied for id (805535866)
% 0.21/0.52  ipcrm: permission denied for id (805601404)
% 0.21/0.53  ipcrm: permission denied for id (805666942)
% 0.21/0.53  ipcrm: permission denied for id (805699711)
% 0.38/0.60  % (4344)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.38/0.64  % (4349)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.38/0.65  % (4335)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.38/0.65  % (4333)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.38/0.66  % (4344)Refutation not found, incomplete strategy% (4344)------------------------------
% 0.38/0.66  % (4344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.66  % (4344)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.66  
% 0.38/0.66  % (4344)Memory used [KB]: 5373
% 0.38/0.66  % (4344)Time elapsed: 0.063 s
% 0.38/0.66  % (4344)------------------------------
% 0.38/0.66  % (4344)------------------------------
% 0.38/0.66  % (4340)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.38/0.66  % (4340)Refutation not found, incomplete strategy% (4340)------------------------------
% 0.38/0.66  % (4340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.66  % (4340)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.66  
% 0.38/0.66  % (4340)Memory used [KB]: 9850
% 0.38/0.66  % (4340)Time elapsed: 0.092 s
% 0.38/0.66  % (4340)------------------------------
% 0.38/0.66  % (4340)------------------------------
% 0.38/0.66  % (4338)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.38/0.66  % (4347)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.38/0.66  % SZS status CounterSatisfiable for theBenchmark
% 0.38/0.66  % (4338)# SZS output start Saturation.
% 0.38/0.66  tff(u95,negated_conjecture,
% 0.38/0.66      ~r1_tarski(k5_waybel_0(sK2,sK3),k5_waybel_0(sK2,sK4))).
% 0.38/0.66  
% 0.38/0.66  tff(u94,axiom,
% 0.38/0.66      (![X0] : (r1_tarski(X0,X0)))).
% 0.38/0.66  
% 0.38/0.66  tff(u93,axiom,
% 0.38/0.66      (![X1, X0] : ((~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1))))).
% 0.38/0.66  
% 0.38/0.66  tff(u92,axiom,
% 0.38/0.66      (![X1, X0] : ((r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1))))).
% 0.38/0.66  
% 0.38/0.66  tff(u91,axiom,
% 0.38/0.66      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.38/0.66  
% 0.38/0.66  tff(u90,axiom,
% 0.38/0.66      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.38/0.66  
% 0.38/0.66  tff(u89,axiom,
% 0.38/0.66      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1))))).
% 0.38/0.66  
% 0.38/0.66  tff(u88,negated_conjecture,
% 0.38/0.66      m1_subset_1(sK3,u1_struct_0(sK2))).
% 0.38/0.66  
% 0.38/0.66  tff(u87,negated_conjecture,
% 0.38/0.66      m1_subset_1(sK4,u1_struct_0(sK2))).
% 0.38/0.66  
% 0.38/0.66  tff(u86,axiom,
% 0.38/0.66      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.38/0.66  
% 0.38/0.66  tff(u85,negated_conjecture,
% 0.38/0.66      l1_orders_2(sK2)).
% 0.38/0.66  
% 0.38/0.66  tff(u84,negated_conjecture,
% 0.38/0.66      (![X0] : ((~r1_lattice3(sK2,X0,sK3) | sP0(sK3,sK2,X0))))).
% 0.38/0.66  
% 0.38/0.66  tff(u83,negated_conjecture,
% 0.38/0.66      (![X0] : ((~r1_lattice3(sK2,X0,sK4) | r1_lattice3(sK2,X0,sK3))))).
% 0.38/0.66  
% 0.38/0.66  tff(u82,negated_conjecture,
% 0.38/0.66      (![X1] : ((~r1_lattice3(sK2,X1,sK4) | sP0(sK4,sK2,X1))))).
% 0.38/0.66  
% 0.38/0.66  tff(u81,axiom,
% 0.38/0.66      (![X5, X7, X4, X6] : ((~r1_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK5(X4,X5,X6),X5,X7))))).
% 0.38/0.66  
% 0.38/0.66  tff(u80,axiom,
% 0.38/0.66      (![X1, X0, X2] : ((~r1_orders_2(X1,X0,sK5(X0,X1,X2)) | sP0(X0,X1,X2))))).
% 0.38/0.66  
% 0.38/0.66  tff(u79,axiom,
% 0.38/0.66      (![X1, X3, X0, X2] : ((~r1_orders_2(X0,X3,X2) | r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0))))).
% 0.38/0.66  
% 0.38/0.66  tff(u78,negated_conjecture,
% 0.38/0.66      r1_orders_2(sK2,sK3,sK4)).
% 0.38/0.66  
% 0.38/0.66  tff(u77,negated_conjecture,
% 0.38/0.66      v4_orders_2(sK2)).
% 0.38/0.66  
% 0.38/0.66  tff(u76,negated_conjecture,
% 0.38/0.66      (![X0] : ((~sP0(sK3,sK2,X0) | r1_lattice3(sK2,X0,sK3))))).
% 0.38/0.66  
% 0.38/0.66  tff(u75,negated_conjecture,
% 0.38/0.66      (![X1] : ((~sP0(sK4,sK2,X1) | r1_lattice3(sK2,X1,sK4))))).
% 0.38/0.66  
% 0.38/0.66  tff(u74,axiom,
% 0.38/0.66      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X0,X4))))).
% 0.38/0.66  
% 0.38/0.66  tff(u73,axiom,
% 0.38/0.66      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r1_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.38/0.66  
% 0.38/0.66  tff(u72,axiom,
% 0.38/0.66      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r1_lattice3(X1,X0,X2))))).
% 0.38/0.66  
% 0.38/0.66  tff(u71,axiom,
% 0.38/0.66      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r1_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.38/0.66  
% 0.38/0.66  tff(u70,negated_conjecture,
% 0.38/0.66      (![X0] : (sP1(X0,sK2,sK3)))).
% 0.38/0.66  
% 0.38/0.66  tff(u69,negated_conjecture,
% 0.38/0.66      (![X1] : (sP1(X1,sK2,sK4)))).
% 0.38/0.66  
% 0.38/0.66  tff(u68,axiom,
% 0.38/0.66      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.38/0.66  
% 0.38/0.66  % (4338)# SZS output end Saturation.
% 0.38/0.66  % (4338)------------------------------
% 0.38/0.66  % (4338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.66  % (4338)Termination reason: Satisfiable
% 0.38/0.66  
% 0.38/0.66  % (4338)Memory used [KB]: 5373
% 0.38/0.66  % (4338)Time elapsed: 0.086 s
% 0.38/0.66  % (4338)------------------------------
% 0.38/0.66  % (4338)------------------------------
% 0.38/0.66  % (4336)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.38/0.66  % (4176)Success in time 0.302 s
%------------------------------------------------------------------------------
