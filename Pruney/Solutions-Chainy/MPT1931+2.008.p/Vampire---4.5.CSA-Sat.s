%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:38 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   78 (  78 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u99,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) )).

tff(u98,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r1_orders_2(sK1,X0,sK3(sK0,sK1,X1,X0))
      | r1_waybel_0(sK0,sK1,X1) ) )).

tff(u97,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(sK3(sK0,sK1,X1,X0),u1_struct_0(sK1))
      | r1_waybel_0(sK0,sK1,X1) ) )).

tff(u96,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(k2_waybel_0(sK0,sK1,X0),u1_struct_0(sK0)) ) )).

tff(u95,negated_conjecture,(
    m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) )).

tff(u94,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u93,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u92,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,X2) ) )).

tff(u91,negated_conjecture,
    ( ~ r2_hidden(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))
    | r2_hidden(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)) )).

tff(u90,negated_conjecture,(
    ~ v2_struct_0(sK1) )).

tff(u89,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u88,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u87,negated_conjecture,(
    l1_struct_0(sK1) )).

tff(u86,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u85,negated_conjecture,(
    l1_orders_2(sK1) )).

tff(u84,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r1_orders_2(X1,X3,sK3(X0,X1,X2,X3))
      | r1_waybel_0(X0,X1,X2) ) )).

tff(u83,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,X2) ) )).

tff(u82,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) )).

tff(u81,axiom,(
    ! [X1,X0] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) ) )).

tff(u80,axiom,(
    ! [X1,X0] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) )).

tff(u79,negated_conjecture,(
    l1_waybel_0(sK1,sK0) )).

tff(u78,negated_conjecture,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) )).

tff(u77,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | v2_struct_0(X0) ) )).

tff(u76,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r2_hidden(k2_waybel_0(X0,X1,X4),X2)
      | ~ r1_waybel_0(X0,X1,X2) ) )).

tff(u75,negated_conjecture,(
    v4_orders_2(sK1) )).

tff(u74,negated_conjecture,(
    v7_waybel_0(sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:42:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (5336)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.49  % (5329)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.49  % (5329)Refutation not found, incomplete strategy% (5329)------------------------------
% 0.22/0.49  % (5329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (5338)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.49  % (5337)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.49  % (5330)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.49  % (5329)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (5329)Memory used [KB]: 895
% 0.22/0.49  % (5329)Time elapsed: 0.050 s
% 0.22/0.49  % (5329)------------------------------
% 0.22/0.49  % (5329)------------------------------
% 0.22/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.49  % (5330)# SZS output start Saturation.
% 0.22/0.49  tff(u99,axiom,
% 0.22/0.49      (![X1, X0] : ((~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u98,negated_conjecture,
% 0.22/0.49      (![X1, X0] : ((~m1_subset_1(X0,u1_struct_0(sK1)) | r1_orders_2(sK1,X0,sK3(sK0,sK1,X1,X0)) | r1_waybel_0(sK0,sK1,X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u97,negated_conjecture,
% 0.22/0.49      (![X1, X0] : ((~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(sK3(sK0,sK1,X1,X0),u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u96,negated_conjecture,
% 0.22/0.49      (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(k2_waybel_0(sK0,sK1,X0),u1_struct_0(sK0)))))).
% 0.22/0.49  
% 0.22/0.49  tff(u95,negated_conjecture,
% 0.22/0.49      m1_subset_1(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))).
% 0.22/0.49  
% 0.22/0.49  tff(u94,axiom,
% 0.22/0.49      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.22/0.49  
% 0.22/0.49  tff(u93,negated_conjecture,
% 0.22/0.49      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.22/0.49  
% 0.22/0.49  tff(u92,axiom,
% 0.22/0.49      (![X1, X3, X0, X2] : ((~r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X3)),X2) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | v2_struct_0(X0) | r1_waybel_0(X0,X1,X2))))).
% 0.22/0.49  
% 0.22/0.49  tff(u91,negated_conjecture,
% 0.22/0.49      ((~r2_hidden(k4_yellow_6(sK0,sK1),u1_struct_0(sK0))) | r2_hidden(k4_yellow_6(sK0,sK1),u1_struct_0(sK0)))).
% 0.22/0.49  
% 0.22/0.49  tff(u90,negated_conjecture,
% 0.22/0.49      ~v2_struct_0(sK1)).
% 0.22/0.49  
% 0.22/0.49  tff(u89,negated_conjecture,
% 0.22/0.49      ~v2_struct_0(sK0)).
% 0.22/0.49  
% 0.22/0.49  tff(u88,negated_conjecture,
% 0.22/0.49      l1_struct_0(sK0)).
% 0.22/0.49  
% 0.22/0.49  tff(u87,negated_conjecture,
% 0.22/0.49      l1_struct_0(sK1)).
% 0.22/0.49  
% 0.22/0.49  tff(u86,axiom,
% 0.22/0.49      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.22/0.49  
% 0.22/0.49  tff(u85,negated_conjecture,
% 0.22/0.49      l1_orders_2(sK1)).
% 0.22/0.49  
% 0.22/0.49  tff(u84,axiom,
% 0.22/0.49      (![X1, X3, X0, X2] : ((~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | r1_orders_2(X1,X3,sK3(X0,X1,X2,X3)) | r1_waybel_0(X0,X1,X2))))).
% 0.22/0.49  
% 0.22/0.49  tff(u83,axiom,
% 0.22/0.49      (![X1, X3, X0, X2] : ((~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X1)) | r1_waybel_0(X0,X1,X2))))).
% 0.22/0.49  
% 0.22/0.49  tff(u82,axiom,
% 0.22/0.49      (![X1, X0, X2] : ((~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)))))).
% 0.22/0.49  
% 0.22/0.49  tff(u81,axiom,
% 0.22/0.49      (![X1, X0] : ((~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0) | m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)))))).
% 0.22/0.49  
% 0.22/0.49  tff(u80,axiom,
% 0.22/0.49      (![X1, X0] : ((~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | l1_orders_2(X1))))).
% 0.22/0.49  
% 0.22/0.49  tff(u79,negated_conjecture,
% 0.22/0.49      l1_waybel_0(sK1,sK0)).
% 0.22/0.49  
% 0.22/0.49  tff(u78,negated_conjecture,
% 0.22/0.49      ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))).
% 0.22/0.49  
% 0.22/0.49  tff(u77,axiom,
% 0.22/0.49      (![X1, X0, X2] : ((~r1_waybel_0(X0,X1,X2) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) | v2_struct_0(X0))))).
% 0.22/0.49  
% 0.22/0.49  tff(u76,axiom,
% 0.22/0.49      (![X1, X0, X2, X4] : ((~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X4,u1_struct_0(X1)) | v2_struct_0(X0) | r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_waybel_0(X0,X1,X2))))).
% 0.22/0.49  
% 0.22/0.49  tff(u75,negated_conjecture,
% 0.22/0.49      v4_orders_2(sK1)).
% 0.22/0.49  
% 0.22/0.49  tff(u74,negated_conjecture,
% 0.22/0.49      v7_waybel_0(sK1)).
% 0.22/0.49  
% 0.22/0.49  % (5330)# SZS output end Saturation.
% 0.22/0.49  % (5330)------------------------------
% 0.22/0.49  % (5330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (5330)Termination reason: Satisfiable
% 0.22/0.49  
% 0.22/0.49  % (5330)Memory used [KB]: 5373
% 0.22/0.49  % (5330)Time elapsed: 0.065 s
% 0.22/0.49  % (5330)------------------------------
% 0.22/0.49  % (5330)------------------------------
% 0.22/0.49  % (5323)Success in time 0.127 s
%------------------------------------------------------------------------------
