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
% DateTime   : Thu Dec  3 13:23:37 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   49 (  49 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u89,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u88,axiom,(
    ! [X0] :
      ( ~ v2_struct_0(sK3(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) )).

tff(u87,negated_conjecture,
    ( ~ ~ v2_struct_0(sK1)
    | ~ v2_struct_0(sK1) )).

tff(u86,negated_conjecture,(
    v2_pre_topc(sK0) )).

tff(u85,axiom,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r2_hidden(sK3(X0),k6_yellow_6(X0))
      | v1_compts_1(X0) ) )).

tff(u84,axiom,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_waybel_0(sK3(X0),X0)
      | v1_compts_1(X0) ) )).

tff(u83,axiom,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v7_waybel_0(sK3(X0))
      | v1_compts_1(X0) ) )).

tff(u82,axiom,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v4_orders_2(sK3(X0))
      | v1_compts_1(X0) ) )).

tff(u81,negated_conjecture,(
    l1_pre_topc(sK0) )).

tff(u80,negated_conjecture,
    ( ~ v1_compts_1(sK0)
    | v4_orders_2(sK1) )).

tff(u79,negated_conjecture,
    ( ~ v1_compts_1(sK0)
    | v7_waybel_0(sK1) )).

tff(u78,negated_conjecture,
    ( ~ v1_compts_1(sK0)
    | l1_waybel_0(sK1,sK0) )).

tff(u77,negated_conjecture,
    ( ~ v1_compts_1(sK0)
    | r2_hidden(sK1,k6_yellow_6(sK0)) )).

tff(u76,negated_conjecture,
    ( ~ v1_compts_1(sK0)
    | ! [X2] :
        ( ~ r3_waybel_9(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) )).

tff(u75,axiom,(
    ! [X0,X2] :
      ( ~ r3_waybel_9(X0,sK3(X0),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) )).

tff(u74,negated_conjecture,
    ( ~ v1_compts_1(sK0)
    | v1_compts_1(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (2140)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.46  % (2131)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (2126)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.46  % (2137)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.46  % (2137)Refutation not found, incomplete strategy% (2137)------------------------------
% 0.21/0.46  % (2137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (2126)Refutation not found, incomplete strategy% (2126)------------------------------
% 0.21/0.46  % (2126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (2126)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (2126)Memory used [KB]: 9850
% 0.21/0.46  % (2126)Time elapsed: 0.053 s
% 0.21/0.46  % (2126)------------------------------
% 0.21/0.46  % (2126)------------------------------
% 0.21/0.46  % (2137)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (2137)Memory used [KB]: 5373
% 0.21/0.46  % (2137)Time elapsed: 0.004 s
% 0.21/0.46  % (2137)------------------------------
% 0.21/0.46  % (2137)------------------------------
% 0.21/0.47  % (2129)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.47  % (2129)# SZS output start Saturation.
% 0.21/0.47  tff(u89,negated_conjecture,
% 0.21/0.47      ~v2_struct_0(sK0)).
% 0.21/0.47  
% 0.21/0.47  tff(u88,axiom,
% 0.21/0.47      (![X0] : ((~v2_struct_0(sK3(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_compts_1(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u87,negated_conjecture,
% 0.21/0.47      ((~~v2_struct_0(sK1)) | ~v2_struct_0(sK1))).
% 0.21/0.47  
% 0.21/0.47  tff(u86,negated_conjecture,
% 0.21/0.47      v2_pre_topc(sK0)).
% 0.21/0.47  
% 0.21/0.47  tff(u85,axiom,
% 0.21/0.47      (![X0] : ((~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r2_hidden(sK3(X0),k6_yellow_6(X0)) | v1_compts_1(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u84,axiom,
% 0.21/0.47      (![X0] : ((~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | l1_waybel_0(sK3(X0),X0) | v1_compts_1(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u83,axiom,
% 0.21/0.47      (![X0] : ((~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v7_waybel_0(sK3(X0)) | v1_compts_1(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u82,axiom,
% 0.21/0.47      (![X0] : ((~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v4_orders_2(sK3(X0)) | v1_compts_1(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u81,negated_conjecture,
% 0.21/0.47      l1_pre_topc(sK0)).
% 0.21/0.47  
% 0.21/0.47  tff(u80,negated_conjecture,
% 0.21/0.47      ((~v1_compts_1(sK0)) | v4_orders_2(sK1))).
% 0.21/0.47  
% 0.21/0.47  tff(u79,negated_conjecture,
% 0.21/0.47      ((~v1_compts_1(sK0)) | v7_waybel_0(sK1))).
% 0.21/0.47  
% 0.21/0.47  tff(u78,negated_conjecture,
% 0.21/0.47      ((~v1_compts_1(sK0)) | l1_waybel_0(sK1,sK0))).
% 0.21/0.47  
% 0.21/0.47  tff(u77,negated_conjecture,
% 0.21/0.47      ((~v1_compts_1(sK0)) | r2_hidden(sK1,k6_yellow_6(sK0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u76,negated_conjecture,
% 0.21/0.47      ((~v1_compts_1(sK0)) | (![X2] : ((~r3_waybel_9(sK0,sK1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0))))))).
% 0.21/0.47  
% 0.21/0.47  tff(u75,axiom,
% 0.21/0.47      (![X0, X2] : ((~r3_waybel_9(X0,sK3(X0),X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | v1_compts_1(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u74,negated_conjecture,
% 0.21/0.47      ((~v1_compts_1(sK0)) | v1_compts_1(sK0))).
% 0.21/0.47  
% 0.21/0.47  % (2129)# SZS output end Saturation.
% 0.21/0.47  % (2129)------------------------------
% 0.21/0.47  % (2129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (2129)Termination reason: Satisfiable
% 0.21/0.47  
% 0.21/0.47  % (2129)Memory used [KB]: 5373
% 0.21/0.47  % (2129)Time elapsed: 0.004 s
% 0.21/0.47  % (2129)------------------------------
% 0.21/0.47  % (2129)------------------------------
% 0.21/0.47  % (2136)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.47  % (2122)Success in time 0.113 s
%------------------------------------------------------------------------------
