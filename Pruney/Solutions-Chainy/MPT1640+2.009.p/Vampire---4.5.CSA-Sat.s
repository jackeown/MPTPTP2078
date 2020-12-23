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
% DateTime   : Thu Dec  3 13:17:00 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    0
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u48,negated_conjecture,(
    sK1 != sK2 )).

tff(u47,negated_conjecture,(
    k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2) )).

tff(u46,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u45,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u44,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u43,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u42,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u41,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u40,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,X1)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u39,negated_conjecture,(
    r1_orders_2(sK0,sK1,sK1) )).

tff(u38,negated_conjecture,(
    r1_orders_2(sK0,sK2,sK2) )).

tff(u37,negated_conjecture,(
    v5_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n001.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:41:15 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (3074)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.45  % (3074)Refutation not found, incomplete strategy% (3074)------------------------------
% 0.22/0.45  % (3074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (3074)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.45  
% 0.22/0.45  % (3074)Memory used [KB]: 6012
% 0.22/0.45  % (3074)Time elapsed: 0.054 s
% 0.22/0.45  % (3074)------------------------------
% 0.22/0.45  % (3074)------------------------------
% 0.22/0.46  % (3090)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.46  % (3090)Refutation not found, incomplete strategy% (3090)------------------------------
% 0.22/0.46  % (3090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (3090)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (3090)Memory used [KB]: 10490
% 0.22/0.46  % (3090)Time elapsed: 0.062 s
% 0.22/0.46  % (3090)------------------------------
% 0.22/0.46  % (3090)------------------------------
% 0.22/0.46  % (3095)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.46  % (3095)# SZS output start Saturation.
% 0.22/0.46  tff(u48,negated_conjecture,
% 0.22/0.46      (sK1 != sK2)).
% 0.22/0.46  
% 0.22/0.46  tff(u47,negated_conjecture,
% 0.22/0.46      (k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2))).
% 0.22/0.46  
% 0.22/0.46  tff(u46,negated_conjecture,
% 0.22/0.46      ~v2_struct_0(sK0)).
% 0.22/0.46  
% 0.22/0.46  tff(u45,negated_conjecture,
% 0.22/0.46      v3_orders_2(sK0)).
% 0.22/0.46  
% 0.22/0.46  tff(u44,negated_conjecture,
% 0.22/0.46      l1_orders_2(sK0)).
% 0.22/0.46  
% 0.22/0.46  tff(u43,axiom,
% 0.22/0.46      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.46  
% 0.22/0.46  tff(u42,negated_conjecture,
% 0.22/0.46      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.46  
% 0.22/0.46  tff(u41,negated_conjecture,
% 0.22/0.46      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.22/0.46  
% 0.22/0.46  tff(u40,axiom,
% 0.22/0.46      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,X1) | (X1 = X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.22/0.46  
% 0.22/0.46  tff(u39,negated_conjecture,
% 0.22/0.46      r1_orders_2(sK0,sK1,sK1)).
% 0.22/0.46  
% 0.22/0.46  tff(u38,negated_conjecture,
% 0.22/0.46      r1_orders_2(sK0,sK2,sK2)).
% 0.22/0.46  
% 0.22/0.46  tff(u37,negated_conjecture,
% 0.22/0.46      v5_orders_2(sK0)).
% 0.22/0.46  
% 0.22/0.46  % (3095)# SZS output end Saturation.
% 0.22/0.46  % (3095)------------------------------
% 0.22/0.46  % (3095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (3095)Termination reason: Satisfiable
% 0.22/0.46  
% 0.22/0.46  % (3095)Memory used [KB]: 10618
% 0.22/0.46  % (3095)Time elapsed: 0.059 s
% 0.22/0.46  % (3095)------------------------------
% 0.22/0.46  % (3095)------------------------------
% 0.22/0.47  % (3069)Success in time 0.103 s
%------------------------------------------------------------------------------
