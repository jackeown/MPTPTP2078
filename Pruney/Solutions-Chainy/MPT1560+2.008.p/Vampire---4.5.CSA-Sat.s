%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:06 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   35 (  35 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (5415)Termination reason: Refutation not found, incomplete strategy

% (5415)Memory used [KB]: 6140
tff(u126,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) )).

tff(u125,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u124,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u123,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u122,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u121,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u120,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u119,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
      | v1_xboole_0(X0) ) )).

tff(u118,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u117,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | v3_orders_2(sK0) )).

tff(u116,axiom,(
    ! [X1,X0] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u115,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | r1_orders_2(sK0,sK1,sK1) )).

tff(u114,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | v5_orders_2(sK0) )).

tff(u113,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

tff(u112,negated_conjecture,
    ( ~ ~ r2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ r2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (5415)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (5413)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (5417)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (5416)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (5413)Refutation not found, incomplete strategy% (5413)------------------------------
% 0.20/0.46  % (5413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (5413)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (5413)Memory used [KB]: 1663
% 0.20/0.46  % (5413)Time elapsed: 0.052 s
% 0.20/0.46  % (5413)------------------------------
% 0.20/0.46  % (5413)------------------------------
% 0.20/0.46  % (5415)Refutation not found, incomplete strategy% (5415)------------------------------
% 0.20/0.46  % (5415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.46  % (5417)# SZS output start Saturation.
% 0.20/0.46  % (5415)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (5415)Memory used [KB]: 6140
% 0.20/0.46  tff(u126,negated_conjecture,
% 0.20/0.46      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))).
% 0.20/0.46  
% 0.20/0.46  tff(u125,negated_conjecture,
% 0.20/0.46      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  tff(u124,negated_conjecture,
% 0.20/0.46      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  tff(u123,axiom,
% 0.20/0.46      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u122,negated_conjecture,
% 0.20/0.46      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.20/0.46  
% 0.20/0.46  tff(u121,axiom,
% 0.20/0.46      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u120,negated_conjecture,
% 0.20/0.46      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.20/0.46  
% 0.20/0.46  tff(u119,axiom,
% 0.20/0.46      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | v1_xboole_0(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u118,negated_conjecture,
% 0.20/0.46      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 0.20/0.46  
% 0.20/0.46  tff(u117,negated_conjecture,
% 0.20/0.46      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 0.20/0.46  
% 0.20/0.46  tff(u116,axiom,
% 0.20/0.46      (![X1, X0] : ((r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u115,negated_conjecture,
% 0.20/0.46      ((~r1_orders_2(sK0,sK1,sK1)) | r1_orders_2(sK0,sK1,sK1))).
% 0.20/0.46  
% 0.20/0.46  tff(u114,negated_conjecture,
% 0.20/0.46      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 0.20/0.46  
% 0.20/0.46  tff(u113,negated_conjecture,
% 0.20/0.46      ((~~r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))).
% 0.20/0.46  
% 0.20/0.46  tff(u112,negated_conjecture,
% 0.20/0.46      ((~~r2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))).
% 0.20/0.46  
% 0.20/0.46  % (5417)# SZS output end Saturation.
% 0.20/0.46  % (5417)------------------------------
% 0.20/0.46  % (5417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5417)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (5417)Memory used [KB]: 6140
% 0.20/0.47  % (5417)Time elapsed: 0.050 s
% 0.20/0.47  % (5417)------------------------------
% 0.20/0.47  % (5417)------------------------------
% 0.20/0.47  % (5415)Time elapsed: 0.052 s
% 0.20/0.47  % (5415)------------------------------
% 0.20/0.47  % (5415)------------------------------
% 0.20/0.47  % (5416)Refutation not found, incomplete strategy% (5416)------------------------------
% 0.20/0.47  % (5416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5416)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (5416)Memory used [KB]: 6140
% 0.20/0.47  % (5416)Time elapsed: 0.052 s
% 0.20/0.47  % (5416)------------------------------
% 0.20/0.47  % (5416)------------------------------
% 0.20/0.47  % (5423)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (5422)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (5406)Success in time 0.115 s
%------------------------------------------------------------------------------
