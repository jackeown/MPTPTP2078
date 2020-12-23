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
% DateTime   : Thu Dec  3 13:16:13 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   35 (  35 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u120,negated_conjecture,
    ( ~ ( sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1)) )
    | sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

tff(u119,negated_conjecture,
    ( ~ ( sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1)) )
    | sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

tff(u118,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k2_tarski(sK1,sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

tff(u117,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u116,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u115,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u114,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u113,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u112,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u111,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) )).

tff(u110,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u109,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | v3_orders_2(sK0) )).

tff(u108,axiom,(
    ! [X1,X0] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u107,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | r1_orders_2(sK0,sK1,sK1) )).

tff(u106,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | v5_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:20:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (22262)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (22264)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (22267)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (22264)Refutation not found, incomplete strategy% (22264)------------------------------
% 0.21/0.47  % (22264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (22264)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (22264)Memory used [KB]: 1535
% 0.21/0.47  % (22264)Time elapsed: 0.051 s
% 0.21/0.47  % (22264)------------------------------
% 0.21/0.47  % (22264)------------------------------
% 0.21/0.47  % (22274)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.47  % (22267)# SZS output start Saturation.
% 0.21/0.47  tff(u120,negated_conjecture,
% 0.21/0.47      ((~(sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1)))) | (sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1))))).
% 0.21/0.47  
% 0.21/0.47  tff(u119,negated_conjecture,
% 0.21/0.47      ((~(sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1)))) | (sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1))))).
% 0.21/0.47  
% 0.21/0.47  tff(u118,negated_conjecture,
% 0.21/0.47      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)))).
% 0.21/0.47  
% 0.21/0.47  tff(u117,negated_conjecture,
% 0.21/0.47      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.21/0.47  
% 0.21/0.47  tff(u116,negated_conjecture,
% 0.21/0.47      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.21/0.47  
% 0.21/0.47  tff(u115,axiom,
% 0.21/0.47      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u114,negated_conjecture,
% 0.21/0.47      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u113,axiom,
% 0.21/0.47      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u112,negated_conjecture,
% 0.21/0.47      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.21/0.47  
% 0.21/0.47  tff(u111,axiom,
% 0.21/0.47      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k2_tarski(X1,X1)) | v1_xboole_0(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u110,negated_conjecture,
% 0.21/0.47      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u109,negated_conjecture,
% 0.21/0.47      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 0.21/0.47  
% 0.21/0.47  tff(u108,axiom,
% 0.21/0.47      (![X1, X0] : ((r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u107,negated_conjecture,
% 0.21/0.47      ((~r1_orders_2(sK0,sK1,sK1)) | r1_orders_2(sK0,sK1,sK1))).
% 0.21/0.47  
% 0.21/0.47  tff(u106,negated_conjecture,
% 0.21/0.47      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 0.21/0.47  
% 0.21/0.47  % (22267)# SZS output end Saturation.
% 0.21/0.47  % (22267)------------------------------
% 0.21/0.47  % (22267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (22267)Termination reason: Satisfiable
% 0.21/0.47  
% 0.21/0.47  % (22267)Memory used [KB]: 6140
% 0.21/0.47  % (22267)Time elapsed: 0.052 s
% 0.21/0.47  % (22267)------------------------------
% 0.21/0.47  % (22267)------------------------------
% 0.21/0.47  % (22260)Success in time 0.112 s
%------------------------------------------------------------------------------
