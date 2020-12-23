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
% DateTime   : Thu Dec  3 13:16:12 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   10 (  10 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    0
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u72,negated_conjecture,
    ( ~ ( sK1 != k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    | k6_domain_1(u1_struct_0(sK0),sK1) != k2_tarski(sK1,sK1)
    | sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

tff(u71,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k2_tarski(sK1,sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

tff(u70,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u69,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u68,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u67,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u66,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u65,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u64,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) )).

tff(u63,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (10476)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (10474)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (10475)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (10475)Refutation not found, incomplete strategy% (10475)------------------------------
% 0.20/0.47  % (10475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (10475)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (10475)Memory used [KB]: 6140
% 0.20/0.47  % (10475)Time elapsed: 0.053 s
% 0.20/0.47  % (10475)------------------------------
% 0.20/0.47  % (10475)------------------------------
% 0.20/0.47  % (10485)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (10472)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.47  % (10472)# SZS output start Saturation.
% 0.20/0.47  tff(u72,negated_conjecture,
% 0.20/0.47      ((~(sK1 != k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) | (~(k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1))) | (sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u71,negated_conjecture,
% 0.20/0.47      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)))).
% 0.20/0.47  
% 0.20/0.47  tff(u70,negated_conjecture,
% 0.20/0.47      ~v2_struct_0(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u69,negated_conjecture,
% 0.20/0.47      l1_struct_0(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u68,axiom,
% 0.20/0.47      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u67,negated_conjecture,
% 0.20/0.47      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u66,axiom,
% 0.20/0.47      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u65,negated_conjecture,
% 0.20/0.47      l1_orders_2(sK0)).
% 0.20/0.47  
% 0.20/0.47  tff(u64,axiom,
% 0.20/0.47      (![X1, X0] : ((~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k2_tarski(X1,X1)) | v1_xboole_0(X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u63,negated_conjecture,
% 0.20/0.47      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.47  
% 0.20/0.47  % (10472)# SZS output end Saturation.
% 0.20/0.47  % (10472)------------------------------
% 0.20/0.47  % (10472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (10472)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (10472)Memory used [KB]: 6140
% 0.20/0.47  % (10472)Time elapsed: 0.052 s
% 0.20/0.47  % (10472)------------------------------
% 0.20/0.47  % (10472)------------------------------
% 0.20/0.47  % (10469)Success in time 0.111 s
%------------------------------------------------------------------------------
