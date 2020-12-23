%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:07 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    0
%              Number of atoms          :   29 (  29 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u66,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) )).

tff(u65,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

tff(u64,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u63,axiom,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) )).

tff(u62,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u61,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u60,axiom,(
    ! [X1,X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) )).

tff(u59,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u58,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0) ) )).

tff(u57,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u56,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u55,axiom,(
    ! [X1,X0] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u54,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u53,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k1_tarski(sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:25:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (12551)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (12537)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (12535)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (12541)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (12551)# SZS output start Saturation.
% 0.21/0.46  tff(u66,axiom,
% 0.21/0.46      (![X0] : ((k2_tarski(X0,X0) = k1_tarski(X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u65,negated_conjecture,
% 0.21/0.46      ((~~v1_xboole_0(u1_struct_0(sK0))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)))).
% 0.21/0.46  
% 0.21/0.46  tff(u64,negated_conjecture,
% 0.21/0.46      ~v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  tff(u63,axiom,
% 0.21/0.46      (![X0] : ((v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u62,axiom,
% 0.21/0.46      (![X0] : ((l1_struct_0(X0) | ~l1_orders_2(X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u61,negated_conjecture,
% 0.21/0.46      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.21/0.46  
% 0.21/0.46  tff(u60,axiom,
% 0.21/0.46      (![X1, X0] : ((v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | (k6_domain_1(X0,X1) = k1_tarski(X1)))))).
% 0.21/0.46  
% 0.21/0.46  tff(u59,negated_conjecture,
% 0.21/0.46      l1_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  tff(u58,negated_conjecture,
% 0.21/0.46      ((~~v1_xboole_0(u1_struct_0(sK0))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0))))))).
% 0.21/0.46  
% 0.21/0.46  tff(u57,negated_conjecture,
% 0.21/0.46      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.46  
% 0.21/0.46  tff(u56,negated_conjecture,
% 0.21/0.46      v3_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  tff(u55,axiom,
% 0.21/0.46      (![X1, X0] : ((r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u54,negated_conjecture,
% 0.21/0.46      v5_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  tff(u53,negated_conjecture,
% 0.21/0.46      ((~~r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | (~~v1_xboole_0(u1_struct_0(sK0))) | ~r1_yellow_0(sK0,k1_tarski(sK1)))).
% 0.21/0.46  
% 0.21/0.46  % (12551)# SZS output end Saturation.
% 0.21/0.46  % (12551)------------------------------
% 0.21/0.46  % (12551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (12551)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (12551)Memory used [KB]: 6140
% 0.21/0.46  % (12551)Time elapsed: 0.044 s
% 0.21/0.46  % (12551)------------------------------
% 0.21/0.46  % (12551)------------------------------
% 0.21/0.46  % (12531)Success in time 0.108 s
%------------------------------------------------------------------------------
