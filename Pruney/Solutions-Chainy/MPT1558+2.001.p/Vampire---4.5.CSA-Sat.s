%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:05 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   10 (  10 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    0
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u73,negated_conjecture,
    ( ~ ( k10_lattice3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) != k1_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2))) )
    | k10_lattice3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) != k1_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2))) )).

tff(u72,axiom,(
    ! [X1,X0] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) )).

tff(u71,axiom,(
    ! [X1,X0] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) )).

tff(u70,axiom,(
    ! [X1,X0] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) )).

tff(u69,negated_conjecture,
    ( ~ v4_orders_2(sK0)
    | v4_orders_2(sK0) )).

tff(u68,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | v5_orders_2(sK0) )).

tff(u67,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u66,negated_conjecture,
    ( ~ r1_yellow_0(sK0,sK1)
    | r1_yellow_0(sK0,sK1) )).

tff(u65,negated_conjecture,
    ( ~ r1_yellow_0(sK0,sK2)
    | r1_yellow_0(sK0,sK2) )).

tff(u64,negated_conjecture,
    ( ~ r1_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2)))
    | r1_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:54:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (16363)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.44  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.44  % (16363)# SZS output start Saturation.
% 0.22/0.44  tff(u73,negated_conjecture,
% 0.22/0.44      ((~(k10_lattice3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) != k1_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2))))) | (k10_lattice3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) != k1_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2)))))).
% 0.22/0.44  
% 0.22/0.44  tff(u72,axiom,
% 0.22/0.44      (![X1, X0] : ((k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)))))).
% 0.22/0.44  
% 0.22/0.44  tff(u71,axiom,
% 0.22/0.44      (![X1, X0] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))))).
% 0.22/0.44  
% 0.22/0.44  tff(u70,axiom,
% 0.22/0.44      (![X1, X0] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))))).
% 0.22/0.44  
% 0.22/0.44  tff(u69,negated_conjecture,
% 0.22/0.44      ((~v4_orders_2(sK0)) | v4_orders_2(sK0))).
% 0.22/0.44  
% 0.22/0.44  tff(u68,negated_conjecture,
% 0.22/0.44      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 0.22/0.44  
% 0.22/0.44  tff(u67,negated_conjecture,
% 0.22/0.44      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.22/0.44  
% 0.22/0.44  tff(u66,negated_conjecture,
% 0.22/0.44      ((~r1_yellow_0(sK0,sK1)) | r1_yellow_0(sK0,sK1))).
% 0.22/0.44  
% 0.22/0.44  tff(u65,negated_conjecture,
% 0.22/0.44      ((~r1_yellow_0(sK0,sK2)) | r1_yellow_0(sK0,sK2))).
% 0.22/0.44  
% 0.22/0.44  tff(u64,negated_conjecture,
% 0.22/0.44      ((~r1_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2)))) | r1_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2))))).
% 0.22/0.44  
% 0.22/0.44  % (16363)# SZS output end Saturation.
% 0.22/0.44  % (16363)------------------------------
% 0.22/0.44  % (16363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (16363)Termination reason: Satisfiable
% 0.22/0.44  
% 0.22/0.44  % (16363)Memory used [KB]: 10618
% 0.22/0.44  % (16363)Time elapsed: 0.005 s
% 0.22/0.44  % (16363)------------------------------
% 0.22/0.44  % (16363)------------------------------
% 0.22/0.45  % (16345)Success in time 0.084 s
%------------------------------------------------------------------------------
