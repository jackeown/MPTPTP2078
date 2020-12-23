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
% DateTime   : Thu Dec  3 13:16:05 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
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
    ( ~ ( k11_lattice3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2)) != k2_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2))) )
    | k11_lattice3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2)) != k2_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2))) )).

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
    ( ~ r2_yellow_0(sK0,sK1)
    | r2_yellow_0(sK0,sK1) )).

tff(u65,negated_conjecture,
    ( ~ r2_yellow_0(sK0,sK2)
    | r2_yellow_0(sK0,sK2) )).

tff(u64,negated_conjecture,
    ( ~ r2_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2)))
    | r2_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:52:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (11895)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.42  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.42  % (11895)# SZS output start Saturation.
% 0.21/0.42  tff(u73,negated_conjecture,
% 0.21/0.42      ((~(k11_lattice3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2)) != k2_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2))))) | (k11_lattice3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2)) != k2_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2)))))).
% 0.21/0.42  
% 0.21/0.42  tff(u72,axiom,
% 0.21/0.42      (![X1, X0] : ((k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)))))).
% 0.21/0.42  
% 0.21/0.42  tff(u71,axiom,
% 0.21/0.42      (![X1, X0] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))))).
% 0.21/0.42  
% 0.21/0.42  tff(u70,axiom,
% 0.21/0.42      (![X1, X0] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))))).
% 0.21/0.42  
% 0.21/0.42  tff(u69,negated_conjecture,
% 0.21/0.42      ((~v4_orders_2(sK0)) | v4_orders_2(sK0))).
% 0.21/0.42  
% 0.21/0.42  tff(u68,negated_conjecture,
% 0.21/0.42      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 0.21/0.42  
% 0.21/0.42  tff(u67,negated_conjecture,
% 0.21/0.42      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.21/0.42  
% 0.21/0.42  tff(u66,negated_conjecture,
% 0.21/0.42      ((~r2_yellow_0(sK0,sK1)) | r2_yellow_0(sK0,sK1))).
% 0.21/0.42  
% 0.21/0.42  tff(u65,negated_conjecture,
% 0.21/0.42      ((~r2_yellow_0(sK0,sK2)) | r2_yellow_0(sK0,sK2))).
% 0.21/0.42  
% 0.21/0.42  tff(u64,negated_conjecture,
% 0.21/0.42      ((~r2_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2)))) | r2_yellow_0(sK0,k3_tarski(k2_tarski(sK1,sK2))))).
% 0.21/0.42  
% 0.21/0.42  % (11895)# SZS output end Saturation.
% 0.21/0.42  % (11895)------------------------------
% 0.21/0.42  % (11895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (11895)Termination reason: Satisfiable
% 0.21/0.42  
% 0.21/0.42  % (11895)Memory used [KB]: 10618
% 0.21/0.42  % (11895)Time elapsed: 0.006 s
% 0.21/0.42  % (11895)------------------------------
% 0.21/0.42  % (11895)------------------------------
% 0.21/0.42  % (11879)Success in time 0.067 s
%------------------------------------------------------------------------------
