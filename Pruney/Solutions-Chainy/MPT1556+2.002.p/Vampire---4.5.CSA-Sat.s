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
% DateTime   : Thu Dec  3 13:16:04 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    5 (   5 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    0
%              Number of atoms          :    5 (   5 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u17,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u16,negated_conjecture,(
    r1_tarski(sK1,sK2) )).

tff(u15,negated_conjecture,(
    r1_yellow_0(sK0,sK1) )).

tff(u14,negated_conjecture,(
    r1_yellow_0(sK0,sK2) )).

tff(u13,negated_conjecture,(
    ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:54:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.48  % (28207)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.49  % (28215)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.49  % (28207)Refutation not found, incomplete strategy% (28207)------------------------------
% 0.21/0.49  % (28207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (28207)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (28207)Memory used [KB]: 5245
% 0.21/0.49  % (28207)Time elapsed: 0.066 s
% 0.21/0.49  % (28207)------------------------------
% 0.21/0.49  % (28207)------------------------------
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (28215)# SZS output start Saturation.
% 0.21/0.49  tff(u17,negated_conjecture,
% 0.21/0.49      l1_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  tff(u16,negated_conjecture,
% 0.21/0.49      r1_tarski(sK1,sK2)).
% 0.21/0.49  
% 0.21/0.49  tff(u15,negated_conjecture,
% 0.21/0.49      r1_yellow_0(sK0,sK1)).
% 0.21/0.49  
% 0.21/0.49  tff(u14,negated_conjecture,
% 0.21/0.49      r1_yellow_0(sK0,sK2)).
% 0.21/0.49  
% 0.21/0.49  tff(u13,negated_conjecture,
% 0.21/0.49      ~r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))).
% 0.21/0.49  
% 0.21/0.49  % (28215)# SZS output end Saturation.
% 0.21/0.49  % (28215)------------------------------
% 0.21/0.49  % (28215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (28215)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (28215)Memory used [KB]: 5245
% 0.21/0.49  % (28215)Time elapsed: 0.079 s
% 0.21/0.49  % (28215)------------------------------
% 0.21/0.49  % (28215)------------------------------
% 0.21/0.49  % (28195)Success in time 0.134 s
%------------------------------------------------------------------------------
