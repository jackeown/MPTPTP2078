%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:07 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u30,negated_conjecture,(
    k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_waybel_0(sK0,sK1)) )).

tff(u29,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u28,axiom,(
    ! [X1,X0,X2] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X2,sK2(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) )).

tff(u27,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u26,negated_conjecture,(
    r1_yellow_0(sK0,sK1) )).

tff(u25,negated_conjecture,(
    ! [X1,X0] :
      ( ~ r2_lattice3(sK0,X1,sK2(sK0,X0,X1))
      | ~ r2_lattice3(sK0,X0,sK2(sK0,X0,X1))
      | ~ r1_yellow_0(sK0,X0)
      | k1_yellow_0(sK0,X0) = k1_yellow_0(sK0,X1) ) )).

tff(u24,axiom,(
    ! [X1,X0,X2] :
      ( r2_lattice3(X0,X2,sK2(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | v2_struct_0(X0)
      | r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:38:33 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.41  % (28906)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.41  % (28901)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.42  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.42  % (28901)# SZS output start Saturation.
% 0.22/0.42  tff(u30,negated_conjecture,
% 0.22/0.42      (k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_waybel_0(sK0,sK1)))).
% 0.22/0.42  
% 0.22/0.42  tff(u29,negated_conjecture,
% 0.22/0.42      ~v2_struct_0(sK0)).
% 0.22/0.42  
% 0.22/0.42  tff(u28,axiom,
% 0.22/0.42      (![X1, X0, X2] : ((v2_struct_0(X0) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X2,sK2(X0,X1,X2)) | ~r2_lattice3(X0,X1,sK2(X0,X1,X2)) | (k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)))))).
% 0.22/0.42  
% 0.22/0.42  tff(u27,negated_conjecture,
% 0.22/0.42      l1_orders_2(sK0)).
% 0.22/0.42  
% 0.22/0.42  tff(u26,negated_conjecture,
% 0.22/0.42      r1_yellow_0(sK0,sK1)).
% 0.22/0.42  
% 0.22/0.42  tff(u25,negated_conjecture,
% 0.22/0.42      (![X1, X0] : ((~r2_lattice3(sK0,X1,sK2(sK0,X0,X1)) | ~r2_lattice3(sK0,X0,sK2(sK0,X0,X1)) | ~r1_yellow_0(sK0,X0) | (k1_yellow_0(sK0,X0) = k1_yellow_0(sK0,X1)))))).
% 0.22/0.42  
% 0.22/0.42  tff(u24,axiom,
% 0.22/0.42      (![X1, X0, X2] : ((r2_lattice3(X0,X2,sK2(X0,X1,X2)) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X1) | v2_struct_0(X0) | r2_lattice3(X0,X1,sK2(X0,X1,X2)) | (k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)))))).
% 0.22/0.42  
% 0.22/0.42  % (28901)# SZS output end Saturation.
% 0.22/0.42  % (28901)------------------------------
% 0.22/0.42  % (28901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (28901)Termination reason: Satisfiable
% 0.22/0.42  
% 0.22/0.42  % (28901)Memory used [KB]: 10490
% 0.22/0.42  % (28901)Time elapsed: 0.004 s
% 0.22/0.42  % (28901)------------------------------
% 0.22/0.42  % (28901)------------------------------
% 0.22/0.42  % (28900)Success in time 0.063 s
%------------------------------------------------------------------------------
