%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:04 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    0
%              Number of atoms          :   55 (  55 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u60,axiom,(
    ! [X1,X3,X0,X2,X4] :
      ( ~ r1_tarski(X3,X4)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(sK5(X0,X1,X2),X4)
      | sP0(X0,X1,X2) ) )).

tff(u59,negated_conjecture,(
    ! [X1,X3,X0,X2,X4] :
      ( ~ r1_tarski(sK4,X3)
      | ~ r1_tarski(X2,sK3)
      | sP0(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X4)
      | ~ r1_tarski(X3,X4) ) )).

tff(u58,negated_conjecture,(
    r1_tarski(sK3,sK4) )).

tff(u57,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) )).

tff(u56,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) )).

tff(u55,negated_conjecture,(
    ! [X1,X3,X0,X2] :
      ( r2_hidden(sK5(X1,X2,X0),X3)
      | sP0(X1,X2,X0)
      | ~ r1_tarski(X0,sK3)
      | ~ r1_tarski(sK4,X3) ) )).

tff(u54,axiom,(
    ! [X1,X3,X0,X2] :
      ( r2_hidden(sK5(X0,X1,X2),X3)
      | sP0(X0,X1,X2)
      | ~ r1_tarski(X2,X3) ) )).

tff(u53,negated_conjecture,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK5(X1,X2,X0),sK4)
      | ~ r1_tarski(X0,sK3)
      | sP0(X1,X2,X0) ) )).

tff(u52,negated_conjecture,(
    l1_orders_2(sK2) )).

tff(u51,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u50,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) )).

tff(u49,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r2_lattice3(X5,X7,sK5(X4,X5,X6))
      | ~ l1_orders_2(X5)
      | sP0(X4,X5,X6)
      | sP0(sK5(X4,X5,X6),X5,X7) ) )).

tff(u48,negated_conjecture,(
    ~ r1_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4)) )).

tff(u47,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X1,sK5(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) )).

tff(u46,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) )).

tff(u45,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ sP0(sK5(X0,X1,X2),X1,X3)
      | ~ l1_orders_2(X1)
      | sP0(X0,X1,X2)
      | r2_lattice3(X1,X3,sK5(X0,X1,X2)) ) )).

tff(u44,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) )).

tff(u43,axiom,(
    ! [X1,X0,X2] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) )).

tff(u42,axiom,(
    ! [X1,X3,X0,X2] :
      ( sP1(X3,X1,sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ l1_orders_2(X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:52:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (2833)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (2825)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.48  % (2825)Refutation not found, incomplete strategy% (2825)------------------------------
% 0.22/0.48  % (2825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (2825)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (2825)Memory used [KB]: 5245
% 0.22/0.48  % (2825)Time elapsed: 0.063 s
% 0.22/0.48  % (2825)------------------------------
% 0.22/0.48  % (2825)------------------------------
% 0.22/0.48  % (2832)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.48  % (2832)# SZS output start Saturation.
% 0.22/0.48  tff(u60,axiom,
% 0.22/0.48      (![X1, X3, X0, X2, X4] : ((~r1_tarski(X3,X4) | ~r1_tarski(X2,X3) | r2_hidden(sK5(X0,X1,X2),X4) | sP0(X0,X1,X2))))).
% 0.22/0.48  
% 0.22/0.48  tff(u59,negated_conjecture,
% 0.22/0.48      (![X1, X3, X0, X2, X4] : ((~r1_tarski(sK4,X3) | ~r1_tarski(X2,sK3) | sP0(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X4) | ~r1_tarski(X3,X4))))).
% 0.22/0.48  
% 0.22/0.48  tff(u58,negated_conjecture,
% 0.22/0.48      r1_tarski(sK3,sK4)).
% 0.22/0.48  
% 0.22/0.48  tff(u57,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u56,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X2) | sP0(X0,X1,X2))))).
% 0.22/0.48  
% 0.22/0.48  tff(u55,negated_conjecture,
% 0.22/0.48      (![X1, X3, X0, X2] : ((r2_hidden(sK5(X1,X2,X0),X3) | sP0(X1,X2,X0) | ~r1_tarski(X0,sK3) | ~r1_tarski(sK4,X3))))).
% 0.22/0.48  
% 0.22/0.48  tff(u54,axiom,
% 0.22/0.48      (![X1, X3, X0, X2] : ((r2_hidden(sK5(X0,X1,X2),X3) | sP0(X0,X1,X2) | ~r1_tarski(X2,X3))))).
% 0.22/0.48  
% 0.22/0.48  tff(u53,negated_conjecture,
% 0.22/0.48      (![X1, X0, X2] : ((r2_hidden(sK5(X1,X2,X0),sK4) | ~r1_tarski(X0,sK3) | sP0(X1,X2,X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u52,negated_conjecture,
% 0.22/0.48      l1_orders_2(sK2)).
% 0.22/0.48  
% 0.22/0.48  tff(u51,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u50,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2))))).
% 0.22/0.48  
% 0.22/0.48  tff(u49,axiom,
% 0.22/0.48      (![X5, X7, X4, X6] : ((~r2_lattice3(X5,X7,sK5(X4,X5,X6)) | ~l1_orders_2(X5) | sP0(X4,X5,X6) | sP0(sK5(X4,X5,X6),X5,X7))))).
% 0.22/0.48  
% 0.22/0.48  tff(u48,negated_conjecture,
% 0.22/0.48      ~r1_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4))).
% 0.22/0.48  
% 0.22/0.48  tff(u47,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((~r1_orders_2(X1,sK5(X0,X1,X2),X0) | sP0(X0,X1,X2))))).
% 0.22/0.48  
% 0.22/0.48  tff(u46,axiom,
% 0.22/0.48      (![X1, X0, X2, X4] : ((~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u45,axiom,
% 0.22/0.48      (![X1, X3, X0, X2] : ((~sP0(sK5(X0,X1,X2),X1,X3) | ~l1_orders_2(X1) | sP0(X0,X1,X2) | r2_lattice3(X1,X3,sK5(X0,X1,X2)))))).
% 0.22/0.48  
% 0.22/0.48  tff(u44,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_lattice3(X1,X0,X2))))).
% 0.22/0.48  
% 0.22/0.48  tff(u43,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((~sP1(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP0(X2,X1,X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u42,axiom,
% 0.22/0.48      (![X1, X3, X0, X2] : ((sP1(X3,X1,sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~l1_orders_2(X1))))).
% 0.22/0.48  
% 0.22/0.48  % (2832)# SZS output end Saturation.
% 0.22/0.48  % (2832)------------------------------
% 0.22/0.48  % (2832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (2832)Termination reason: Satisfiable
% 0.22/0.48  
% 0.22/0.48  % (2832)Memory used [KB]: 5373
% 0.22/0.48  % (2832)Time elapsed: 0.064 s
% 0.22/0.48  % (2832)------------------------------
% 0.22/0.48  % (2832)------------------------------
% 0.22/0.48  % (2823)Success in time 0.119 s
%------------------------------------------------------------------------------
