%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:58 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u72,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | v5_orders_2(sK0) )).

tff(u71,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u70,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u69,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | X1 = X2 ) )).

tff(u68,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK2)
    | r1_orders_2(sK0,sK2,sK2) )).

tff(u67,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,sK1)
    | ~ r1_yellow_0(sK0,sK1) )).

tff(u66,negated_conjecture,
    ( ~ ! [X3] :
          ( ~ r2_lattice3(sK0,sK1,X3)
          | r1_orders_2(sK0,sK2,X3)
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ! [X3] :
        ( ~ r2_lattice3(sK0,sK1,X3)
        | r1_orders_2(sK0,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) )).

tff(u65,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK1,sK2)
    | r2_lattice3(sK0,sK1,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:23:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (14750)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.49  % (14742)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.49  % (14742)Refutation not found, incomplete strategy% (14742)------------------------------
% 0.22/0.49  % (14742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.49  % (14742)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (14742)Memory used [KB]: 10618
% 0.22/0.49  % (14742)Time elapsed: 0.064 s
% 0.22/0.49  % (14742)------------------------------
% 0.22/0.49  % (14742)------------------------------
% 0.22/0.50  % (14750)# SZS output start Saturation.
% 0.22/0.50  tff(u72,negated_conjecture,
% 0.22/0.50      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 0.22/0.50  
% 0.22/0.50  tff(u71,negated_conjecture,
% 0.22/0.50      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.22/0.50  
% 0.22/0.50  tff(u70,negated_conjecture,
% 0.22/0.50      ((~m1_subset_1(sK2,u1_struct_0(sK0))) | m1_subset_1(sK2,u1_struct_0(sK0)))).
% 0.22/0.50  
% 0.22/0.50  tff(u69,axiom,
% 0.22/0.50      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | (X1 = X2))))).
% 0.22/0.50  
% 0.22/0.50  tff(u68,negated_conjecture,
% 0.22/0.50      ((~r1_orders_2(sK0,sK2,sK2)) | r1_orders_2(sK0,sK2,sK2))).
% 0.22/0.50  
% 0.22/0.50  tff(u67,negated_conjecture,
% 0.22/0.50      ((~~r1_yellow_0(sK0,sK1)) | ~r1_yellow_0(sK0,sK1))).
% 0.22/0.50  
% 0.22/0.50  tff(u66,negated_conjecture,
% 0.22/0.50      ((~(![X3] : ((~r2_lattice3(sK0,sK1,X3) | r1_orders_2(sK0,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)))))) | (![X3] : ((~r2_lattice3(sK0,sK1,X3) | r1_orders_2(sK0,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0))))))).
% 0.22/0.50  
% 0.22/0.50  tff(u65,negated_conjecture,
% 0.22/0.50      ((~r2_lattice3(sK0,sK1,sK2)) | r2_lattice3(sK0,sK1,sK2))).
% 0.22/0.50  
% 0.22/0.50  % (14750)# SZS output end Saturation.
% 0.22/0.50  % (14750)------------------------------
% 0.22/0.50  % (14750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (14750)Termination reason: Satisfiable
% 0.22/0.50  
% 0.22/0.50  % (14750)Memory used [KB]: 10618
% 0.22/0.50  % (14750)Time elapsed: 0.070 s
% 0.22/0.50  % (14750)------------------------------
% 0.22/0.50  % (14750)------------------------------
% 0.22/0.50  % (14733)Success in time 0.129 s
%------------------------------------------------------------------------------
