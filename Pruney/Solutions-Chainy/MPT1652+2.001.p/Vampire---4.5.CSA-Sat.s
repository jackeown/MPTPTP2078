%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:07 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    6 (   6 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    0
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u44,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u43,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u42,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_lattice3(X0,X2,sK2(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u41,axiom,(
    ! [X1,X0,X2] :
      ( r2_lattice3(X0,X2,sK2(X0,X1,X2))
      | r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u40,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,sK1)
    | ~ r1_yellow_0(sK0,sK1) )).

tff(u39,negated_conjecture,
    ( ~ r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))
    | r1_yellow_0(sK0,k3_waybel_0(sK0,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:49:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (23831)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.47  % (23841)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.47  % (23832)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.47  % (23832)# SZS output start Saturation.
% 0.22/0.47  tff(u44,negated_conjecture,
% 0.22/0.47      ~v2_struct_0(sK0)).
% 0.22/0.47  
% 0.22/0.47  tff(u43,negated_conjecture,
% 0.22/0.47      l1_orders_2(sK0)).
% 0.22/0.47  
% 0.22/0.47  tff(u42,axiom,
% 0.22/0.47      (![X1, X0, X2] : ((~r2_lattice3(X0,X2,sK2(X0,X1,X2)) | ~r1_yellow_0(X0,X1) | r1_yellow_0(X0,X2) | ~r2_lattice3(X0,X1,sK2(X0,X1,X2)) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u41,axiom,
% 0.22/0.47      (![X1, X0, X2] : ((r2_lattice3(X0,X2,sK2(X0,X1,X2)) | r2_lattice3(X0,X1,sK2(X0,X1,X2)) | ~r1_yellow_0(X0,X1) | r1_yellow_0(X0,X2) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u40,negated_conjecture,
% 0.22/0.47      ((~~r1_yellow_0(sK0,sK1)) | ~r1_yellow_0(sK0,sK1))).
% 0.22/0.47  
% 0.22/0.47  tff(u39,negated_conjecture,
% 0.22/0.47      ((~r1_yellow_0(sK0,k3_waybel_0(sK0,sK1))) | r1_yellow_0(sK0,k3_waybel_0(sK0,sK1)))).
% 0.22/0.47  
% 0.22/0.47  % (23832)# SZS output end Saturation.
% 0.22/0.47  % (23832)------------------------------
% 0.22/0.47  % (23832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (23832)Termination reason: Satisfiable
% 0.22/0.47  
% 0.22/0.47  % (23832)Memory used [KB]: 5373
% 0.22/0.47  % (23832)Time elapsed: 0.048 s
% 0.22/0.47  % (23832)------------------------------
% 0.22/0.47  % (23832)------------------------------
% 0.22/0.47  % (23824)Success in time 0.108 s
%------------------------------------------------------------------------------
