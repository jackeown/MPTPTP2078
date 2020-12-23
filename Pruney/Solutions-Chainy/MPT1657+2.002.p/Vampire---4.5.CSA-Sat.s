%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:11 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
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
      ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u41,axiom,(
    ! [X1,X0,X2] :
      ( r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u40,negated_conjecture,
    ( ~ ~ r2_yellow_0(sK0,sK1)
    | ~ r2_yellow_0(sK0,sK1) )).

tff(u39,negated_conjecture,
    ( ~ r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | r2_yellow_0(sK0,k4_waybel_0(sK0,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (3258)WARNING: option uwaf not known.
% 0.21/0.45  % (3252)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.46  % (3249)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.46  % (3258)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.46  % (3268)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.21/0.47  % (3253)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (3253)Refutation not found, incomplete strategy% (3253)------------------------------
% 0.21/0.47  % (3253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (3253)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (3253)Memory used [KB]: 895
% 0.21/0.47  % (3253)Time elapsed: 0.065 s
% 0.21/0.47  % (3253)------------------------------
% 0.21/0.47  % (3253)------------------------------
% 0.21/0.47  % (3255)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.47  % (3255)# SZS output start Saturation.
% 0.21/0.47  tff(u44,negated_conjecture,
% 0.21/0.47      ~v2_struct_0(sK0)).
% 0.21/0.47  
% 0.21/0.47  tff(u43,negated_conjecture,
% 0.21/0.47      l1_orders_2(sK0)).
% 0.21/0.47  
% 0.21/0.47  tff(u42,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((~r1_lattice3(X0,X2,sK2(X0,X1,X2)) | ~r2_yellow_0(X0,X1) | r2_yellow_0(X0,X2) | ~r1_lattice3(X0,X1,sK2(X0,X1,X2)) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u41,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((r1_lattice3(X0,X2,sK2(X0,X1,X2)) | r1_lattice3(X0,X1,sK2(X0,X1,X2)) | ~r2_yellow_0(X0,X1) | r2_yellow_0(X0,X2) | ~l1_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u40,negated_conjecture,
% 0.21/0.47      ((~~r2_yellow_0(sK0,sK1)) | ~r2_yellow_0(sK0,sK1))).
% 0.21/0.47  
% 0.21/0.47  tff(u39,negated_conjecture,
% 0.21/0.47      ((~r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))) | r2_yellow_0(sK0,k4_waybel_0(sK0,sK1)))).
% 0.21/0.47  
% 0.21/0.47  % (3255)# SZS output end Saturation.
% 0.21/0.47  % (3255)------------------------------
% 0.21/0.47  % (3255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (3255)Termination reason: Satisfiable
% 0.21/0.47  
% 0.21/0.47  % (3255)Memory used [KB]: 5373
% 0.21/0.47  % (3255)Time elapsed: 0.038 s
% 0.21/0.47  % (3255)------------------------------
% 0.21/0.47  % (3255)------------------------------
% 0.21/0.48  % (3246)Success in time 0.123 s
%------------------------------------------------------------------------------
