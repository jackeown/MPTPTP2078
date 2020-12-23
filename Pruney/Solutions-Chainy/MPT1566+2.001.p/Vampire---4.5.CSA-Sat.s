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
% DateTime   : Thu Dec  3 13:16:16 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   66 (  66 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u158,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | m1_subset_1(X1,X0) ) )).

tff(u157,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1) ) )).

tff(u156,axiom,(
    ! [X0,X2] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) )).

tff(u155,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u154,negated_conjecture,
    ( ~ ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

tff(u153,axiom,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) )).

tff(u152,negated_conjecture,
    ( ~ r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) )).

tff(u151,negated_conjecture,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0)) )).

tff(u150,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u149,axiom,(
    ! [X1,X0,X2] :
      ( r2_hidden(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2)
      | v1_xboole_0(u1_struct_0(X0)) ) )).

tff(u148,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u147,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u146,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u145,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u144,negated_conjecture,
    ( ~ m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) )).

tff(u143,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u142,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u141,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u140,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u139,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u138,negated_conjecture,
    ( ~ ~ r1_orders_2(sK0,k3_yellow_0(sK0),sK1)
    | ~ r1_orders_2(sK0,k3_yellow_0(sK0),sK1) )).

tff(u137,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u136,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | v5_orders_2(sK0) )).

tff(u135,negated_conjecture,
    ( ~ v1_yellow_0(sK0)
    | v1_yellow_0(sK0) )).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (5222)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.45  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.46  % (5230)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (5222)# SZS output start Saturation.
% 0.20/0.46  tff(u158,axiom,
% 0.20/0.46      (![X1, X0] : ((~v1_xboole_0(X0) | ~v1_xboole_0(X1) | m1_subset_1(X1,X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u157,axiom,
% 0.20/0.46      (![X1, X0] : ((~v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X1))))).
% 0.20/0.46  
% 0.20/0.46  tff(u156,axiom,
% 0.20/0.46      (![X0, X2] : ((~v1_xboole_0(X0) | ~r2_hidden(X2,X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u155,axiom,
% 0.20/0.46      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u154,negated_conjecture,
% 0.20/0.46      ((~~v1_xboole_0(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)))).
% 0.20/0.46  
% 0.20/0.46  tff(u153,axiom,
% 0.20/0.46      (![X0] : ((r2_hidden(sK3(X0),X0) | v1_xboole_0(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u152,negated_conjecture,
% 0.20/0.46      ((~r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))) | r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)))).
% 0.20/0.46  
% 0.20/0.46  tff(u151,negated_conjecture,
% 0.20/0.46      ((~r2_hidden(sK1,u1_struct_0(sK0))) | r2_hidden(sK1,u1_struct_0(sK0)))).
% 0.20/0.46  
% 0.20/0.46  tff(u150,axiom,
% 0.20/0.46      (![X1, X0, X2] : ((r2_hidden(sK2(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u149,axiom,
% 0.20/0.46      (![X1, X0, X2] : ((r2_hidden(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2) | v1_xboole_0(u1_struct_0(X0)))))).
% 0.20/0.46  
% 0.20/0.46  tff(u148,axiom,
% 0.20/0.46      (![X1, X0] : ((~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u147,axiom,
% 0.20/0.46      (![X1, X0] : ((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u146,negated_conjecture,
% 0.20/0.46      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 0.20/0.46  
% 0.20/0.46  tff(u145,axiom,
% 0.20/0.46      (![X1, X0, X2] : ((m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u144,negated_conjecture,
% 0.20/0.46      ((~m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))) | m1_subset_1(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)))).
% 0.20/0.46  
% 0.20/0.46  tff(u143,negated_conjecture,
% 0.20/0.46      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  tff(u142,negated_conjecture,
% 0.20/0.46      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  tff(u141,axiom,
% 0.20/0.46      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u140,negated_conjecture,
% 0.20/0.46      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.20/0.46  
% 0.20/0.46  tff(u139,axiom,
% 0.20/0.46      (![X1, X0, X2, X4] : ((~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u138,negated_conjecture,
% 0.20/0.46      ((~~r1_orders_2(sK0,k3_yellow_0(sK0),sK1)) | ~r1_orders_2(sK0,k3_yellow_0(sK0),sK1))).
% 0.20/0.46  
% 0.20/0.46  tff(u137,axiom,
% 0.20/0.46      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK2(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.20/0.46  
% 0.20/0.46  tff(u136,negated_conjecture,
% 0.20/0.46      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 0.20/0.46  
% 0.20/0.46  tff(u135,negated_conjecture,
% 0.20/0.46      ((~v1_yellow_0(sK0)) | v1_yellow_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  % (5222)# SZS output end Saturation.
% 0.20/0.46  % (5222)------------------------------
% 0.20/0.46  % (5222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (5222)Termination reason: Satisfiable
% 0.20/0.46  
% 0.20/0.46  % (5222)Memory used [KB]: 6140
% 0.20/0.46  % (5222)Time elapsed: 0.044 s
% 0.20/0.46  % (5222)------------------------------
% 0.20/0.46  % (5222)------------------------------
% 0.20/0.46  % (5215)Success in time 0.104 s
%------------------------------------------------------------------------------
