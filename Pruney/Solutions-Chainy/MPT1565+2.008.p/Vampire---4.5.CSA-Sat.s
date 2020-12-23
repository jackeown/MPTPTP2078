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
% DateTime   : Thu Dec  3 13:16:16 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    0
%              Number of atoms          :   56 (  56 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u72,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u71,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) )).

tff(u70,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) )).

tff(u69,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) )).

tff(u68,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X2) ) )).

tff(u67,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) )).

tff(u66,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) )).

tff(u65,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) )).

tff(u64,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) )).

tff(u63,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u62,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u61,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

% (29455)Refutation not found, incomplete strategy% (29455)------------------------------
% (29455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29455)Termination reason: Refutation not found, incomplete strategy

% (29455)Memory used [KB]: 895
% (29455)Time elapsed: 0.056 s
% (29455)------------------------------
% (29455)------------------------------
tff(u60,negated_conjecture,(
    l1_struct_0(sK0) )).

tff(u59,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u58,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u57,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u56,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) )).

tff(u55,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u54,negated_conjecture,(
    v2_yellow_0(sK0) )).

tff(u53,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (29457)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.50  % (29456)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (29455)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.50  % (29458)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (29456)# SZS output start Saturation.
% 0.21/0.50  tff(u72,axiom,
% 0.21/0.50      (![X0] : (r1_tarski(k1_xboole_0,X0)))).
% 0.21/0.50  
% 0.21/0.50  tff(u71,axiom,
% 0.21/0.50      (![X1, X0] : ((~r2_hidden(X0,X1) | ~r1_tarski(X1,X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u70,axiom,
% 0.21/0.50      (![X1, X0] : ((~r2_hidden(X0,X1) | m1_subset_1(X0,X1))))).
% 0.21/0.50  
% 0.21/0.50  tff(u69,axiom,
% 0.21/0.50      (![X1, X0] : ((~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))))).
% 0.21/0.50  
% 0.21/0.50  tff(u68,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X2,X3) | ~r1_lattice3(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u67,axiom,
% 0.21/0.50      (![X1, X3, X0, X2] : ((~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u66,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u65,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u64,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK2(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u63,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK1(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u62,axiom,
% 0.21/0.50      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u61,negated_conjecture,
% 0.21/0.50      ~v2_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  % (29455)Refutation not found, incomplete strategy% (29455)------------------------------
% 0.21/0.50  % (29455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29455)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29455)Memory used [KB]: 895
% 0.21/0.50  % (29455)Time elapsed: 0.056 s
% 0.21/0.50  % (29455)------------------------------
% 0.21/0.50  % (29455)------------------------------
% 0.21/0.50  tff(u60,negated_conjecture,
% 0.21/0.50      l1_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u59,axiom,
% 0.21/0.50      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u58,negated_conjecture,
% 0.21/0.50      l1_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u57,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~r1_orders_2(X0,sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u56,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2))))).
% 0.21/0.50  
% 0.21/0.50  tff(u55,negated_conjecture,
% 0.21/0.50      v5_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u54,negated_conjecture,
% 0.21/0.50      v2_yellow_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u53,negated_conjecture,
% 0.21/0.50      ((~~r1_yellow_0(sK0,u1_struct_0(sK0))) | ~r1_yellow_0(sK0,u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  % (29456)# SZS output end Saturation.
% 0.21/0.50  % (29456)------------------------------
% 0.21/0.50  % (29456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29456)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (29456)Memory used [KB]: 5373
% 0.21/0.50  % (29456)Time elapsed: 0.059 s
% 0.21/0.50  % (29456)------------------------------
% 0.21/0.50  % (29456)------------------------------
% 0.21/0.50  % (29449)Success in time 0.135 s
%------------------------------------------------------------------------------
