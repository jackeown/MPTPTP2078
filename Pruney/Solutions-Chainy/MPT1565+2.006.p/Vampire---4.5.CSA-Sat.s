%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:16 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    0
%              Number of atoms          :   47 (  47 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u74,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) )).

tff(u73,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) )).

tff(u72,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | m1_subset_1(X1,X0) ) )).

tff(u71,axiom,(
    v1_xboole_0(k1_xboole_0) )).

% (25671)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
tff(u70,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) )).

tff(u69,axiom,(
    ! [X1,X0,X2,X4] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | r1_orders_2(X0,X4,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u68,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u67,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u66,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) )).

tff(u65,axiom,(
    m1_subset_1(k1_xboole_0,k1_xboole_0) )).

tff(u64,axiom,(
    ! [X0] :
      ( m1_subset_1(X0,k1_xboole_0)
      | ~ v1_xboole_0(X0) ) )).

tff(u63,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u62,axiom,(
    ! [X1,X0] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u61,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u60,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u59,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u58,negated_conjecture,(
    v2_yellow_0(sK0) )).

tff(u57,negated_conjecture,
    ( ~ ~ r2_yellow_0(sK0,k1_xboole_0)
    | ~ r2_yellow_0(sK0,k1_xboole_0) )).

tff(u56,negated_conjecture,
    ( ~ ~ r1_yellow_0(sK0,u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,u1_struct_0(sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:54:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (25666)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.49  % (25682)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.49  % (25682)Refutation not found, incomplete strategy% (25682)------------------------------
% 0.21/0.49  % (25682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (25682)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (25682)Memory used [KB]: 1535
% 0.21/0.49  % (25682)Time elapsed: 0.001 s
% 0.21/0.49  % (25682)------------------------------
% 0.21/0.49  % (25682)------------------------------
% 0.21/0.49  % (25680)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.49  % (25676)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.49  % (25676)Refutation not found, incomplete strategy% (25676)------------------------------
% 0.21/0.49  % (25676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (25676)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.50  % (25672)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (25672)Refutation not found, incomplete strategy% (25672)------------------------------
% 0.21/0.50  % (25672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25677)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (25683)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.50  % (25672)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (25672)Memory used [KB]: 10490
% 0.21/0.50  % (25672)Time elapsed: 0.086 s
% 0.21/0.50  % (25672)------------------------------
% 0.21/0.50  % (25672)------------------------------
% 0.21/0.50  % (25683)Refutation not found, incomplete strategy% (25683)------------------------------
% 0.21/0.50  % (25683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25683)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (25683)Memory used [KB]: 1535
% 0.21/0.50  % (25683)Time elapsed: 0.050 s
% 0.21/0.50  % (25683)------------------------------
% 0.21/0.50  % (25683)------------------------------
% 0.21/0.50  % (25668)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (25680)# SZS output start Saturation.
% 0.21/0.50  tff(u74,axiom,
% 0.21/0.50      (![X0] : ((~v1_xboole_0(X0) | (k1_xboole_0 = X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u73,axiom,
% 0.21/0.50      (![X1, X0] : ((~v1_xboole_0(X0) | (X0 = X1) | ~v1_xboole_0(X1))))).
% 0.21/0.50  
% 0.21/0.50  tff(u72,axiom,
% 0.21/0.50      (![X1, X0] : ((~v1_xboole_0(X0) | ~v1_xboole_0(X1) | m1_subset_1(X1,X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u71,axiom,
% 0.21/0.50      v1_xboole_0(k1_xboole_0)).
% 0.21/0.50  
% 0.21/0.50  % (25671)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  tff(u70,axiom,
% 0.21/0.50      (![X1, X0] : ((~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u69,axiom,
% 0.21/0.50      (![X1, X0, X2, X4] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | r1_orders_2(X0,X4,X2) | ~l1_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u68,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,sK1(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u67,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u66,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK1(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u65,axiom,
% 0.21/0.50      m1_subset_1(k1_xboole_0,k1_xboole_0)).
% 0.21/0.50  
% 0.21/0.50  tff(u64,axiom,
% 0.21/0.50      (![X0] : ((m1_subset_1(X0,k1_xboole_0) | ~v1_xboole_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u63,axiom,
% 0.21/0.50      (![X1, X0] : ((~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u62,axiom,
% 0.21/0.50      (![X1, X0] : ((r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u61,negated_conjecture,
% 0.21/0.50      l1_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u60,negated_conjecture,
% 0.21/0.50      ~v2_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u59,negated_conjecture,
% 0.21/0.50      v5_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u58,negated_conjecture,
% 0.21/0.50      v2_yellow_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u57,negated_conjecture,
% 0.21/0.50      ((~~r2_yellow_0(sK0,k1_xboole_0)) | ~r2_yellow_0(sK0,k1_xboole_0))).
% 0.21/0.50  
% 0.21/0.50  tff(u56,negated_conjecture,
% 0.21/0.50      ((~~r1_yellow_0(sK0,u1_struct_0(sK0))) | ~r1_yellow_0(sK0,u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  % (25680)# SZS output end Saturation.
% 0.21/0.50  % (25680)------------------------------
% 0.21/0.50  % (25680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25680)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (25680)Memory used [KB]: 10618
% 0.21/0.50  % (25680)Time elapsed: 0.092 s
% 0.21/0.50  % (25680)------------------------------
% 0.21/0.50  % (25680)------------------------------
% 0.21/0.50  % (25674)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (25665)Success in time 0.136 s
%------------------------------------------------------------------------------
