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
% DateTime   : Thu Dec  3 13:22:49 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   33 (  33 expanded)
%              Depth                    :    0
%              Number of atoms          :  125 ( 125 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u243,negated_conjecture,
    ( k4_yellow_0(sK0) != k3_yellow_0(sK0)
    | k4_yellow_0(sK0) = k3_yellow_0(sK0) )).

tff(u242,negated_conjecture,
    ( k4_yellow_0(sK0) != k2_yellow_0(sK0,k1_xboole_0)
    | k4_yellow_0(sK0) = k2_yellow_0(sK0,k1_xboole_0) )).

tff(u241,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0) ) )).

tff(u240,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u239,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u238,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | v5_orders_2(sK0) )).

tff(u237,axiom,(
    ! [X1,X0,X4] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) )).

tff(u236,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) )).

tff(u235,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k4_yellow_0(sK0) = X0 )
    | ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_yellow_0(sK0) = X0 ) )).

tff(u234,axiom,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u233,axiom,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u232,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u231,negated_conjecture,
    ( ~ m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))
    | m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)) )).

tff(u230,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,X1)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u229,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u228,negated_conjecture,
    ( ~ ! [X0] :
          ( r1_orders_2(sK0,k4_yellow_0(sK0),X0)
          | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ! [X0] :
        ( r1_orders_2(sK0,k4_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u227,negated_conjecture,
    ( ~ ! [X0] :
          ( r1_orders_2(sK0,X0,k4_yellow_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ! [X0] :
        ( r1_orders_2(sK0,X0,k4_yellow_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u226,axiom,(
    ! [X1,X0] :
      ( ~ v3_yellow_0(X1)
      | ~ l1_orders_2(X1)
      | r1_orders_2(X1,k3_yellow_0(X1),X0)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) )).

tff(u225,negated_conjecture,
    ( ~ v3_yellow_0(sK0)
    | v3_yellow_0(sK0) )).

tff(u224,axiom,(
    ! [X1,X0] :
      ( ~ v1_yellow_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u223,axiom,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u222,axiom,(
    ! [X0] :
      ( v2_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u221,negated_conjecture,
    ( ~ v2_yellow_0(sK0)
    | v2_yellow_0(sK0) )).

tff(u220,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ r2_yellow_0(sK0,X0)
          | k2_yellow_0(sK0,X0) = X1
          | ~ r1_lattice3(sK0,X0,X1)
          | k4_yellow_0(sK0) = sK1(sK0,X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ! [X1,X0] :
        ( ~ r2_yellow_0(sK0,X0)
        | k2_yellow_0(sK0,X0) = X1
        | ~ r1_lattice3(sK0,X0,X1)
        | k4_yellow_0(sK0) = sK1(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) )).

tff(u219,axiom,(
    ! [X0] :
      ( r2_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u218,negated_conjecture,
    ( ~ r2_yellow_0(sK0,k1_xboole_0)
    | r2_yellow_0(sK0,k1_xboole_0) )).

tff(u217,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r1_lattice3(sK0,X0,k4_yellow_0(sK0))
          | k4_yellow_0(sK0) = k2_yellow_0(sK0,X0)
          | ~ r2_yellow_0(sK0,X0) )
    | ! [X0] :
        ( ~ r1_lattice3(sK0,X0,k4_yellow_0(sK0))
        | k4_yellow_0(sK0) = k2_yellow_0(sK0,X0)
        | ~ r2_yellow_0(sK0,X0) ) )).

tff(u216,axiom,(
    ! [X1,X0] :
      ( r1_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u215,axiom,(
    ! [X1,X0,X2] :
      ( r1_lattice3(X0,X1,sK1(X0,X1,X2))
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u214,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u213,axiom,(
    ! [X0] :
      ( r1_yellow_0(X0,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u212,axiom,(
    ! [X1,X0] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u211,negated_conjecture,
    ( ~ ~ v7_struct_0(sK0)
    | ~ v7_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:29:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (1133)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (1128)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (1129)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (1127)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (1127)Refutation not found, incomplete strategy% (1127)------------------------------
% 0.21/0.54  % (1127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1127)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1127)Memory used [KB]: 6140
% 0.21/0.54  % (1127)Time elapsed: 0.110 s
% 0.21/0.54  % (1127)------------------------------
% 0.21/0.54  % (1127)------------------------------
% 0.21/0.54  % (1132)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (1125)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (1124)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.55  % (1124)Refutation not found, incomplete strategy% (1124)------------------------------
% 0.21/0.55  % (1124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1124)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1124)Memory used [KB]: 10618
% 0.21/0.55  % (1124)Time elapsed: 0.121 s
% 0.21/0.55  % (1124)------------------------------
% 0.21/0.55  % (1124)------------------------------
% 0.21/0.55  % (1148)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.55  % (1142)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.55  % (1137)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (1126)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.56  % (1147)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.56  % (1137)Refutation not found, incomplete strategy% (1137)------------------------------
% 0.21/0.56  % (1137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (1137)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (1137)Memory used [KB]: 6140
% 0.21/0.56  % (1137)Time elapsed: 0.130 s
% 0.21/0.56  % (1137)------------------------------
% 0.21/0.56  % (1137)------------------------------
% 0.21/0.56  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.56  % (1126)# SZS output start Saturation.
% 0.21/0.56  tff(u243,negated_conjecture,
% 0.21/0.56      ((~(k4_yellow_0(sK0) = k3_yellow_0(sK0))) | (k4_yellow_0(sK0) = k3_yellow_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u242,negated_conjecture,
% 0.21/0.56      ((~(k4_yellow_0(sK0) = k2_yellow_0(sK0,k1_xboole_0))) | (k4_yellow_0(sK0) = k2_yellow_0(sK0,k1_xboole_0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u241,axiom,
% 0.21/0.56      (![X0] : ((~l1_orders_2(X0) | (k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u240,negated_conjecture,
% 0.21/0.56      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.21/0.56  
% 0.21/0.56  tff(u239,axiom,
% 0.21/0.56      (![X0] : ((l1_struct_0(X0) | ~l1_orders_2(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u238,negated_conjecture,
% 0.21/0.56      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 0.21/0.56  
% 0.21/0.56  tff(u237,axiom,
% 0.21/0.56      (![X1, X0, X4] : ((~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) | ~l1_orders_2(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u236,axiom,
% 0.21/0.56      (![X1, X0] : ((~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) | ~l1_orders_2(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u235,negated_conjecture,
% 0.21/0.56      ((~(![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k4_yellow_0(sK0) = X0))))) | (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k4_yellow_0(sK0) = X0)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u234,axiom,
% 0.21/0.56      (![X0] : ((m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u233,axiom,
% 0.21/0.56      (![X0] : ((m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u232,axiom,
% 0.21/0.56      (![X1, X0, X2] : ((m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | (k2_yellow_0(X0,X1) = X2) | ~r1_lattice3(X0,X1,X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u231,negated_conjecture,
% 0.21/0.56      ((~m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))) | m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  tff(u230,axiom,
% 0.21/0.56      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,X1) | (X1 = X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u229,axiom,
% 0.21/0.56      (![X1, X0, X2] : ((~r1_orders_2(X0,sK1(X0,X1,X2),X2) | (k2_yellow_0(X0,X1) = X2) | ~r1_lattice3(X0,X1,X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u228,negated_conjecture,
% 0.21/0.56      ((~(![X0] : ((r1_orders_2(sK0,k4_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))))) | (![X0] : ((r1_orders_2(sK0,k4_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 0.21/0.56  
% 0.21/0.56  tff(u227,negated_conjecture,
% 0.21/0.56      ((~(![X0] : ((r1_orders_2(sK0,X0,k4_yellow_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)))))) | (![X0] : ((r1_orders_2(sK0,X0,k4_yellow_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 0.21/0.56  
% 0.21/0.56  tff(u226,axiom,
% 0.21/0.56      (![X1, X0] : ((~v3_yellow_0(X1) | ~l1_orders_2(X1) | r1_orders_2(X1,k3_yellow_0(X1),X0) | ~v5_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u225,negated_conjecture,
% 0.21/0.56      ((~v3_yellow_0(sK0)) | v3_yellow_0(sK0))).
% 0.21/0.56  
% 0.21/0.56  tff(u224,axiom,
% 0.21/0.56      (![X1, X0] : ((~v1_yellow_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,k3_yellow_0(X0),X1) | ~v5_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u223,axiom,
% 0.21/0.56      (![X0] : ((v1_yellow_0(X0) | ~v3_yellow_0(X0) | ~l1_orders_2(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u222,axiom,
% 0.21/0.56      (![X0] : ((v2_yellow_0(X0) | ~v3_yellow_0(X0) | ~l1_orders_2(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u221,negated_conjecture,
% 0.21/0.56      ((~v2_yellow_0(sK0)) | v2_yellow_0(sK0))).
% 0.21/0.56  
% 0.21/0.56  tff(u220,negated_conjecture,
% 0.21/0.56      ((~(![X1, X0] : ((~r2_yellow_0(sK0,X0) | (k2_yellow_0(sK0,X0) = X1) | ~r1_lattice3(sK0,X0,X1) | (k4_yellow_0(sK0) = sK1(sK0,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)))))) | (![X1, X0] : ((~r2_yellow_0(sK0,X0) | (k2_yellow_0(sK0,X0) = X1) | ~r1_lattice3(sK0,X0,X1) | (k4_yellow_0(sK0) = sK1(sK0,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0))))))).
% 0.21/0.56  
% 0.21/0.56  tff(u219,axiom,
% 0.21/0.56      (![X0] : ((r2_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v2_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u218,negated_conjecture,
% 0.21/0.56      ((~r2_yellow_0(sK0,k1_xboole_0)) | r2_yellow_0(sK0,k1_xboole_0))).
% 0.21/0.56  
% 0.21/0.56  tff(u217,negated_conjecture,
% 0.21/0.56      ((~(![X0] : ((~r1_lattice3(sK0,X0,k4_yellow_0(sK0)) | (k4_yellow_0(sK0) = k2_yellow_0(sK0,X0)) | ~r2_yellow_0(sK0,X0))))) | (![X0] : ((~r1_lattice3(sK0,X0,k4_yellow_0(sK0)) | (k4_yellow_0(sK0) = k2_yellow_0(sK0,X0)) | ~r2_yellow_0(sK0,X0)))))).
% 0.21/0.56  
% 0.21/0.56  tff(u216,axiom,
% 0.21/0.56      (![X1, X0] : ((r1_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u215,axiom,
% 0.21/0.56      (![X1, X0, X2] : ((r1_lattice3(X0,X1,sK1(X0,X1,X2)) | (k2_yellow_0(X0,X1) = X2) | ~r1_lattice3(X0,X1,X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u214,negated_conjecture,
% 0.21/0.56      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.21/0.56  
% 0.21/0.56  tff(u213,axiom,
% 0.21/0.56      (![X0] : ((r1_yellow_0(X0,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u212,axiom,
% 0.21/0.56      (![X1, X0] : ((r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 0.21/0.56  
% 0.21/0.56  tff(u211,negated_conjecture,
% 0.21/0.56      ((~~v7_struct_0(sK0)) | ~v7_struct_0(sK0))).
% 0.21/0.56  
% 0.21/0.56  % (1126)# SZS output end Saturation.
% 0.21/0.56  % (1126)------------------------------
% 0.21/0.56  % (1126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (1126)Termination reason: Satisfiable
% 0.21/0.56  
% 0.21/0.56  % (1126)Memory used [KB]: 6268
% 0.21/0.56  % (1126)Time elapsed: 0.130 s
% 0.21/0.56  % (1126)------------------------------
% 0.21/0.56  % (1126)------------------------------
% 0.21/0.56  % (1145)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.56  % (1123)Success in time 0.199 s
%------------------------------------------------------------------------------
