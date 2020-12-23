%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:49 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    0
%              Number of atoms          :  125 ( 125 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u246,negated_conjecture,
    ( ~ ( k3_yellow_0(sK0) != k4_yellow_0(sK0) )
    | k3_yellow_0(sK0) != k4_yellow_0(sK0) )).

tff(u245,negated_conjecture,
    ( k3_yellow_0(sK0) != k1_yellow_0(sK0,k1_xboole_0)
    | k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) )).

tff(u244,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) )).

tff(u243,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u242,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u241,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | v5_orders_2(sK0) )).

tff(u240,axiom,(
    ! [X1,X0,X4] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ l1_orders_2(X0) ) )).

tff(u239,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) )).

tff(u238,axiom,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u237,axiom,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u236,axiom,(
    ! [X1,X0,X2] :
      ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u235,negated_conjecture,
    ( ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) )).

tff(u234,negated_conjecture,
    ( ~ m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))
    | m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)) )).

tff(u233,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,X1)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) )).

tff(u232,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X2,sK1(X0,X1,X2))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u231,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r1_orders_2(sK0,k4_yellow_0(sK0),X0)
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | k4_yellow_0(sK0) = X0 )
    | ! [X0] :
        ( ~ r1_orders_2(sK0,k4_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_yellow_0(sK0) = X0 ) )).

tff(u230,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r1_orders_2(sK0,X0,k3_yellow_0(sK0))
          | k3_yellow_0(sK0) = X0
          | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ! [X0] :
        ( ~ r1_orders_2(sK0,X0,k3_yellow_0(sK0))
        | k3_yellow_0(sK0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u229,negated_conjecture,
    ( ~ ! [X0] :
          ( r1_orders_2(sK0,X0,k4_yellow_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ! [X0] :
        ( r1_orders_2(sK0,X0,k4_yellow_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u228,negated_conjecture,
    ( ~ ! [X0] :
          ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
          | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u227,axiom,(
    ! [X1,X0] :
      ( ~ v3_yellow_0(X1)
      | ~ l1_orders_2(X1)
      | r1_orders_2(X1,X0,k4_yellow_0(X1))
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) )).

tff(u226,negated_conjecture,
    ( ~ v3_yellow_0(sK0)
    | v3_yellow_0(sK0) )).

tff(u225,axiom,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u224,negated_conjecture,
    ( ~ v1_yellow_0(sK0)
    | v1_yellow_0(sK0) )).

tff(u223,axiom,(
    ! [X1,X0] :
      ( ~ v2_yellow_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,k4_yellow_0(X0))
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u222,axiom,(
    ! [X0] :
      ( v2_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u221,axiom,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u220,negated_conjecture,
    ( ~ r1_yellow_0(sK0,k1_xboole_0)
    | r1_yellow_0(sK0,k1_xboole_0) )).

tff(u219,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r2_lattice3(sK0,X0,k3_yellow_0(sK0))
          | k3_yellow_0(sK0) = k1_yellow_0(sK0,X0)
          | ~ r1_yellow_0(sK0,X0) )
    | ! [X0] :
        ( ~ r2_lattice3(sK0,X0,k3_yellow_0(sK0))
        | k3_yellow_0(sK0) = k1_yellow_0(sK0,X0)
        | ~ r1_yellow_0(sK0,X0) ) )).

tff(u218,axiom,(
    ! [X1,X0] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u217,axiom,(
    ! [X1,X0,X2] :
      ( r2_lattice3(X0,X1,sK1(X0,X1,X2))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u216,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u215,axiom,(
    ! [X0] :
      ( r2_yellow_0(X0,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u214,axiom,(
    ! [X1,X0] :
      ( r1_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) )).

tff(u213,negated_conjecture,
    ( ~ v7_struct_0(sK0)
    | v7_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:48:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (21633)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (21631)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (21630)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (21647)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (21639)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (21646)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (21632)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (21649)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.53  % (21641)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (21653)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (21645)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (21641)Refutation not found, incomplete strategy% (21641)------------------------------
% 0.22/0.53  % (21641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21641)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21641)Memory used [KB]: 6268
% 0.22/0.53  % (21641)Time elapsed: 0.112 s
% 0.22/0.53  % (21641)------------------------------
% 0.22/0.53  % (21641)------------------------------
% 0.22/0.53  % (21629)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (21630)Refutation not found, incomplete strategy% (21630)------------------------------
% 0.22/0.53  % (21630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21630)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21630)Memory used [KB]: 10618
% 0.22/0.53  % (21630)Time elapsed: 0.113 s
% 0.22/0.53  % (21630)------------------------------
% 0.22/0.53  % (21630)------------------------------
% 0.22/0.53  % (21634)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (21629)Refutation not found, incomplete strategy% (21629)------------------------------
% 0.22/0.53  % (21629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21629)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21629)Memory used [KB]: 10618
% 0.22/0.53  % (21629)Time elapsed: 0.087 s
% 0.22/0.53  % (21629)------------------------------
% 0.22/0.53  % (21629)------------------------------
% 0.22/0.53  % (21654)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.54  % (21632)Refutation not found, incomplete strategy% (21632)------------------------------
% 0.22/0.54  % (21632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21632)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21632)Memory used [KB]: 6140
% 0.22/0.54  % (21632)Time elapsed: 0.113 s
% 0.22/0.54  % (21632)------------------------------
% 0.22/0.54  % (21632)------------------------------
% 0.22/0.54  % (21640)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.54  % (21635)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (21640)Refutation not found, incomplete strategy% (21640)------------------------------
% 0.22/0.54  % (21640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21640)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21640)Memory used [KB]: 10618
% 0.22/0.54  % (21640)Time elapsed: 0.118 s
% 0.22/0.54  % (21640)------------------------------
% 0.22/0.54  % (21640)------------------------------
% 0.22/0.54  % (21635)Refutation not found, incomplete strategy% (21635)------------------------------
% 0.22/0.54  % (21635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21635)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21635)Memory used [KB]: 10618
% 0.22/0.54  % (21635)Time elapsed: 0.122 s
% 0.22/0.54  % (21635)------------------------------
% 0.22/0.54  % (21635)------------------------------
% 0.22/0.54  % (21637)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.54  % (21650)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  % (21644)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % (21649)Refutation not found, incomplete strategy% (21649)------------------------------
% 0.22/0.54  % (21649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (21649)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (21649)Memory used [KB]: 11129
% 0.22/0.54  % (21649)Time elapsed: 0.127 s
% 0.22/0.54  % (21649)------------------------------
% 0.22/0.54  % (21649)------------------------------
% 0.22/0.54  % (21638)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.45/0.55  % (21631)# SZS output start Saturation.
% 1.45/0.55  tff(u246,negated_conjecture,
% 1.45/0.55      ((~(k3_yellow_0(sK0) != k4_yellow_0(sK0))) | (k3_yellow_0(sK0) != k4_yellow_0(sK0)))).
% 1.45/0.55  
% 1.45/0.55  tff(u245,negated_conjecture,
% 1.45/0.55      ((~(k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0))) | (k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)))).
% 1.45/0.55  
% 1.45/0.55  tff(u244,axiom,
% 1.45/0.55      (![X0] : ((~l1_orders_2(X0) | (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)))))).
% 1.45/0.55  
% 1.45/0.55  tff(u243,negated_conjecture,
% 1.45/0.55      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 1.45/0.55  
% 1.45/0.55  tff(u242,axiom,
% 1.45/0.55      (![X0] : ((l1_struct_0(X0) | ~l1_orders_2(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u241,negated_conjecture,
% 1.45/0.55      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 1.45/0.55  
% 1.45/0.55  tff(u240,axiom,
% 1.45/0.55      (![X1, X0, X4] : ((~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~l1_orders_2(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u239,axiom,
% 1.45/0.55      (![X1, X0] : ((~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~l1_orders_2(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u238,axiom,
% 1.45/0.55      (![X0] : ((m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u237,axiom,
% 1.45/0.55      (![X0] : ((m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u236,axiom,
% 1.45/0.55      (![X1, X0, X2] : ((m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | (k1_yellow_0(X0,X1) = X2) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u235,negated_conjecture,
% 1.45/0.55      ((~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))) | m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)))).
% 1.45/0.55  
% 1.45/0.55  tff(u234,negated_conjecture,
% 1.45/0.55      ((~m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))) | m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)))).
% 1.45/0.55  
% 1.45/0.55  tff(u233,axiom,
% 1.45/0.55      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,X1) | (X1 = X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u232,axiom,
% 1.45/0.55      (![X1, X0, X2] : ((~r1_orders_2(X0,X2,sK1(X0,X1,X2)) | (k1_yellow_0(X0,X1) = X2) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u231,negated_conjecture,
% 1.45/0.55      ((~(![X0] : ((~r1_orders_2(sK0,k4_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k4_yellow_0(sK0) = X0))))) | (![X0] : ((~r1_orders_2(sK0,k4_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k4_yellow_0(sK0) = X0)))))).
% 1.45/0.55  
% 1.45/0.55  tff(u230,negated_conjecture,
% 1.45/0.55      ((~(![X0] : ((~r1_orders_2(sK0,X0,k3_yellow_0(sK0)) | (k3_yellow_0(sK0) = X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))))) | (![X0] : ((~r1_orders_2(sK0,X0,k3_yellow_0(sK0)) | (k3_yellow_0(sK0) = X0) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 1.45/0.55  
% 1.45/0.55  tff(u229,negated_conjecture,
% 1.45/0.55      ((~(![X0] : ((r1_orders_2(sK0,X0,k4_yellow_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)))))) | (![X0] : ((r1_orders_2(sK0,X0,k4_yellow_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 1.45/0.55  
% 1.45/0.55  tff(u228,negated_conjecture,
% 1.45/0.55      ((~(![X0] : ((r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)))))) | (![X0] : ((r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 1.45/0.55  
% 1.45/0.55  tff(u227,axiom,
% 1.45/0.55      (![X1, X0] : ((~v3_yellow_0(X1) | ~l1_orders_2(X1) | r1_orders_2(X1,X0,k4_yellow_0(X1)) | ~v5_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1)))))).
% 1.45/0.55  
% 1.45/0.55  tff(u226,negated_conjecture,
% 1.45/0.55      ((~v3_yellow_0(sK0)) | v3_yellow_0(sK0))).
% 1.45/0.55  
% 1.45/0.55  tff(u225,axiom,
% 1.45/0.55      (![X0] : ((v1_yellow_0(X0) | ~v3_yellow_0(X0) | ~l1_orders_2(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u224,negated_conjecture,
% 1.45/0.55      ((~v1_yellow_0(sK0)) | v1_yellow_0(sK0))).
% 1.45/0.55  
% 1.45/0.55  tff(u223,axiom,
% 1.45/0.55      (![X1, X0] : ((~v2_yellow_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,k4_yellow_0(X0)) | ~v5_orders_2(X0) | v2_struct_0(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u222,axiom,
% 1.45/0.55      (![X0] : ((v2_yellow_0(X0) | ~v3_yellow_0(X0) | ~l1_orders_2(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u221,axiom,
% 1.45/0.55      (![X0] : ((r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u220,negated_conjecture,
% 1.45/0.55      ((~r1_yellow_0(sK0,k1_xboole_0)) | r1_yellow_0(sK0,k1_xboole_0))).
% 1.45/0.55  
% 1.45/0.55  tff(u219,negated_conjecture,
% 1.45/0.55      ((~(![X0] : ((~r2_lattice3(sK0,X0,k3_yellow_0(sK0)) | (k3_yellow_0(sK0) = k1_yellow_0(sK0,X0)) | ~r1_yellow_0(sK0,X0))))) | (![X0] : ((~r2_lattice3(sK0,X0,k3_yellow_0(sK0)) | (k3_yellow_0(sK0) = k1_yellow_0(sK0,X0)) | ~r1_yellow_0(sK0,X0)))))).
% 1.45/0.55  
% 1.45/0.55  tff(u218,axiom,
% 1.45/0.55      (![X1, X0] : ((r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u217,axiom,
% 1.45/0.55      (![X1, X0, X2] : ((r2_lattice3(X0,X1,sK1(X0,X1,X2)) | (k1_yellow_0(X0,X1) = X2) | ~r2_lattice3(X0,X1,X2) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u216,negated_conjecture,
% 1.45/0.55      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 1.45/0.55  
% 1.45/0.55  tff(u215,axiom,
% 1.45/0.55      (![X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u214,axiom,
% 1.45/0.55      (![X1, X0] : ((r1_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))))).
% 1.45/0.55  
% 1.45/0.55  tff(u213,negated_conjecture,
% 1.45/0.55      ((~v7_struct_0(sK0)) | v7_struct_0(sK0))).
% 1.45/0.55  
% 1.45/0.55  % (21631)# SZS output end Saturation.
% 1.45/0.55  % (21631)------------------------------
% 1.45/0.55  % (21631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (21631)Termination reason: Satisfiable
% 1.45/0.55  
% 1.45/0.55  % (21631)Memory used [KB]: 6268
% 1.45/0.55  % (21631)Time elapsed: 0.104 s
% 1.45/0.55  % (21631)------------------------------
% 1.45/0.55  % (21631)------------------------------
% 1.45/0.55  % (21636)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.45/0.55  % (21628)Success in time 0.179 s
%------------------------------------------------------------------------------
