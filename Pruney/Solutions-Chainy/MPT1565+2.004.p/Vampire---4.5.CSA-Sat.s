%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:15 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   47 (  47 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u78,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u77,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

tff(u76,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u75,axiom,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) )).

tff(u74,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) )).

tff(u73,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) )).

tff(u72,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) )).

tff(u71,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u70,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u69,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u68,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u67,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u66,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | v5_orders_2(sK0) )).

tff(u65,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) )).

tff(u64,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | X1 = X2 ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:15:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (10009)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (10001)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (10025)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.51  % (9997)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (9998)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (9998)Refutation not found, incomplete strategy% (9998)------------------------------
% 0.22/0.51  % (9998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9998)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9998)Memory used [KB]: 10618
% 0.22/0.51  % (9998)Time elapsed: 0.109 s
% 0.22/0.51  % (9998)------------------------------
% 0.22/0.51  % (9998)------------------------------
% 0.22/0.52  % (10016)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (10003)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (10001)Refutation not found, incomplete strategy% (10001)------------------------------
% 0.22/0.52  % (10001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10001)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10001)Memory used [KB]: 6140
% 0.22/0.52  % (10001)Time elapsed: 0.103 s
% 0.22/0.52  % (10001)------------------------------
% 0.22/0.52  % (10001)------------------------------
% 0.22/0.52  % (10008)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (10017)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (10017)Refutation not found, incomplete strategy% (10017)------------------------------
% 0.22/0.53  % (10017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10025)Refutation not found, incomplete strategy% (10025)------------------------------
% 0.22/0.53  % (10025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10017)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (10017)Memory used [KB]: 1663
% 0.22/0.53  % (10017)Time elapsed: 0.115 s
% 0.22/0.53  % (10017)------------------------------
% 0.22/0.53  % (10017)------------------------------
% 0.22/0.53  % (10016)Refutation not found, incomplete strategy% (10016)------------------------------
% 0.22/0.53  % (10016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10016)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (10016)Memory used [KB]: 10746
% 0.22/0.53  % (10016)Time elapsed: 0.116 s
% 0.22/0.53  % (10016)------------------------------
% 0.22/0.53  % (10016)------------------------------
% 0.22/0.53  % (10025)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (10025)Memory used [KB]: 1663
% 0.22/0.53  % (10025)Time elapsed: 0.116 s
% 0.22/0.53  % (10025)------------------------------
% 0.22/0.53  % (10025)------------------------------
% 0.22/0.53  % (9999)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (10010)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (10005)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (10000)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (10000)Refutation not found, incomplete strategy% (10000)------------------------------
% 0.22/0.54  % (10000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9996)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (10022)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (10003)Refutation not found, incomplete strategy% (10003)------------------------------
% 0.22/0.54  % (10003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10003)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10003)Memory used [KB]: 6140
% 0.22/0.54  % (10003)Time elapsed: 0.125 s
% 0.22/0.54  % (10003)------------------------------
% 0.22/0.54  % (10003)------------------------------
% 0.22/0.54  % (10014)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (9996)Refutation not found, incomplete strategy% (9996)------------------------------
% 0.22/0.54  % (9996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9996)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9996)Memory used [KB]: 1663
% 0.22/0.54  % (9996)Time elapsed: 0.128 s
% 0.22/0.54  % (9996)------------------------------
% 0.22/0.54  % (9996)------------------------------
% 0.22/0.54  % (10005)Refutation not found, incomplete strategy% (10005)------------------------------
% 0.22/0.54  % (10005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10023)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (10019)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (10002)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (10013)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (10015)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (10000)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10000)Memory used [KB]: 6140
% 0.22/0.54  % (10000)Time elapsed: 0.127 s
% 0.22/0.54  % (10000)------------------------------
% 0.22/0.54  % (10000)------------------------------
% 0.22/0.54  % (10021)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (10012)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (10021)Refutation not found, incomplete strategy% (10021)------------------------------
% 0.22/0.54  % (10021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10021)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10021)Memory used [KB]: 6268
% 0.22/0.54  % (10021)Time elapsed: 0.136 s
% 0.22/0.54  % (10021)------------------------------
% 0.22/0.54  % (10021)------------------------------
% 0.22/0.54  % (10011)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.54  % (10018)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (10015)Refutation not found, incomplete strategy% (10015)------------------------------
% 0.22/0.55  % (10015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10007)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (10013)Refutation not found, incomplete strategy% (10013)------------------------------
% 0.22/0.55  % (10013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10018)Refutation not found, incomplete strategy% (10018)------------------------------
% 0.22/0.55  % (10018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10018)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10018)Memory used [KB]: 10618
% 0.22/0.55  % (10018)Time elapsed: 0.101 s
% 0.22/0.55  % (10018)------------------------------
% 0.22/0.55  % (10018)------------------------------
% 0.22/0.55  % (10007)Refutation not found, incomplete strategy% (10007)------------------------------
% 0.22/0.55  % (10007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10024)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (10022)Refutation not found, incomplete strategy% (10022)------------------------------
% 0.22/0.55  % (10022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10022)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10022)Memory used [KB]: 10618
% 0.22/0.55  % (10022)Time elapsed: 0.140 s
% 0.22/0.55  % (10022)------------------------------
% 0.22/0.55  % (10022)------------------------------
% 0.22/0.55  % (10005)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  % (10023)Refutation not found, incomplete strategy% (10023)------------------------------
% 0.22/0.55  % (10023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10023)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10023)Memory used [KB]: 6268
% 0.22/0.55  % (10023)Time elapsed: 0.140 s
% 0.22/0.55  % (10023)------------------------------
% 0.22/0.55  % (10023)------------------------------
% 0.22/0.55  
% 0.22/0.55  % (10005)Memory used [KB]: 10618
% 0.22/0.55  % (10005)Time elapsed: 0.134 s
% 0.22/0.55  % (10005)------------------------------
% 0.22/0.55  % (10005)------------------------------
% 0.22/0.55  % (10004)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (10015)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10015)Memory used [KB]: 10746
% 0.22/0.55  % (10015)Time elapsed: 0.141 s
% 0.22/0.55  % (10015)------------------------------
% 0.22/0.55  % (10015)------------------------------
% 0.22/0.55  % (10020)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (10004)Refutation not found, incomplete strategy% (10004)------------------------------
% 0.22/0.55  % (10004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10004)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10004)Memory used [KB]: 10618
% 0.22/0.55  % (10004)Time elapsed: 0.140 s
% 0.22/0.55  % (10004)------------------------------
% 0.22/0.55  % (10004)------------------------------
% 0.22/0.55  % (10007)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10007)Memory used [KB]: 10618
% 0.22/0.55  % (10007)Time elapsed: 0.141 s
% 0.22/0.55  % (10007)------------------------------
% 0.22/0.55  % (10007)------------------------------
% 0.22/0.55  % (10020)Refutation not found, incomplete strategy% (10020)------------------------------
% 0.22/0.55  % (10020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10013)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10013)Memory used [KB]: 10618
% 0.22/0.55  % (10013)Time elapsed: 0.143 s
% 0.22/0.55  % (10013)------------------------------
% 0.22/0.55  % (10013)------------------------------
% 0.22/0.55  % (10012)# SZS output start Saturation.
% 0.22/0.55  tff(u78,axiom,
% 0.22/0.55      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u77,axiom,
% 0.22/0.55      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 0.22/0.55  
% 0.22/0.55  tff(u76,axiom,
% 0.22/0.55      (![X1, X0] : ((~r2_hidden(X1,X0) | ~v1_xboole_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u75,axiom,
% 0.22/0.55      (![X0] : ((r2_hidden(sK2(X0),X0) | v1_xboole_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u74,axiom,
% 0.22/0.55      (![X1, X0] : ((~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))))).
% 0.22/0.55  
% 0.22/0.55  tff(u73,axiom,
% 0.22/0.55      (![X1, X3, X0, X2] : ((~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2))))).
% 0.22/0.55  
% 0.22/0.55  tff(u72,axiom,
% 0.22/0.55      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2))))).
% 0.22/0.55  
% 0.22/0.55  tff(u71,axiom,
% 0.22/0.55      (![X1, X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK1(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2))))).
% 0.22/0.55  
% 0.22/0.55  tff(u70,negated_conjecture,
% 0.22/0.55      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.22/0.55  
% 0.22/0.55  tff(u69,negated_conjecture,
% 0.22/0.55      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.22/0.55  
% 0.22/0.55  tff(u68,axiom,
% 0.22/0.55      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.22/0.55  
% 0.22/0.55  tff(u67,negated_conjecture,
% 0.22/0.55      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.22/0.55  
% 0.22/0.55  tff(u66,negated_conjecture,
% 0.22/0.55      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 0.22/0.55  
% 0.22/0.55  tff(u65,axiom,
% 0.22/0.55      (![X1, X0, X2] : ((~r1_orders_2(X0,sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2))))).
% 0.22/0.55  
% 0.22/0.55  tff(u64,axiom,
% 0.22/0.55      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | (X1 = X2))))).
% 0.22/0.55  
% 0.22/0.55  % (10012)# SZS output end Saturation.
% 0.22/0.55  % (10012)------------------------------
% 0.22/0.55  % (10012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10012)Termination reason: Satisfiable
% 0.22/0.55  
% 0.22/0.55  % (10012)Memory used [KB]: 10618
% 0.22/0.55  % (10012)Time elapsed: 0.142 s
% 0.22/0.55  % (10012)------------------------------
% 0.22/0.55  % (10012)------------------------------
% 0.22/0.56  % (9995)Success in time 0.184 s
%------------------------------------------------------------------------------
