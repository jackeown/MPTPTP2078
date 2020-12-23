%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:12 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   45 (  45 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u110,negated_conjecture,
    ( ~ ( sK1 != k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    | sK1 != k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

tff(u109,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_enumset1(sK1,sK1,sK1)
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1) )).

tff(u108,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u107,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

tff(u106,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) )).

tff(u105,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) )).

tff(u104,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u103,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) ) )).

tff(u102,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r1_orders_2(X0,X1,X1) ) )).

tff(u101,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u100,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | v3_orders_2(sK0) )).

tff(u99,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | X1 = X2 ) )).

tff(u98,negated_conjecture,
    ( ~ ( sK1 != k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    | ! [X0] :
        ( ~ r1_orders_2(X0,k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),sK1)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(sK1,u1_struct_0(X0))
        | ~ m1_subset_1(k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),u1_struct_0(X0))
        | ~ v5_orders_2(X0)
        | ~ r1_orders_2(X0,sK1,k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ) )).

tff(u97,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | r1_orders_2(sK0,sK1,sK1) )).

tff(u96,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | v5_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:58:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.49  % (13336)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (13341)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (13334)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (13362)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.50  % (13334)Refutation not found, incomplete strategy% (13334)------------------------------
% 0.20/0.50  % (13334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (13334)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (13334)Memory used [KB]: 1663
% 0.20/0.50  % (13334)Time elapsed: 0.106 s
% 0.20/0.50  % (13334)------------------------------
% 0.20/0.50  % (13334)------------------------------
% 0.20/0.50  % (13354)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.50  % (13339)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (13338)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (13340)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (13337)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (13341)Refutation not found, incomplete strategy% (13341)------------------------------
% 0.20/0.51  % (13341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13346)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (13341)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (13341)Memory used [KB]: 6140
% 0.20/0.51  % (13341)Time elapsed: 0.109 s
% 0.20/0.51  % (13341)------------------------------
% 0.20/0.51  % (13341)------------------------------
% 0.20/0.51  % (13352)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (13360)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.51  % (13346)Refutation not found, incomplete strategy% (13346)------------------------------
% 0.20/0.51  % (13346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13347)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (13338)Refutation not found, incomplete strategy% (13338)------------------------------
% 0.20/0.51  % (13338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13356)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (13336)Refutation not found, incomplete strategy% (13336)------------------------------
% 0.20/0.51  % (13336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13349)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (13356)Refutation not found, incomplete strategy% (13356)------------------------------
% 0.20/0.51  % (13356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (13356)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (13356)Memory used [KB]: 10746
% 0.20/0.51  % (13356)Time elapsed: 0.096 s
% 0.20/0.51  % (13356)------------------------------
% 0.20/0.51  % (13356)------------------------------
% 0.20/0.51  % (13357)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (13348)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (13350)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.52  % (13350)# SZS output start Saturation.
% 0.20/0.52  tff(u110,negated_conjecture,
% 0.20/0.52      ((~(sK1 != k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) | (sK1 != k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))))).
% 0.20/0.52  
% 0.20/0.52  tff(u109,negated_conjecture,
% 0.20/0.52      ((~(k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1))) | (k6_domain_1(u1_struct_0(sK0),sK1) = k1_enumset1(sK1,sK1,sK1)))).
% 0.20/0.52  
% 0.20/0.52  tff(u108,negated_conjecture,
% 0.20/0.52      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  tff(u107,negated_conjecture,
% 0.20/0.52      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  tff(u106,axiom,
% 0.20/0.52      (![X0] : ((~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u105,axiom,
% 0.20/0.52      (![X0] : ((~l1_orders_2(X0) | l1_struct_0(X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u104,negated_conjecture,
% 0.20/0.52      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.20/0.52  
% 0.20/0.52  tff(u103,axiom,
% 0.20/0.52      (![X1, X0] : ((~m1_subset_1(X1,X0) | v1_xboole_0(X0) | (k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)))))).
% 0.20/0.52  
% 0.20/0.52  tff(u102,axiom,
% 0.20/0.52      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,X1,X1))))).
% 0.20/0.52  
% 0.20/0.52  tff(u101,negated_conjecture,
% 0.20/0.52      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 0.20/0.52  
% 0.20/0.52  tff(u100,negated_conjecture,
% 0.20/0.52      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 0.20/0.52  
% 0.20/0.52  tff(u99,axiom,
% 0.20/0.52      (![X1, X0, X2] : ((~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | (X1 = X2))))).
% 0.20/0.52  
% 0.20/0.52  tff(u98,negated_conjecture,
% 0.20/0.52      ((~(sK1 != k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) | (![X0] : ((~r1_orders_2(X0,k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),sK1) | ~l1_orders_2(X0) | ~m1_subset_1(sK1,u1_struct_0(X0)) | ~m1_subset_1(k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r1_orders_2(X0,sK1,k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))))))).
% 0.20/0.52  
% 0.20/0.52  tff(u97,negated_conjecture,
% 0.20/0.52      ((~r1_orders_2(sK0,sK1,sK1)) | r1_orders_2(sK0,sK1,sK1))).
% 0.20/0.52  
% 0.20/0.52  tff(u96,negated_conjecture,
% 0.20/0.52      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 0.20/0.52  
% 0.20/0.52  % (13350)# SZS output end Saturation.
% 0.20/0.52  % (13350)------------------------------
% 0.20/0.52  % (13350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13350)Termination reason: Satisfiable
% 0.20/0.52  
% 0.20/0.52  % (13350)Memory used [KB]: 10746
% 0.20/0.52  % (13350)Time elapsed: 0.129 s
% 0.20/0.52  % (13350)------------------------------
% 0.20/0.52  % (13350)------------------------------
% 0.20/0.52  % (13357)Refutation not found, incomplete strategy% (13357)------------------------------
% 0.20/0.52  % (13357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13357)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13339)Refutation not found, incomplete strategy% (13339)------------------------------
% 0.20/0.52  % (13339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13339)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13339)Memory used [KB]: 6268
% 0.20/0.52  % (13339)Time elapsed: 0.128 s
% 0.20/0.52  % (13339)------------------------------
% 0.20/0.52  % (13339)------------------------------
% 0.20/0.52  % (13357)Memory used [KB]: 1663
% 0.20/0.52  % (13357)Time elapsed: 0.115 s
% 0.20/0.52  % (13357)------------------------------
% 0.20/0.52  % (13357)------------------------------
% 0.20/0.52  % (13363)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (13354)Refutation not found, incomplete strategy% (13354)------------------------------
% 0.20/0.52  % (13354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13354)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13354)Memory used [KB]: 10746
% 0.20/0.52  % (13354)Time elapsed: 0.133 s
% 0.20/0.52  % (13354)------------------------------
% 0.20/0.52  % (13354)------------------------------
% 0.20/0.52  % (13353)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (13349)Refutation not found, incomplete strategy% (13349)------------------------------
% 0.20/0.52  % (13349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13349)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13349)Memory used [KB]: 6268
% 0.20/0.52  % (13349)Time elapsed: 0.123 s
% 0.20/0.52  % (13349)------------------------------
% 0.20/0.52  % (13349)------------------------------
% 0.20/0.52  % (13346)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13346)Memory used [KB]: 6140
% 0.20/0.52  % (13346)Time elapsed: 0.129 s
% 0.20/0.52  % (13346)------------------------------
% 0.20/0.52  % (13346)------------------------------
% 0.20/0.52  % (13363)Refutation not found, incomplete strategy% (13363)------------------------------
% 0.20/0.52  % (13363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13336)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13336)Memory used [KB]: 10618
% 0.20/0.52  % (13336)Time elapsed: 0.120 s
% 0.20/0.52  % (13336)------------------------------
% 0.20/0.52  % (13336)------------------------------
% 0.20/0.52  % (13335)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (13359)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (13358)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (13338)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13338)Memory used [KB]: 6268
% 0.20/0.52  % (13338)Time elapsed: 0.120 s
% 0.20/0.52  % (13338)------------------------------
% 0.20/0.52  % (13338)------------------------------
% 0.20/0.52  % (13355)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (13359)Refutation not found, incomplete strategy% (13359)------------------------------
% 0.20/0.52  % (13359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13361)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (13342)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (13351)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (13361)Refutation not found, incomplete strategy% (13361)------------------------------
% 0.20/0.52  % (13361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13342)Refutation not found, incomplete strategy% (13342)------------------------------
% 0.20/0.52  % (13342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13345)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (13361)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13361)Memory used [KB]: 6268
% 0.20/0.52  % (13361)Time elapsed: 0.131 s
% 0.20/0.52  % (13361)------------------------------
% 0.20/0.52  % (13361)------------------------------
% 0.20/0.52  % (13351)Refutation not found, incomplete strategy% (13351)------------------------------
% 0.20/0.52  % (13351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13358)Refutation not found, incomplete strategy% (13358)------------------------------
% 0.20/0.53  % (13358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13358)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13358)Memory used [KB]: 6268
% 0.20/0.53  % (13358)Time elapsed: 0.139 s
% 0.20/0.53  % (13358)------------------------------
% 0.20/0.53  % (13358)------------------------------
% 0.20/0.53  % (13343)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (13342)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13342)Memory used [KB]: 10618
% 0.20/0.53  % (13342)Time elapsed: 0.141 s
% 0.20/0.53  % (13342)------------------------------
% 0.20/0.53  % (13342)------------------------------
% 1.48/0.53  % (13333)Success in time 0.175 s
%------------------------------------------------------------------------------
