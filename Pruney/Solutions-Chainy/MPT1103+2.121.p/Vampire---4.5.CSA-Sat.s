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
% DateTime   : Thu Dec  3 13:08:50 EST 2020

% Result     : CounterSatisfiable 3.24s
% Output     : Saturation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    0
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u93,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u92,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

tff(u91,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u90,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )).

tff(u89,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) )).

tff(u88,axiom,(
    ! [X2] : k3_xboole_0(X2,X2) = X2 )).

tff(u87,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k3_xboole_0(X0,X1))) )).

tff(u86,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u85,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

tff(u84,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u83,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) )).

tff(u82,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u81,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u80,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u79,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u78,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u77,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u76,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:37:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (21458)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (21466)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.34/0.56  % (21457)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.56  % (21457)Refutation not found, incomplete strategy% (21457)------------------------------
% 1.34/0.56  % (21457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (21457)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (21457)Memory used [KB]: 6268
% 1.34/0.56  % (21457)Time elapsed: 0.131 s
% 1.34/0.56  % (21457)------------------------------
% 1.34/0.56  % (21457)------------------------------
% 1.58/0.57  % (21476)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.58/0.57  % (21473)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.58/0.57  % (21465)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.58/0.57  % (21473)Refutation not found, incomplete strategy% (21473)------------------------------
% 1.58/0.57  % (21473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (21473)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.57  
% 1.58/0.57  % (21473)Memory used [KB]: 10746
% 1.58/0.57  % (21473)Time elapsed: 0.151 s
% 1.58/0.57  % (21473)------------------------------
% 1.58/0.57  % (21473)------------------------------
% 1.58/0.58  % (21459)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.58/0.58  % (21456)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.58/0.58  % (21468)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.58/0.58  % (21468)Refutation not found, incomplete strategy% (21468)------------------------------
% 1.58/0.58  % (21468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (21468)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.58  
% 1.58/0.58  % (21468)Memory used [KB]: 6140
% 1.58/0.58  % (21468)Time elapsed: 0.002 s
% 1.58/0.58  % (21468)------------------------------
% 1.58/0.58  % (21468)------------------------------
% 1.58/0.59  % (21476)Refutation not found, incomplete strategy% (21476)------------------------------
% 1.58/0.59  % (21476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.59  % (21476)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.59  
% 1.58/0.59  % (21476)Memory used [KB]: 1663
% 1.58/0.59  % (21476)Time elapsed: 0.096 s
% 1.58/0.59  % (21476)------------------------------
% 1.58/0.59  % (21476)------------------------------
% 1.58/0.59  % (21460)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.58/0.59  % (21460)Refutation not found, incomplete strategy% (21460)------------------------------
% 1.58/0.59  % (21460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.59  % (21460)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.60  
% 1.58/0.60  % (21460)Memory used [KB]: 6268
% 1.58/0.60  % (21460)Time elapsed: 0.128 s
% 1.58/0.60  % (21460)------------------------------
% 1.58/0.60  % (21460)------------------------------
% 1.58/0.60  % (21453)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.58/0.60  % (21453)Refutation not found, incomplete strategy% (21453)------------------------------
% 1.58/0.60  % (21453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.60  % (21453)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.60  
% 1.58/0.60  % (21453)Memory used [KB]: 1663
% 1.58/0.60  % (21453)Time elapsed: 0.171 s
% 1.58/0.60  % (21453)------------------------------
% 1.58/0.60  % (21453)------------------------------
% 1.58/0.60  % (21482)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.58/0.60  % (21481)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.58/0.61  % (21469)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.58/0.61  % (21474)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.58/0.61  % (21472)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.58/0.62  % (21454)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.58/0.62  % (21464)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.58/0.62  % (21467)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.58/0.62  % (21464)Refutation not found, incomplete strategy% (21464)------------------------------
% 1.58/0.62  % (21464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.62  % (21464)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.62  
% 1.58/0.62  % (21464)Memory used [KB]: 10618
% 1.58/0.62  % (21464)Time elapsed: 0.189 s
% 1.58/0.62  % (21464)------------------------------
% 1.58/0.62  % (21464)------------------------------
% 1.58/0.62  % (21480)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.58/0.62  % (21461)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.58/0.62  % (21455)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.58/0.63  % (21477)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.58/0.63  % (21455)Refutation not found, incomplete strategy% (21455)------------------------------
% 1.58/0.63  % (21455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.63  % (21455)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.63  
% 1.58/0.63  % (21455)Memory used [KB]: 10746
% 1.58/0.63  % (21455)Time elapsed: 0.200 s
% 1.58/0.63  % (21455)------------------------------
% 1.58/0.63  % (21455)------------------------------
% 1.58/0.64  % (21478)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.58/0.64  % (21471)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.58/0.64  % (21470)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.58/0.65  % (21461)Refutation not found, incomplete strategy% (21461)------------------------------
% 1.58/0.65  % (21461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.65  % (21461)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.65  
% 1.58/0.65  % (21461)Memory used [KB]: 10746
% 1.58/0.65  % (21461)Time elapsed: 0.200 s
% 1.58/0.65  % (21461)------------------------------
% 1.58/0.65  % (21461)------------------------------
% 2.17/0.65  % (21470)Refutation not found, incomplete strategy% (21470)------------------------------
% 2.17/0.65  % (21470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.65  % (21470)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.65  
% 2.17/0.65  % (21470)Memory used [KB]: 10618
% 2.17/0.65  % (21470)Time elapsed: 0.218 s
% 2.17/0.65  % (21470)------------------------------
% 2.17/0.65  % (21470)------------------------------
% 2.17/0.65  % (21479)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.17/0.65  % (21462)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.17/0.65  % (21462)Refutation not found, incomplete strategy% (21462)------------------------------
% 2.17/0.65  % (21462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.65  % (21462)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.65  
% 2.17/0.65  % (21462)Memory used [KB]: 10618
% 2.17/0.65  % (21462)Time elapsed: 0.220 s
% 2.17/0.65  % (21462)------------------------------
% 2.17/0.65  % (21462)------------------------------
% 2.17/0.65  % (21478)Refutation not found, incomplete strategy% (21478)------------------------------
% 2.17/0.65  % (21478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.65  % (21478)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.65  
% 2.17/0.65  % (21478)Memory used [KB]: 6268
% 2.17/0.65  % (21478)Time elapsed: 0.229 s
% 2.17/0.65  % (21478)------------------------------
% 2.17/0.65  % (21478)------------------------------
% 2.17/0.66  % (21475)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 2.17/0.66  % (21463)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 2.17/0.66  % (21463)Refutation not found, incomplete strategy% (21463)------------------------------
% 2.17/0.66  % (21463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.66  % (21463)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.66  
% 2.17/0.66  % (21463)Memory used [KB]: 10618
% 2.17/0.66  % (21463)Time elapsed: 0.238 s
% 2.17/0.66  % (21463)------------------------------
% 2.17/0.66  % (21463)------------------------------
% 2.17/0.67  % (21479)Refutation not found, incomplete strategy% (21479)------------------------------
% 2.17/0.67  % (21479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.67  % (21479)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.67  
% 2.17/0.67  % (21479)Memory used [KB]: 10746
% 2.17/0.67  % (21479)Time elapsed: 0.241 s
% 2.17/0.67  % (21479)------------------------------
% 2.17/0.67  % (21479)------------------------------
% 2.17/0.68  % (21475)Refutation not found, incomplete strategy% (21475)------------------------------
% 2.17/0.68  % (21475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.68  % (21475)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.68  
% 2.17/0.68  % (21475)Memory used [KB]: 10618
% 2.17/0.68  % (21475)Time elapsed: 0.224 s
% 2.17/0.68  % (21475)------------------------------
% 2.17/0.68  % (21475)------------------------------
% 2.61/0.75  % (21519)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.71/0.75  % (21519)Refutation not found, incomplete strategy% (21519)------------------------------
% 2.71/0.75  % (21519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.71/0.75  % (21519)Termination reason: Refutation not found, incomplete strategy
% 2.71/0.75  
% 2.71/0.75  % (21519)Memory used [KB]: 6268
% 2.71/0.75  % (21519)Time elapsed: 0.077 s
% 2.71/0.75  % (21519)------------------------------
% 2.71/0.75  % (21519)------------------------------
% 2.71/0.76  % (21520)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.02/0.83  % (21522)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 3.02/0.83  % (21521)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.02/0.84  % (21523)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 3.02/0.84  % (21458)Time limit reached!
% 3.02/0.84  % (21458)------------------------------
% 3.02/0.84  % (21458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.02/0.84  % (21524)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 3.02/0.86  % (21458)Termination reason: Time limit
% 3.02/0.86  % (21458)Termination phase: Saturation
% 3.02/0.86  
% 3.02/0.86  % (21458)Memory used [KB]: 8571
% 3.02/0.86  % (21458)Time elapsed: 0.400 s
% 3.02/0.86  % (21458)------------------------------
% 3.02/0.86  % (21458)------------------------------
% 3.24/0.87  % (21528)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 3.24/0.87  % SZS status CounterSatisfiable for theBenchmark
% 3.24/0.87  % (21454)# SZS output start Saturation.
% 3.24/0.87  tff(u93,negated_conjecture,
% 3.24/0.87      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 3.24/0.87  
% 3.24/0.87  tff(u92,axiom,
% 3.24/0.87      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)))))).
% 3.24/0.87  
% 3.24/0.87  tff(u91,axiom,
% 3.24/0.87      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 3.24/0.87  
% 3.24/0.87  tff(u90,axiom,
% 3.24/0.87      (![X1, X0] : ((k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)))))).
% 3.24/0.87  
% 3.24/0.87  tff(u89,axiom,
% 3.24/0.87      (![X1, X0] : ((k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)))))).
% 3.24/0.87  
% 3.24/0.87  tff(u88,axiom,
% 3.24/0.87      (![X2] : ((k3_xboole_0(X2,X2) = X2)))).
% 3.24/0.87  
% 3.24/0.87  tff(u87,axiom,
% 3.24/0.87      (![X1, X0] : ((k3_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k3_xboole_0(X0,X1))))))).
% 3.24/0.87  
% 3.24/0.87  tff(u86,axiom,
% 3.24/0.87      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 3.24/0.87  
% 3.24/0.87  tff(u85,axiom,
% 3.24/0.87      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 3.24/0.87  
% 3.24/0.87  tff(u84,axiom,
% 3.24/0.87      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 3.24/0.87  
% 3.24/0.87  tff(u83,axiom,
% 3.24/0.87      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,X0))))).
% 3.24/0.87  
% 3.24/0.87  tff(u82,negated_conjecture,
% 3.24/0.87      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 3.24/0.87  
% 3.24/0.87  tff(u81,negated_conjecture,
% 3.24/0.87      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)))))).
% 3.24/0.87  
% 3.24/0.87  tff(u80,negated_conjecture,
% 3.24/0.87      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 3.24/0.87  
% 3.24/0.87  tff(u79,axiom,
% 3.24/0.87      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 3.24/0.87  
% 3.24/0.87  tff(u78,axiom,
% 3.24/0.87      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 3.24/0.87  
% 3.24/0.87  tff(u77,negated_conjecture,
% 3.24/0.87      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 3.24/0.87  
% 3.24/0.87  tff(u76,negated_conjecture,
% 3.24/0.87      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 3.24/0.87  
% 3.24/0.87  % (21454)# SZS output end Saturation.
% 3.24/0.87  % (21454)------------------------------
% 3.24/0.87  % (21454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.24/0.87  % (21454)Termination reason: Satisfiable
% 3.24/0.87  
% 3.24/0.87  % (21454)Memory used [KB]: 6268
% 3.24/0.87  % (21454)Time elapsed: 0.424 s
% 3.24/0.87  % (21454)------------------------------
% 3.24/0.87  % (21454)------------------------------
% 3.24/0.87  % (21526)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 3.24/0.88  % (21452)Success in time 0.504 s
%------------------------------------------------------------------------------
