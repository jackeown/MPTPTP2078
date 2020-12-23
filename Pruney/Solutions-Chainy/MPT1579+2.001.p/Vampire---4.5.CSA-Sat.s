%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:21 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :    2 (   2 expanded)
%              Number of leaves         :    2 (   2 expanded)
%              Depth                    :    0
%              Number of atoms          :    2 (   2 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    2 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u18,negated_conjecture,(
    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK2)) )).

tff(u17,negated_conjecture,(
    u1_struct_0(sK1) = u1_struct_0(sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (32367)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.47  % (32367)Refutation not found, incomplete strategy% (32367)------------------------------
% 0.20/0.47  % (32367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (32367)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (32367)Memory used [KB]: 10618
% 0.20/0.47  % (32367)Time elapsed: 0.063 s
% 0.20/0.47  % (32367)------------------------------
% 0.20/0.47  % (32367)------------------------------
% 0.20/0.48  % (32375)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.50  % (32359)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (32361)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (32361)Refutation not found, incomplete strategy% (32361)------------------------------
% 0.20/0.50  % (32361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (32361)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (32361)Memory used [KB]: 6140
% 0.20/0.50  % (32361)Time elapsed: 0.101 s
% 0.20/0.50  % (32361)------------------------------
% 0.20/0.50  % (32361)------------------------------
% 0.20/0.51  % (32357)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (32360)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (32357)Refutation not found, incomplete strategy% (32357)------------------------------
% 0.20/0.51  % (32357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (32357)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (32357)Memory used [KB]: 1663
% 0.20/0.51  % (32357)Time elapsed: 0.106 s
% 0.20/0.51  % (32357)------------------------------
% 0.20/0.51  % (32357)------------------------------
% 0.20/0.51  % (32385)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (32370)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (32364)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (32377)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (32377)Refutation not found, incomplete strategy% (32377)------------------------------
% 0.20/0.52  % (32377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32377)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (32377)Memory used [KB]: 10618
% 0.20/0.52  % (32377)Time elapsed: 0.125 s
% 0.20/0.52  % (32377)------------------------------
% 0.20/0.52  % (32377)------------------------------
% 0.20/0.52  % (32366)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (32380)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (32380)Refutation not found, incomplete strategy% (32380)------------------------------
% 0.20/0.52  % (32380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32380)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (32380)Memory used [KB]: 1663
% 0.20/0.52  % (32380)Time elapsed: 0.120 s
% 0.20/0.52  % (32380)------------------------------
% 0.20/0.52  % (32380)------------------------------
% 0.20/0.52  % (32358)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (32379)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (32369)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (32369)Refutation not found, incomplete strategy% (32369)------------------------------
% 0.20/0.52  % (32369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32369)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (32369)Memory used [KB]: 6140
% 0.20/0.52  % (32369)Time elapsed: 0.127 s
% 0.20/0.52  % (32369)------------------------------
% 0.20/0.52  % (32369)------------------------------
% 0.20/0.52  % (32379)Refutation not found, incomplete strategy% (32379)------------------------------
% 0.20/0.52  % (32379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32382)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (32359)Refutation not found, incomplete strategy% (32359)------------------------------
% 0.20/0.52  % (32359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32359)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (32359)Memory used [KB]: 10618
% 0.20/0.52  % (32359)Time elapsed: 0.118 s
% 0.20/0.52  % (32359)------------------------------
% 0.20/0.52  % (32359)------------------------------
% 0.20/0.52  % (32368)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (32386)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (32383)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (32374)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (32383)Refutation not found, incomplete strategy% (32383)------------------------------
% 0.20/0.52  % (32383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32383)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (32383)Memory used [KB]: 10618
% 0.20/0.52  % (32383)Time elapsed: 0.122 s
% 0.20/0.52  % (32383)------------------------------
% 0.20/0.52  % (32383)------------------------------
% 0.20/0.53  % (32371)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (32382)Refutation not found, incomplete strategy% (32382)------------------------------
% 0.20/0.53  % (32382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (32384)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (32366)Refutation not found, incomplete strategy% (32366)------------------------------
% 0.20/0.53  % (32366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (32382)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (32382)Memory used [KB]: 6140
% 0.20/0.53  % (32382)Time elapsed: 0.122 s
% 0.20/0.53  % (32382)------------------------------
% 0.20/0.53  % (32382)------------------------------
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (32360)# SZS output start Saturation.
% 0.20/0.53  tff(u18,negated_conjecture,
% 0.20/0.53      (g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK2)))).
% 0.20/0.53  
% 0.20/0.53  tff(u17,negated_conjecture,
% 0.20/0.53      (u1_struct_0(sK1) = u1_struct_0(sK2))).
% 0.20/0.53  
% 0.20/0.53  % (32360)# SZS output end Saturation.
% 0.20/0.53  % (32360)------------------------------
% 0.20/0.53  % (32360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (32360)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (32360)Memory used [KB]: 10618
% 0.20/0.53  % (32360)Time elapsed: 0.129 s
% 0.20/0.53  % (32360)------------------------------
% 0.20/0.53  % (32360)------------------------------
% 0.20/0.53  % (32366)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (32366)Memory used [KB]: 10618
% 0.20/0.53  % (32366)Time elapsed: 0.133 s
% 0.20/0.53  % (32366)------------------------------
% 0.20/0.53  % (32366)------------------------------
% 0.20/0.53  % (32378)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (32356)Success in time 0.167 s
%------------------------------------------------------------------------------
