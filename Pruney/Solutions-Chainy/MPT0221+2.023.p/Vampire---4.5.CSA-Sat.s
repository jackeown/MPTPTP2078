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
% DateTime   : Thu Dec  3 12:35:48 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    3 (   3 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    0
%              Number of atoms          :    4 (   4 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u31,axiom,
    ( r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) )).

cnf(u30,axiom,
    ( ~ r1_xboole_0(X0,X0)
    | o_0_0_xboole_0 = X0 )).

cnf(u33,negated_conjecture,
    ( o_0_0_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:14:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (15844)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.50  % (15844)Refutation not found, incomplete strategy% (15844)------------------------------
% 0.21/0.50  % (15844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15844)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (15844)Memory used [KB]: 6140
% 0.21/0.50  % (15844)Time elapsed: 0.097 s
% 0.21/0.50  % (15844)------------------------------
% 0.21/0.50  % (15844)------------------------------
% 0.21/0.51  % (15833)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (15823)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (15823)Refutation not found, incomplete strategy% (15823)------------------------------
% 0.21/0.51  % (15823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15823)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15823)Memory used [KB]: 10618
% 0.21/0.51  % (15823)Time elapsed: 0.105 s
% 0.21/0.51  % (15823)------------------------------
% 0.21/0.51  % (15823)------------------------------
% 0.21/0.52  % (15822)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (15822)Refutation not found, incomplete strategy% (15822)------------------------------
% 0.21/0.52  % (15822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15822)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15822)Memory used [KB]: 10618
% 0.21/0.52  % (15822)Time elapsed: 0.107 s
% 0.21/0.52  % (15822)------------------------------
% 0.21/0.52  % (15822)------------------------------
% 0.21/0.52  % (15839)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (15839)Refutation not found, incomplete strategy% (15839)------------------------------
% 0.21/0.52  % (15839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15831)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (15821)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (15831)Refutation not found, incomplete strategy% (15831)------------------------------
% 0.21/0.52  % (15831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15831)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15831)Memory used [KB]: 10618
% 0.21/0.52  % (15831)Time elapsed: 0.124 s
% 0.21/0.52  % (15831)------------------------------
% 0.21/0.52  % (15831)------------------------------
% 0.21/0.53  % (15839)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15839)Memory used [KB]: 10618
% 0.21/0.53  % (15839)Time elapsed: 0.122 s
% 0.21/0.53  % (15839)------------------------------
% 0.21/0.53  % (15839)------------------------------
% 0.21/0.53  % (15838)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (15829)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (15826)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (15829)Refutation not found, incomplete strategy% (15829)------------------------------
% 0.21/0.53  % (15829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15829)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15829)Memory used [KB]: 10618
% 0.21/0.53  % (15829)Time elapsed: 0.115 s
% 0.21/0.53  % (15829)------------------------------
% 0.21/0.53  % (15829)------------------------------
% 0.21/0.53  % (15827)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (15835)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (15824)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (15835)Refutation not found, incomplete strategy% (15835)------------------------------
% 0.21/0.53  % (15835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15835)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15835)Memory used [KB]: 6140
% 0.21/0.53  % (15835)Time elapsed: 0.002 s
% 0.21/0.53  % (15835)------------------------------
% 0.21/0.53  % (15835)------------------------------
% 0.21/0.53  % (15827)Refutation not found, incomplete strategy% (15827)------------------------------
% 0.21/0.53  % (15827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15827)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15827)Memory used [KB]: 6140
% 0.21/0.53  % (15827)Time elapsed: 0.133 s
% 0.21/0.53  % (15827)------------------------------
% 0.21/0.53  % (15827)------------------------------
% 0.21/0.54  % (15824)Refutation not found, incomplete strategy% (15824)------------------------------
% 0.21/0.54  % (15824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15824)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15824)Memory used [KB]: 6140
% 0.21/0.54  % (15824)Time elapsed: 0.127 s
% 0.21/0.54  % (15824)------------------------------
% 0.21/0.54  % (15824)------------------------------
% 0.21/0.54  % (15841)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (15841)Refutation not found, incomplete strategy% (15841)------------------------------
% 0.21/0.54  % (15841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15841)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15841)Memory used [KB]: 1663
% 0.21/0.54  % (15841)Time elapsed: 0.101 s
% 0.21/0.54  % (15841)------------------------------
% 0.21/0.54  % (15841)------------------------------
% 0.21/0.54  % (15846)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (15846)Refutation not found, incomplete strategy% (15846)------------------------------
% 0.21/0.54  % (15846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15846)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15846)Memory used [KB]: 10618
% 0.21/0.54  % (15846)Time elapsed: 0.131 s
% 0.21/0.54  % (15846)------------------------------
% 0.21/0.54  % (15846)------------------------------
% 0.21/0.54  % (15843)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (15828)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (15832)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (15828)Refutation not found, incomplete strategy% (15828)------------------------------
% 0.21/0.54  % (15828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15828)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15828)Memory used [KB]: 10618
% 0.21/0.54  % (15828)Time elapsed: 0.103 s
% 0.21/0.54  % (15828)------------------------------
% 0.21/0.54  % (15828)------------------------------
% 0.21/0.54  % (15843)Refutation not found, incomplete strategy% (15843)------------------------------
% 0.21/0.54  % (15843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15843)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15832)Refutation not found, incomplete strategy% (15832)------------------------------
% 0.21/0.54  % (15832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15832)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15832)Memory used [KB]: 6140
% 0.21/0.54  % (15832)Time elapsed: 0.133 s
% 0.21/0.54  % (15832)------------------------------
% 0.21/0.54  % (15832)------------------------------
% 0.21/0.54  % (15843)Memory used [KB]: 1663
% 0.21/0.54  % (15843)Time elapsed: 0.119 s
% 0.21/0.54  % (15843)------------------------------
% 0.21/0.54  % (15843)------------------------------
% 0.21/0.54  % (15849)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (15847)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (15849)Refutation not found, incomplete strategy% (15849)------------------------------
% 0.21/0.54  % (15849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15849)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15849)Memory used [KB]: 1663
% 0.21/0.54  % (15849)Time elapsed: 0.142 s
% 0.21/0.54  % (15849)------------------------------
% 0.21/0.54  % (15849)------------------------------
% 0.21/0.54  % (15847)Refutation not found, incomplete strategy% (15847)------------------------------
% 0.21/0.54  % (15847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15847)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15847)Memory used [KB]: 6140
% 0.21/0.54  % (15847)Time elapsed: 0.138 s
% 0.21/0.54  % (15847)------------------------------
% 0.21/0.54  % (15847)------------------------------
% 0.21/0.55  % (15840)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (15825)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (15840)Refutation not found, incomplete strategy% (15840)------------------------------
% 0.21/0.55  % (15840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15840)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15840)Memory used [KB]: 10618
% 0.21/0.55  % (15840)Time elapsed: 0.140 s
% 0.21/0.55  % (15840)------------------------------
% 0.21/0.55  % (15840)------------------------------
% 0.21/0.55  % (15825)Refutation not found, incomplete strategy% (15825)------------------------------
% 0.21/0.55  % (15825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15825)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15825)Memory used [KB]: 6140
% 0.21/0.55  % (15825)Time elapsed: 0.130 s
% 0.21/0.55  % (15825)------------------------------
% 0.21/0.55  % (15825)------------------------------
% 0.21/0.55  % (15830)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (15830)Refutation not found, incomplete strategy% (15830)------------------------------
% 0.21/0.55  % (15830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15830)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15830)Memory used [KB]: 10618
% 0.21/0.55  % (15830)Time elapsed: 0.136 s
% 0.21/0.55  % (15830)------------------------------
% 0.21/0.55  % (15830)------------------------------
% 0.21/0.55  % (15836)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.55  % (15826)# SZS output start Saturation.
% 0.21/0.55  cnf(u31,axiom,
% 0.21/0.55      r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u30,axiom,
% 0.21/0.55      ~r1_xboole_0(X0,X0) | o_0_0_xboole_0 = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u33,negated_conjecture,
% 0.21/0.55      o_0_0_xboole_0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)).
% 0.21/0.55  
% 0.21/0.55  % (15826)# SZS output end Saturation.
% 0.21/0.55  % (15826)------------------------------
% 0.21/0.55  % (15826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15826)Termination reason: Satisfiable
% 0.21/0.55  
% 0.21/0.55  % (15826)Memory used [KB]: 6140
% 0.21/0.55  % (15826)Time elapsed: 0.134 s
% 0.21/0.55  % (15826)------------------------------
% 0.21/0.55  % (15826)------------------------------
% 0.21/0.55  % (15819)Success in time 0.179 s
%------------------------------------------------------------------------------
