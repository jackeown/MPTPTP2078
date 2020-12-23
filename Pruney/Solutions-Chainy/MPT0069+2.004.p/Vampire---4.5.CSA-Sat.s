%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:25 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    2 (   2 expanded)
%              Number of leaves         :    2 (   2 expanded)
%              Depth                    :    0
%              Number of atoms          :    2 (   2 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u10,negated_conjecture,
    ( r2_xboole_0(sK0,k1_xboole_0) )).

cnf(u12,axiom,
    ( ~ r2_xboole_0(X1,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:27:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (22124)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (22124)Refutation not found, incomplete strategy% (22124)------------------------------
% 0.21/0.48  % (22124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22124)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (22124)Memory used [KB]: 10490
% 0.21/0.48  % (22124)Time elapsed: 0.007 s
% 0.21/0.48  % (22124)------------------------------
% 0.21/0.48  % (22124)------------------------------
% 0.21/0.48  % (22116)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (22116)Refutation not found, incomplete strategy% (22116)------------------------------
% 0.21/0.48  % (22116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22116)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (22116)Memory used [KB]: 10490
% 0.21/0.48  % (22116)Time elapsed: 0.005 s
% 0.21/0.48  % (22116)------------------------------
% 0.21/0.48  % (22116)------------------------------
% 0.21/0.48  % (22112)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (22119)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (22112)Refutation not found, incomplete strategy% (22112)------------------------------
% 0.21/0.48  % (22112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22112)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (22112)Memory used [KB]: 10490
% 0.21/0.48  % (22112)Time elapsed: 0.072 s
% 0.21/0.48  % (22112)------------------------------
% 0.21/0.48  % (22112)------------------------------
% 0.21/0.49  % (22119)Refutation not found, incomplete strategy% (22119)------------------------------
% 0.21/0.49  % (22119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (22119)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (22119)Memory used [KB]: 10490
% 0.21/0.49  % (22119)Time elapsed: 0.071 s
% 0.21/0.49  % (22119)------------------------------
% 0.21/0.49  % (22119)------------------------------
% 0.21/0.49  % (22130)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (22118)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (22114)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (22114)Refutation not found, incomplete strategy% (22114)------------------------------
% 0.21/0.50  % (22114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22114)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (22114)Memory used [KB]: 1535
% 0.21/0.50  % (22114)Time elapsed: 0.081 s
% 0.21/0.50  % (22114)------------------------------
% 0.21/0.50  % (22114)------------------------------
% 0.21/0.50  % (22128)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (22117)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (22128)Refutation not found, incomplete strategy% (22128)------------------------------
% 0.21/0.50  % (22128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22128)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (22128)Memory used [KB]: 1535
% 0.21/0.50  % (22128)Time elapsed: 0.090 s
% 0.21/0.50  % (22128)------------------------------
% 0.21/0.50  % (22128)------------------------------
% 0.21/0.50  % (22125)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (22122)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (22122)Refutation not found, incomplete strategy% (22122)------------------------------
% 0.21/0.50  % (22122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22122)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (22110)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (22122)Memory used [KB]: 6012
% 0.21/0.50  % (22122)Time elapsed: 0.001 s
% 0.21/0.50  % (22122)------------------------------
% 0.21/0.50  % (22122)------------------------------
% 0.21/0.51  % (22125)Refutation not found, incomplete strategy% (22125)------------------------------
% 0.21/0.51  % (22125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22125)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22125)Memory used [KB]: 6012
% 0.21/0.51  % (22125)Time elapsed: 0.091 s
% 0.21/0.51  % (22125)------------------------------
% 0.21/0.51  % (22125)------------------------------
% 0.21/0.51  % (22110)Refutation not found, incomplete strategy% (22110)------------------------------
% 0.21/0.51  % (22110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22110)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22110)Memory used [KB]: 6012
% 0.21/0.51  % (22110)Time elapsed: 0.088 s
% 0.21/0.51  % (22110)------------------------------
% 0.21/0.51  % (22110)------------------------------
% 0.21/0.51  % (22130)Refutation not found, incomplete strategy% (22130)------------------------------
% 0.21/0.51  % (22130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22130)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22130)Memory used [KB]: 10490
% 0.21/0.51  % (22130)Time elapsed: 0.082 s
% 0.21/0.51  % (22130)------------------------------
% 0.21/0.51  % (22130)------------------------------
% 0.21/0.51  % (22126)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (22120)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (22120)Refutation not found, incomplete strategy% (22120)------------------------------
% 0.21/0.51  % (22120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22120)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22120)Memory used [KB]: 6012
% 0.21/0.51  % (22120)Time elapsed: 0.091 s
% 0.21/0.51  % (22120)------------------------------
% 0.21/0.51  % (22120)------------------------------
% 0.21/0.51  % (22126)Refutation not found, incomplete strategy% (22126)------------------------------
% 0.21/0.51  % (22126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22126)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22126)Memory used [KB]: 10490
% 0.21/0.51  % (22126)Time elapsed: 0.090 s
% 0.21/0.51  % (22126)------------------------------
% 0.21/0.51  % (22126)------------------------------
% 0.21/0.51  % (22111)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (22113)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (22111)Refutation not found, incomplete strategy% (22111)------------------------------
% 0.21/0.51  % (22111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22111)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  % (22129)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  
% 0.21/0.51  % (22111)Memory used [KB]: 10490
% 0.21/0.51  % (22111)Time elapsed: 0.088 s
% 0.21/0.51  % (22111)------------------------------
% 0.21/0.51  % (22111)------------------------------
% 0.21/0.51  % (22129)Refutation not found, incomplete strategy% (22129)------------------------------
% 0.21/0.51  % (22129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22129)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22129)Memory used [KB]: 6012
% 0.21/0.51  % (22113)Refutation not found, incomplete strategy% (22113)------------------------------
% 0.21/0.51  % (22113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22113)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22113)Memory used [KB]: 10490
% 0.21/0.51  % (22113)Time elapsed: 0.091 s
% 0.21/0.51  % (22113)------------------------------
% 0.21/0.51  % (22113)------------------------------
% 0.21/0.51  % (22129)Time elapsed: 0.093 s
% 0.21/0.51  % (22129)------------------------------
% 0.21/0.51  % (22129)------------------------------
% 0.21/0.51  % (22127)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (22127)# SZS output start Saturation.
% 0.21/0.51  cnf(u10,negated_conjecture,
% 0.21/0.51      r2_xboole_0(sK0,k1_xboole_0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u12,axiom,
% 0.21/0.51      ~r2_xboole_0(X1,X1)).
% 0.21/0.51  
% 0.21/0.51  % (22127)# SZS output end Saturation.
% 0.21/0.51  % (22127)------------------------------
% 0.21/0.51  % (22127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22127)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (22127)Memory used [KB]: 1535
% 0.21/0.51  % (22127)Time elapsed: 0.099 s
% 0.21/0.51  % (22127)------------------------------
% 0.21/0.51  % (22127)------------------------------
% 0.21/0.51  % (22115)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (22115)Refutation not found, incomplete strategy% (22115)------------------------------
% 0.21/0.51  % (22115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22115)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22115)Memory used [KB]: 6012
% 0.21/0.51  % (22115)Time elapsed: 0.099 s
% 0.21/0.51  % (22115)------------------------------
% 0.21/0.51  % (22115)------------------------------
% 0.21/0.51  % (22109)Success in time 0.153 s
%------------------------------------------------------------------------------
