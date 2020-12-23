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
% DateTime   : Thu Dec  3 12:30:23 EST 2020

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
cnf(u9,negated_conjecture,
    ( r2_xboole_0(sK1,sK0) )).

cnf(u11,axiom,
    ( ~ r2_xboole_0(X1,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:30:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.43  % (7121)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.43  % (7121)Refutation not found, incomplete strategy% (7121)------------------------------
% 0.21/0.43  % (7121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (7121)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.43  
% 0.21/0.43  % (7121)Memory used [KB]: 6012
% 0.21/0.43  % (7121)Time elapsed: 0.002 s
% 0.21/0.43  % (7121)------------------------------
% 0.21/0.43  % (7121)------------------------------
% 0.21/0.46  % (7124)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  % (7124)Refutation not found, incomplete strategy% (7124)------------------------------
% 0.21/0.46  % (7124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (7124)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (7124)Memory used [KB]: 6012
% 0.21/0.46  % (7124)Time elapsed: 0.062 s
% 0.21/0.46  % (7124)------------------------------
% 0.21/0.46  % (7124)------------------------------
% 0.21/0.48  % (7129)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (7129)Refutation not found, incomplete strategy% (7129)------------------------------
% 0.21/0.48  % (7129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7129)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (7129)Memory used [KB]: 10490
% 0.21/0.48  % (7129)Time elapsed: 0.077 s
% 0.21/0.48  % (7129)------------------------------
% 0.21/0.48  % (7129)------------------------------
% 0.21/0.48  % (7122)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (7122)Refutation not found, incomplete strategy% (7122)------------------------------
% 0.21/0.48  % (7122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7122)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (7122)Memory used [KB]: 1535
% 0.21/0.48  % (7122)Time elapsed: 0.071 s
% 0.21/0.48  % (7122)------------------------------
% 0.21/0.48  % (7122)------------------------------
% 0.21/0.48  % (7109)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (7109)Refutation not found, incomplete strategy% (7109)------------------------------
% 0.21/0.48  % (7109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7109)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (7109)Memory used [KB]: 6012
% 0.21/0.48  % (7109)Time elapsed: 0.065 s
% 0.21/0.48  % (7109)------------------------------
% 0.21/0.48  % (7109)------------------------------
% 0.21/0.48  % (7116)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (7111)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (7114)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (7111)Refutation not found, incomplete strategy% (7111)------------------------------
% 0.21/0.49  % (7111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7114)Refutation not found, incomplete strategy% (7114)------------------------------
% 0.21/0.49  % (7114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7114)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7114)Memory used [KB]: 6012
% 0.21/0.49  % (7114)Time elapsed: 0.070 s
% 0.21/0.49  % (7114)------------------------------
% 0.21/0.49  % (7114)------------------------------
% 0.21/0.49  % (7112)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (7112)Refutation not found, incomplete strategy% (7112)------------------------------
% 0.21/0.49  % (7112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7112)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7112)Memory used [KB]: 10490
% 0.21/0.49  % (7112)Time elapsed: 0.082 s
% 0.21/0.49  % (7112)------------------------------
% 0.21/0.49  % (7112)------------------------------
% 0.21/0.49  % (7125)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (7115)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (7110)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (7115)Refutation not found, incomplete strategy% (7115)------------------------------
% 0.21/0.49  % (7115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7115)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7115)Memory used [KB]: 10490
% 0.21/0.49  % (7115)Time elapsed: 0.061 s
% 0.21/0.49  % (7115)------------------------------
% 0.21/0.49  % (7115)------------------------------
% 0.21/0.49  % (7127)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (7123)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (7125)Refutation not found, incomplete strategy% (7125)------------------------------
% 0.21/0.49  % (7125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7125)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7125)Memory used [KB]: 10618
% 0.21/0.49  % (7125)Time elapsed: 0.066 s
% 0.21/0.49  % (7125)------------------------------
% 0.21/0.49  % (7125)------------------------------
% 0.21/0.49  % (7111)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  % (7127)Refutation not found, incomplete strategy% (7127)------------------------------
% 0.21/0.49  % (7127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7127)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7127)Memory used [KB]: 1535
% 0.21/0.49  % (7127)Time elapsed: 0.085 s
% 0.21/0.49  % (7127)------------------------------
% 0.21/0.49  % (7127)------------------------------
% 0.21/0.49  
% 0.21/0.49  % (7111)Memory used [KB]: 10490
% 0.21/0.49  % (7111)Time elapsed: 0.072 s
% 0.21/0.49  % (7111)------------------------------
% 0.21/0.49  % (7111)------------------------------
% 0.21/0.49  % (7110)Refutation not found, incomplete strategy% (7110)------------------------------
% 0.21/0.49  % (7110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7110)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7110)Memory used [KB]: 10490
% 0.21/0.49  % (7110)Time elapsed: 0.082 s
% 0.21/0.49  % (7110)------------------------------
% 0.21/0.49  % (7110)------------------------------
% 0.21/0.49  % (7118)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (7120)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (7118)Refutation not found, incomplete strategy% (7118)------------------------------
% 0.21/0.49  % (7118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7118)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7118)Memory used [KB]: 10490
% 0.21/0.49  % (7118)Time elapsed: 0.086 s
% 0.21/0.49  % (7118)------------------------------
% 0.21/0.49  % (7118)------------------------------
% 0.21/0.49  % (7120)Refutation not found, incomplete strategy% (7120)------------------------------
% 0.21/0.49  % (7120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7120)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7120)Memory used [KB]: 10490
% 0.21/0.49  % (7120)Time elapsed: 0.084 s
% 0.21/0.49  % (7120)------------------------------
% 0.21/0.49  % (7120)------------------------------
% 0.21/0.49  % (7119)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (7123)Refutation not found, incomplete strategy% (7123)------------------------------
% 0.21/0.49  % (7123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7123)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7123)Memory used [KB]: 10490
% 0.21/0.49  % (7123)Time elapsed: 0.072 s
% 0.21/0.49  % (7123)------------------------------
% 0.21/0.49  % (7123)------------------------------
% 0.21/0.49  % (7119)Refutation not found, incomplete strategy% (7119)------------------------------
% 0.21/0.49  % (7119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (7119)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (7119)Memory used [KB]: 6012
% 0.21/0.49  % (7119)Time elapsed: 0.095 s
% 0.21/0.49  % (7119)------------------------------
% 0.21/0.49  % (7119)------------------------------
% 0.21/0.50  % (7128)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (7117)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (7113)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (7128)Refutation not found, incomplete strategy% (7128)------------------------------
% 0.21/0.50  % (7128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7128)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (7128)Memory used [KB]: 6012
% 0.21/0.50  % (7128)Time elapsed: 0.094 s
% 0.21/0.50  % (7128)------------------------------
% 0.21/0.50  % (7128)------------------------------
% 0.21/0.50  % (7113)Refutation not found, incomplete strategy% (7113)------------------------------
% 0.21/0.50  % (7113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7113)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (7113)Memory used [KB]: 1535
% 0.21/0.50  % (7113)Time elapsed: 0.094 s
% 0.21/0.50  % (7113)------------------------------
% 0.21/0.50  % (7113)------------------------------
% 0.21/0.50  % (7126)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (7126)# SZS output start Saturation.
% 0.21/0.50  cnf(u9,negated_conjecture,
% 0.21/0.50      r2_xboole_0(sK1,sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u11,axiom,
% 0.21/0.50      ~r2_xboole_0(X1,X1)).
% 0.21/0.50  
% 0.21/0.50  % (7126)# SZS output end Saturation.
% 0.21/0.50  % (7126)------------------------------
% 0.21/0.50  % (7126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7126)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (7126)Memory used [KB]: 1535
% 0.21/0.50  % (7126)Time elapsed: 0.096 s
% 0.21/0.50  % (7126)------------------------------
% 0.21/0.50  % (7126)------------------------------
% 0.21/0.50  % (7108)Success in time 0.147 s
%------------------------------------------------------------------------------
