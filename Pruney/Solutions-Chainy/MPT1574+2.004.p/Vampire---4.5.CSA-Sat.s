%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:20 EST 2020

% Result     : CounterSatisfiable 1.66s
% Output     : Saturation 1.66s
% Verified   : 
% Statistics : Number of clauses        :    1 (   1 expanded)
%              Number of leaves         :    1 (   1 expanded)
%              Depth                    :    0
%              Number of atoms          :    1 (   1 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u7,negated_conjecture,
    ( k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (16991)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.46  % (16991)Refutation not found, incomplete strategy% (16991)------------------------------
% 0.20/0.46  % (16991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (16999)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.47  % (16991)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (16991)Memory used [KB]: 10618
% 0.20/0.47  % (16991)Time elapsed: 0.060 s
% 0.20/0.47  % (16991)------------------------------
% 0.20/0.47  % (16991)------------------------------
% 0.20/0.47  % (16999)Refutation not found, incomplete strategy% (16999)------------------------------
% 0.20/0.47  % (16999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (16999)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (16999)Memory used [KB]: 6140
% 0.20/0.47  % (16999)Time elapsed: 0.069 s
% 0.20/0.47  % (16999)------------------------------
% 0.20/0.47  % (16999)------------------------------
% 0.20/0.56  % (16982)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.56  % (16980)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.57  % (16981)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.57  % (16973)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.57  % (16995)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.57  % (16995)Refutation not found, incomplete strategy% (16995)------------------------------
% 0.20/0.57  % (16995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (16995)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (16995)Memory used [KB]: 1663
% 0.20/0.57  % (16995)Time elapsed: 0.168 s
% 0.20/0.57  % (16995)------------------------------
% 0.20/0.57  % (16995)------------------------------
% 0.20/0.57  % (16973)Refutation not found, incomplete strategy% (16973)------------------------------
% 0.20/0.57  % (16973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (16973)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (16973)Memory used [KB]: 10618
% 0.20/0.57  % (16973)Time elapsed: 0.137 s
% 0.20/0.57  % (16973)------------------------------
% 0.20/0.57  % (16973)------------------------------
% 0.20/0.57  % (16979)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.66/0.57  % SZS status CounterSatisfiable for theBenchmark
% 1.66/0.57  % (16979)# SZS output start Saturation.
% 1.66/0.57  cnf(u7,negated_conjecture,
% 1.66/0.57      k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))).
% 1.66/0.57  
% 1.66/0.57  % (16979)# SZS output end Saturation.
% 1.66/0.57  % (16979)------------------------------
% 1.66/0.57  % (16979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.57  % (16979)Termination reason: Satisfiable
% 1.66/0.57  
% 1.66/0.57  % (16979)Memory used [KB]: 6140
% 1.66/0.57  % (16979)Time elapsed: 0.165 s
% 1.66/0.57  % (16979)------------------------------
% 1.66/0.57  % (16979)------------------------------
% 1.66/0.57  % (16966)Success in time 0.217 s
%------------------------------------------------------------------------------
