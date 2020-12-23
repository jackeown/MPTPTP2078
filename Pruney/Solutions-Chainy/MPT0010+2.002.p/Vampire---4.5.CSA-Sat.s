%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:32 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    1 (   1 expanded)
%              Number of leaves         :    1 (   1 expanded)
%              Depth                    :    0
%              Number of atoms          :    2 (   2 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    4 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u14,negated_conjecture,
    ( ~ ( k1_xboole_0 != sK0 )
    | k1_xboole_0 != sK0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:55:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (13063)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.45  % (13063)Refutation not found, incomplete strategy% (13063)------------------------------
% 0.21/0.45  % (13063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (13063)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (13063)Memory used [KB]: 6012
% 0.21/0.45  % (13063)Time elapsed: 0.036 s
% 0.21/0.45  % (13063)------------------------------
% 0.21/0.45  % (13063)------------------------------
% 0.21/0.46  % (13045)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (13045)Refutation not found, incomplete strategy% (13045)------------------------------
% 0.21/0.47  % (13045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (13045)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (13045)Memory used [KB]: 10490
% 0.21/0.47  % (13045)Time elapsed: 0.050 s
% 0.21/0.47  % (13045)------------------------------
% 0.21/0.47  % (13045)------------------------------
% 0.21/0.47  % (13055)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (13055)Refutation not found, incomplete strategy% (13055)------------------------------
% 0.21/0.47  % (13055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (13055)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (13055)Memory used [KB]: 10490
% 0.21/0.47  % (13055)Time elapsed: 0.053 s
% 0.21/0.47  % (13055)------------------------------
% 0.21/0.47  % (13055)------------------------------
% 0.21/0.47  % (13052)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (13056)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (13056)Refutation not found, incomplete strategy% (13056)------------------------------
% 0.21/0.48  % (13056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13056)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (13056)Memory used [KB]: 6012
% 0.21/0.48  % (13056)Time elapsed: 0.002 s
% 0.21/0.48  % (13056)------------------------------
% 0.21/0.48  % (13056)------------------------------
% 0.21/0.48  % (13047)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (13047)Refutation not found, incomplete strategy% (13047)------------------------------
% 0.21/0.48  % (13047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13047)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (13047)Memory used [KB]: 10490
% 0.21/0.48  % (13047)Time elapsed: 0.072 s
% 0.21/0.48  % (13047)------------------------------
% 0.21/0.48  % (13047)------------------------------
% 0.21/0.48  % (13048)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (13048)Refutation not found, incomplete strategy% (13048)------------------------------
% 0.21/0.48  % (13048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13048)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (13048)Memory used [KB]: 1535
% 0.21/0.48  % (13048)Time elapsed: 0.072 s
% 0.21/0.48  % (13048)------------------------------
% 0.21/0.48  % (13048)------------------------------
% 0.21/0.49  % (13051)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (13064)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (13058)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (13064)Refutation not found, incomplete strategy% (13064)------------------------------
% 0.21/0.49  % (13064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13064)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13064)Memory used [KB]: 10490
% 0.21/0.49  % (13064)Time elapsed: 0.083 s
% 0.21/0.49  % (13064)------------------------------
% 0.21/0.49  % (13064)------------------------------
% 0.21/0.49  % (13058)Refutation not found, incomplete strategy% (13058)------------------------------
% 0.21/0.49  % (13058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13058)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13058)Memory used [KB]: 10490
% 0.21/0.49  % (13058)Time elapsed: 0.078 s
% 0.21/0.49  % (13058)------------------------------
% 0.21/0.49  % (13058)------------------------------
% 0.21/0.50  % (13049)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (13050)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (13060)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (13050)# SZS output start Saturation.
% 0.21/0.50  tff(u14,negated_conjecture,
% 0.21/0.50      ((~(k1_xboole_0 != sK0)) | (k1_xboole_0 != sK0))).
% 0.21/0.50  
% 0.21/0.50  % (13050)# SZS output end Saturation.
% 0.21/0.50  % (13050)------------------------------
% 0.21/0.50  % (13050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13050)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (13050)Memory used [KB]: 10490
% 0.21/0.50  % (13050)Time elapsed: 0.068 s
% 0.21/0.50  % (13050)------------------------------
% 0.21/0.50  % (13050)------------------------------
% 0.21/0.50  % (13043)Success in time 0.144 s
%------------------------------------------------------------------------------
