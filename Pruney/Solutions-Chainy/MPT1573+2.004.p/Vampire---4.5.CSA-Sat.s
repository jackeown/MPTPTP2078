%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:19 EST 2020

% Result     : CounterSatisfiable 1.27s
% Output     : Saturation 1.27s
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
cnf(u9,negated_conjecture,
    ( k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (30081)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (30089)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (30089)Refutation not found, incomplete strategy% (30089)------------------------------
% 0.21/0.50  % (30089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30089)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (30089)Memory used [KB]: 6140
% 0.21/0.51  % (30089)Time elapsed: 0.002 s
% 0.21/0.51  % (30089)------------------------------
% 0.21/0.51  % (30089)------------------------------
% 0.21/0.51  % (30076)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (30078)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (30081)Refutation not found, incomplete strategy% (30081)------------------------------
% 0.21/0.51  % (30081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30081)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30081)Memory used [KB]: 6140
% 0.21/0.51  % (30081)Time elapsed: 0.103 s
% 0.21/0.51  % (30081)------------------------------
% 0.21/0.51  % (30081)------------------------------
% 0.21/0.51  % (30092)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (30096)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (30076)Refutation not found, incomplete strategy% (30076)------------------------------
% 0.21/0.51  % (30076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30076)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30076)Memory used [KB]: 10618
% 0.21/0.51  % (30076)Time elapsed: 0.101 s
% 0.21/0.51  % (30076)------------------------------
% 0.21/0.51  % (30076)------------------------------
% 0.21/0.51  % (30097)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (30097)Refutation not found, incomplete strategy% (30097)------------------------------
% 0.21/0.51  % (30097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30097)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.52  % (30097)Memory used [KB]: 1663
% 0.21/0.52  % (30097)Time elapsed: 0.102 s
% 0.21/0.52  % (30097)------------------------------
% 0.21/0.52  % (30097)------------------------------
% 0.21/0.52  % (30084)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (30084)Refutation not found, incomplete strategy% (30084)------------------------------
% 0.21/0.52  % (30084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30084)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30084)Memory used [KB]: 10618
% 0.21/0.52  % (30084)Time elapsed: 0.108 s
% 0.21/0.52  % (30084)------------------------------
% 0.21/0.52  % (30084)------------------------------
% 1.27/0.53  % (30078)Refutation not found, incomplete strategy% (30078)------------------------------
% 1.27/0.53  % (30078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (30078)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (30078)Memory used [KB]: 6140
% 1.27/0.53  % (30078)Time elapsed: 0.127 s
% 1.27/0.53  % (30078)------------------------------
% 1.27/0.53  % (30078)------------------------------
% 1.27/0.53  % (30074)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.53  % (30074)Refutation not found, incomplete strategy% (30074)------------------------------
% 1.27/0.53  % (30074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (30074)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (30074)Memory used [KB]: 1663
% 1.27/0.53  % (30074)Time elapsed: 0.125 s
% 1.27/0.53  % (30074)------------------------------
% 1.27/0.53  % (30074)------------------------------
% 1.27/0.53  % (30075)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.53  % (30077)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.53  % (30079)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.53  % SZS status CounterSatisfiable for theBenchmark
% 1.27/0.53  % (30079)# SZS output start Saturation.
% 1.27/0.53  cnf(u9,negated_conjecture,
% 1.27/0.53      k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))).
% 1.27/0.53  
% 1.27/0.53  % (30079)# SZS output end Saturation.
% 1.27/0.53  % (30079)------------------------------
% 1.27/0.53  % (30079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (30079)Termination reason: Satisfiable
% 1.27/0.53  
% 1.27/0.53  % (30079)Memory used [KB]: 6140
% 1.27/0.53  % (30079)Time elapsed: 0.124 s
% 1.27/0.53  % (30079)------------------------------
% 1.27/0.53  % (30079)------------------------------
% 1.27/0.53  % (30073)Success in time 0.172 s
%------------------------------------------------------------------------------
