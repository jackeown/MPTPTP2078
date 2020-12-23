%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:37 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    0
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u9,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u10,axiom,
    ( ~ v1_xboole_0(X0)
    | X0 = X1
    | ~ v1_xboole_0(X1) )).

cnf(u11,axiom,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 )).

cnf(u7,negated_conjecture,
    ( k1_xboole_0 = k2_xboole_0(sK0,sK1) )).

cnf(u8,negated_conjecture,
    ( k1_xboole_0 != sK0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (16638)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.46  % (16633)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (16638)Refutation not found, incomplete strategy% (16638)------------------------------
% 0.21/0.46  % (16638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (16638)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (16638)Memory used [KB]: 1535
% 0.21/0.46  % (16638)Time elapsed: 0.053 s
% 0.21/0.46  % (16638)------------------------------
% 0.21/0.46  % (16638)------------------------------
% 0.21/0.46  % (16633)Refutation not found, incomplete strategy% (16633)------------------------------
% 0.21/0.46  % (16633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (16633)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (16633)Memory used [KB]: 6140
% 0.21/0.46  % (16633)Time elapsed: 0.049 s
% 0.21/0.46  % (16633)------------------------------
% 0.21/0.46  % (16633)------------------------------
% 0.21/0.48  % (16639)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (16653)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (16653)Refutation not found, incomplete strategy% (16653)------------------------------
% 0.21/0.48  % (16653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16653)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (16653)Memory used [KB]: 6012
% 0.21/0.48  % (16653)Time elapsed: 0.070 s
% 0.21/0.48  % (16653)------------------------------
% 0.21/0.48  % (16653)------------------------------
% 0.21/0.49  % (16648)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (16634)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (16649)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (16637)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (16636)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (16651)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (16637)Refutation not found, incomplete strategy% (16637)------------------------------
% 0.21/0.50  % (16637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16637)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (16637)Memory used [KB]: 10490
% 0.21/0.50  % (16637)Time elapsed: 0.063 s
% 0.21/0.50  % (16637)------------------------------
% 0.21/0.50  % (16637)------------------------------
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (16651)# SZS output start Saturation.
% 0.21/0.50  cnf(u9,axiom,
% 0.21/0.50      v1_xboole_0(k1_xboole_0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u10,axiom,
% 0.21/0.50      ~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u11,axiom,
% 0.21/0.50      ~v1_xboole_0(X0) | k1_xboole_0 = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u7,negated_conjecture,
% 0.21/0.50      k1_xboole_0 = k2_xboole_0(sK0,sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u8,negated_conjecture,
% 0.21/0.50      k1_xboole_0 != sK0).
% 0.21/0.50  
% 0.21/0.50  % (16651)# SZS output end Saturation.
% 0.21/0.50  % (16651)------------------------------
% 0.21/0.50  % (16651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16651)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (16651)Memory used [KB]: 1535
% 0.21/0.50  % (16651)Time elapsed: 0.064 s
% 0.21/0.50  % (16651)------------------------------
% 0.21/0.50  % (16651)------------------------------
% 0.21/0.50  % (16628)Success in time 0.141 s
%------------------------------------------------------------------------------
