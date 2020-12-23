%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:47 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    0
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    2 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u38,axiom,
    ( r1_xboole_0(X0,k1_xboole_0) )).

cnf(u30,axiom,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) )).

cnf(u37,axiom,
    ( ~ r1_xboole_0(X1,k1_xboole_0)
    | r1_xboole_0(X0,k1_xboole_0) )).

cnf(u19,axiom,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 )).

cnf(u36,axiom,
    ( r2_hidden(sK2(X0,k1_xboole_0),k1_xboole_0)
    | r1_xboole_0(X0,k1_xboole_0) )).

cnf(u23,axiom,
    ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) )).

cnf(u32,axiom,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(X0,k1_xboole_0) )).

cnf(u22,axiom,
    ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
    | ~ r1_xboole_0(X0,X1) )).

cnf(u33,negated_conjecture,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) )).

cnf(u17,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:00:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (22341)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (22355)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (22341)Refutation not found, incomplete strategy% (22341)------------------------------
% 0.21/0.51  % (22341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22341)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22341)Memory used [KB]: 1663
% 0.21/0.51  % (22341)Time elapsed: 0.003 s
% 0.21/0.51  % (22341)------------------------------
% 0.21/0.51  % (22341)------------------------------
% 0.21/0.52  % (22348)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (22348)Refutation not found, incomplete strategy% (22348)------------------------------
% 0.21/0.52  % (22348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22348)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22348)Memory used [KB]: 6140
% 0.21/0.52  % (22348)Time elapsed: 0.098 s
% 0.21/0.52  % (22348)------------------------------
% 0.21/0.52  % (22348)------------------------------
% 0.21/0.52  % (22346)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (22346)Refutation not found, incomplete strategy% (22346)------------------------------
% 0.21/0.52  % (22346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22346)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22346)Memory used [KB]: 6140
% 0.21/0.52  % (22346)Time elapsed: 0.107 s
% 0.21/0.52  % (22346)------------------------------
% 0.21/0.52  % (22346)------------------------------
% 0.21/0.53  % (22366)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (22360)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (22360)Refutation not found, incomplete strategy% (22360)------------------------------
% 0.21/0.53  % (22360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22360)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22360)Memory used [KB]: 10618
% 0.21/0.53  % (22360)Time elapsed: 0.104 s
% 0.21/0.53  % (22360)------------------------------
% 0.21/0.53  % (22360)------------------------------
% 0.21/0.53  % (22347)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (22359)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (22350)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (22347)# SZS output start Saturation.
% 0.21/0.53  cnf(u38,axiom,
% 0.21/0.53      r1_xboole_0(X0,k1_xboole_0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u30,axiom,
% 0.21/0.53      r1_xboole_0(k1_xboole_0,k1_xboole_0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u37,axiom,
% 0.21/0.53      ~r1_xboole_0(X1,k1_xboole_0) | r1_xboole_0(X0,k1_xboole_0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u19,axiom,
% 0.21/0.53      ~r1_xboole_0(X0,X0) | k1_xboole_0 = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u36,axiom,
% 0.21/0.53      r2_hidden(sK2(X0,k1_xboole_0),k1_xboole_0) | r1_xboole_0(X0,k1_xboole_0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u23,axiom,
% 0.21/0.53      r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u32,axiom,
% 0.21/0.53      ~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u22,axiom,
% 0.21/0.53      ~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u33,negated_conjecture,
% 0.21/0.53      k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u17,axiom,
% 0.21/0.53      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.53  
% 0.21/0.53  % (22347)# SZS output end Saturation.
% 0.21/0.53  % (22347)------------------------------
% 0.21/0.53  % (22347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22347)Termination reason: Satisfiable
% 0.21/0.53  
% 0.21/0.53  % (22347)Memory used [KB]: 6140
% 0.21/0.53  % (22347)Time elapsed: 0.109 s
% 0.21/0.53  % (22347)------------------------------
% 0.21/0.53  % (22347)------------------------------
% 0.21/0.53  % (22367)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (22350)Refutation not found, incomplete strategy% (22350)------------------------------
% 0.21/0.53  % (22350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22350)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22350)Memory used [KB]: 10618
% 0.21/0.53  % (22350)Time elapsed: 0.002 s
% 0.21/0.53  % (22350)------------------------------
% 0.21/0.53  % (22350)------------------------------
% 0.21/0.53  % (22340)Success in time 0.171 s
%------------------------------------------------------------------------------
