%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:29 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u12,negated_conjecture,
    ( r3_xboole_0(sK0,sK1)
    | r2_xboole_0(sK0,sK1)
    | sK0 = sK1
    | r2_xboole_0(sK1,sK0) )).

cnf(u23,negated_conjecture,
    ( ~ r3_xboole_0(sK0,sK0)
    | sK0 != sK1 )).

cnf(u9,negated_conjecture,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK0,sK1) )).

cnf(u11,negated_conjecture,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK1,sK0) )).

cnf(u16,axiom,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) )).

cnf(u20,axiom,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 )).

cnf(u19,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u18,axiom,
    ( ~ r1_tarski(X0,X1)
    | X0 = X1
    | r2_xboole_0(X0,X1) )).

cnf(u27,axiom,
    ( r2_xboole_0(X0,X1)
    | X0 = X1
    | k4_xboole_0(X0,X1) != k1_xboole_0 )).

cnf(u25,axiom,
    ( ~ r2_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u22,axiom,
    ( ~ r2_xboole_0(X1,X1) )).

cnf(u24,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u14,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:45:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.49  % (30268)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.49  % (30277)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.49  % (30286)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.49  % (30286)Refutation not found, incomplete strategy% (30286)------------------------------
% 0.19/0.49  % (30286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (30286)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (30286)Memory used [KB]: 1663
% 0.19/0.49  % (30286)Time elapsed: 0.004 s
% 0.19/0.49  % (30286)------------------------------
% 0.19/0.49  % (30286)------------------------------
% 0.19/0.49  % (30277)Refutation not found, incomplete strategy% (30277)------------------------------
% 0.19/0.49  % (30277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (30277)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (30277)Memory used [KB]: 6140
% 0.19/0.49  % (30277)Time elapsed: 0.005 s
% 0.19/0.49  % (30277)------------------------------
% 0.19/0.49  % (30277)------------------------------
% 0.19/0.49  % (30285)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.49  % (30269)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.49  % (30266)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.49  % (30269)Refutation not found, incomplete strategy% (30269)------------------------------
% 0.19/0.49  % (30269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (30269)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (30269)Memory used [KB]: 6140
% 0.19/0.49  % (30269)Time elapsed: 0.066 s
% 0.19/0.49  % (30269)------------------------------
% 0.19/0.49  % (30269)------------------------------
% 0.19/0.49  % (30266)Refutation not found, incomplete strategy% (30266)------------------------------
% 0.19/0.49  % (30266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (30266)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (30266)Memory used [KB]: 6140
% 0.19/0.49  % (30266)Time elapsed: 0.110 s
% 0.19/0.49  % (30266)------------------------------
% 0.19/0.49  % (30266)------------------------------
% 0.19/0.50  % (30273)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.50  % (30272)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.50  % (30273)Refutation not found, incomplete strategy% (30273)------------------------------
% 0.19/0.50  % (30273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (30273)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (30273)Memory used [KB]: 10618
% 0.19/0.50  % (30273)Time elapsed: 0.117 s
% 0.19/0.50  % (30273)------------------------------
% 0.19/0.50  % (30273)------------------------------
% 0.19/0.50  % (30283)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.50  % (30271)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.51  % (30263)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.51  % (30276)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.51  % (30274)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (30274)Refutation not found, incomplete strategy% (30274)------------------------------
% 0.19/0.51  % (30274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (30274)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (30274)Memory used [KB]: 6140
% 0.19/0.51  % (30274)Time elapsed: 0.124 s
% 0.19/0.51  % (30274)------------------------------
% 0.19/0.51  % (30274)------------------------------
% 0.19/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.51  % (30268)# SZS output start Saturation.
% 0.19/0.51  cnf(u12,negated_conjecture,
% 0.19/0.51      r3_xboole_0(sK0,sK1) | r2_xboole_0(sK0,sK1) | sK0 = sK1 | r2_xboole_0(sK1,sK0)).
% 0.19/0.51  
% 0.19/0.51  cnf(u23,negated_conjecture,
% 0.19/0.51      ~r3_xboole_0(sK0,sK0) | sK0 != sK1).
% 0.19/0.51  
% 0.19/0.51  cnf(u9,negated_conjecture,
% 0.19/0.51      ~r3_xboole_0(sK0,sK1) | ~r2_xboole_0(sK0,sK1)).
% 0.19/0.51  
% 0.19/0.51  cnf(u11,negated_conjecture,
% 0.19/0.51      ~r3_xboole_0(sK0,sK1) | ~r2_xboole_0(sK1,sK0)).
% 0.19/0.51  
% 0.19/0.51  cnf(u16,axiom,
% 0.19/0.51      r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)).
% 0.19/0.51  
% 0.19/0.51  cnf(u20,axiom,
% 0.19/0.51      r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0).
% 0.19/0.51  
% 0.19/0.51  cnf(u19,axiom,
% 0.19/0.51      ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.19/0.51  
% 0.19/0.51  cnf(u18,axiom,
% 0.19/0.51      ~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)).
% 0.19/0.51  
% 0.19/0.51  cnf(u27,axiom,
% 0.19/0.51      r2_xboole_0(X0,X1) | X0 = X1 | k4_xboole_0(X0,X1) != k1_xboole_0).
% 0.19/0.51  
% 0.19/0.51  cnf(u25,axiom,
% 0.19/0.51      ~r2_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.19/0.51  
% 0.19/0.51  cnf(u22,axiom,
% 0.19/0.51      ~r2_xboole_0(X1,X1)).
% 0.19/0.51  
% 0.19/0.51  cnf(u24,axiom,
% 0.19/0.51      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.19/0.51  
% 0.19/0.51  cnf(u14,axiom,
% 0.19/0.51      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.19/0.51  
% 0.19/0.51  % (30268)# SZS output end Saturation.
% 0.19/0.51  % (30268)------------------------------
% 0.19/0.51  % (30268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (30268)Termination reason: Satisfiable
% 0.19/0.51  
% 0.19/0.51  % (30268)Memory used [KB]: 6140
% 0.19/0.51  % (30268)Time elapsed: 0.116 s
% 0.19/0.51  % (30268)------------------------------
% 0.19/0.51  % (30268)------------------------------
% 0.19/0.51  % (30262)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.51  % (30267)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (30261)Success in time 0.167 s
%------------------------------------------------------------------------------
