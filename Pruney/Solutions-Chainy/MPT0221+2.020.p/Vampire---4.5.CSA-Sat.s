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
% DateTime   : Thu Dec  3 12:35:48 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u18,axiom,
    ( r1_xboole_0(X0,k1_xboole_0) )).

cnf(u21,axiom,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 )).

cnf(u25,axiom,
    ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) )).

cnf(u35,axiom,
    ( ~ r2_hidden(X1,k1_xboole_0) )).

cnf(u24,axiom,
    ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
    | ~ r1_xboole_0(X0,X1) )).

cnf(u36,negated_conjecture,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) )).

cnf(u19,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (19400)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.49  % (19415)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.49  % (19407)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (19397)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (19400)Refutation not found, incomplete strategy% (19400)------------------------------
% 0.20/0.50  % (19400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (19407)Refutation not found, incomplete strategy% (19407)------------------------------
% 0.20/0.50  % (19407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (19407)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (19407)Memory used [KB]: 6140
% 0.20/0.50  % (19407)Time elapsed: 0.050 s
% 0.20/0.50  % (19407)------------------------------
% 0.20/0.50  % (19407)------------------------------
% 0.20/0.50  % (19400)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (19400)Memory used [KB]: 10618
% 0.20/0.50  % (19400)Time elapsed: 0.050 s
% 0.20/0.50  % (19400)------------------------------
% 0.20/0.50  % (19400)------------------------------
% 0.20/0.50  % (19414)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (19406)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.50  % (19397)# SZS output start Saturation.
% 0.20/0.50  cnf(u18,axiom,
% 0.20/0.50      r1_xboole_0(X0,k1_xboole_0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u21,axiom,
% 0.20/0.50      ~r1_xboole_0(X0,X0) | k1_xboole_0 = X0).
% 0.20/0.50  
% 0.20/0.50  cnf(u25,axiom,
% 0.20/0.50      r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)).
% 0.20/0.50  
% 0.20/0.50  cnf(u35,axiom,
% 0.20/0.50      ~r2_hidden(X1,k1_xboole_0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u24,axiom,
% 0.20/0.50      ~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)).
% 0.20/0.50  
% 0.20/0.50  cnf(u36,negated_conjecture,
% 0.20/0.50      k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)).
% 0.20/0.50  
% 0.20/0.50  cnf(u19,axiom,
% 0.20/0.50      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.20/0.50  
% 0.20/0.50  % (19397)# SZS output end Saturation.
% 0.20/0.50  % (19397)------------------------------
% 0.20/0.50  % (19397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (19397)Termination reason: Satisfiable
% 0.20/0.50  
% 0.20/0.50  % (19397)Memory used [KB]: 6140
% 0.20/0.50  % (19397)Time elapsed: 0.092 s
% 0.20/0.50  % (19397)------------------------------
% 0.20/0.50  % (19397)------------------------------
% 0.20/0.50  % (19395)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (19388)Success in time 0.149 s
%------------------------------------------------------------------------------
