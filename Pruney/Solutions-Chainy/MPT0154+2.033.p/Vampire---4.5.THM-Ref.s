%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  88 expanded)
%              Number of leaves         :    6 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 ( 146 expanded)
%              Number of equality atoms :   33 (  87 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f154])).

fof(f154,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) ),
    inference(superposition,[],[f26,f140])).

fof(f140,plain,(
    ! [X8,X9] : k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))) = k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X8))) ),
    inference(subsumption_resolution,[],[f138,f61])).

fof(f61,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK2(X4,X5,X5),X4)
      | k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))) = X5 ) ),
    inference(subsumption_resolution,[],[f57,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f14,f12])).

fof(f12,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f57,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK2(X4,X5,X5),X4)
      | r2_hidden(sK2(X4,X5,X5),X5)
      | k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))) = X5 ) ),
    inference(factoring,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ) ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f138,plain,(
    ! [X8,X9] :
      ( k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))) = k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X8)))
      | ~ r2_hidden(sK2(X8,k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8)))),X8) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
    ! [X8,X9] :
      ( k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))) = k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X8)))
      | ~ r2_hidden(sK2(X8,k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8)))),X8)
      | k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))) = k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X8))) ) ),
    inference(resolution,[],[f44,f61])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK2(X0,X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),X2)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
      | ~ r2_hidden(sK2(X0,X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),X0) ) ),
    inference(resolution,[],[f32,f34])).

% (10921)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (10913)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (10902)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != X2 ) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2 ) ),
    inference(definition_unfolding,[],[f16,f22])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f26,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f10,f23,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f15,f22,f23])).

fof(f15,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f13,f22])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f10,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (10903)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (10903)Refutation not found, incomplete strategy% (10903)------------------------------
% 0.21/0.46  % (10903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (10903)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (10903)Memory used [KB]: 6140
% 0.21/0.46  % (10903)Time elapsed: 0.074 s
% 0.21/0.46  % (10903)------------------------------
% 0.21/0.46  % (10903)------------------------------
% 0.21/0.48  % (10905)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.49  % (10905)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (10928)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.50  % (10920)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f154])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))),
% 0.21/0.50    inference(superposition,[],[f26,f140])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ( ! [X8,X9] : (k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))) = k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X8)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f138,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X4,X5] : (r2_hidden(sK2(X4,X5,X5),X4) | k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))) = X5) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f57,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2) )),
% 0.21/0.50    inference(definition_unfolding,[],[f17,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f14,f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X4,X5] : (r2_hidden(sK2(X4,X5,X5),X4) | r2_hidden(sK2(X4,X5,X5),X5) | k5_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,X4))) = X5) )),
% 0.21/0.50    inference(factoring,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2) )),
% 0.21/0.50    inference(definition_unfolding,[],[f18,f22])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ( ! [X8,X9] : (k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))) = k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X8))) | ~r2_hidden(sK2(X8,k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8)))),X8)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f130])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    ( ! [X8,X9] : (k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))) = k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X8))) | ~r2_hidden(sK2(X8,k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8)))),X8) | k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))) = k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X9,X8))),X8)))) )),
% 0.21/0.50    inference(resolution,[],[f44,f61])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK2(X0,X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),X2) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))) | ~r2_hidden(sK2(X0,X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))),X0)) )),
% 0.21/0.50    inference(resolution,[],[f32,f34])).
% 0.21/0.51  % (10921)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (10913)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (10902)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) | ~r2_hidden(X3,X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != X2) )),
% 0.21/0.51    inference(definition_unfolding,[],[f20,f22])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X0) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X2) )),
% 0.21/0.51    inference(definition_unfolding,[],[f16,f22])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0))))),
% 0.21/0.51    inference(definition_unfolding,[],[f10,f23,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0))))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f15,f22,f23])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f13,f22])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (10905)------------------------------
% 0.21/0.51  % (10905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10905)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (10905)Memory used [KB]: 6396
% 0.21/0.51  % (10905)Time elapsed: 0.101 s
% 0.21/0.51  % (10905)------------------------------
% 0.21/0.51  % (10905)------------------------------
% 0.21/0.51  % (10895)Success in time 0.153 s
%------------------------------------------------------------------------------
