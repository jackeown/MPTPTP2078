%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f22])).

fof(f22,plain,(
    k1_tarski(sK0) != k1_tarski(sK0) ),
    inference(superposition,[],[f18,f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f16,f19])).

fof(f19,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f18,plain,(
    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(definition_unfolding,[],[f12,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f12,plain,(
    k1_tarski(sK0) != k2_tarski(sK0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_tarski(sK0) != k2_tarski(sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f8])).

fof(f8,plain,
    ( ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0)
   => k1_tarski(sK0) != k2_tarski(sK0,sK0) ),
    introduced(choice_axiom,[])).

% (16504)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f6,plain,(
    ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:36:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (16480)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (16483)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (16489)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (16480)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    k1_tarski(sK0) != k1_tarski(sK0)),
% 0.21/0.56    inference(superposition,[],[f18,f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.56    inference(resolution,[],[f16,f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(flattening,[],[f10])).
% 0.21/0.56  fof(f10,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,plain,(
% 0.21/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    k1_tarski(sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.21/0.56    inference(definition_unfolding,[],[f12,f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    k1_tarski(sK0) != k2_tarski(sK0,sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,plain,(
% 0.21/0.56    k1_tarski(sK0) != k2_tarski(sK0,sK0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f8])).
% 0.21/0.56  fof(f8,plain,(
% 0.21/0.56    ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0) => k1_tarski(sK0) != k2_tarski(sK0,sK0)),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  % (16504)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  fof(f6,plain,(
% 0.21/0.56    ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,negated_conjecture,(
% 0.21/0.56    ~! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.56    inference(negated_conjecture,[],[f4])).
% 0.21/0.56  fof(f4,conjecture,(
% 0.21/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (16480)------------------------------
% 0.21/0.56  % (16480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (16480)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (16480)Memory used [KB]: 1663
% 0.21/0.56  % (16480)Time elapsed: 0.140 s
% 0.21/0.56  % (16480)------------------------------
% 0.21/0.56  % (16480)------------------------------
% 0.21/0.56  % (16474)Success in time 0.204 s
%------------------------------------------------------------------------------
