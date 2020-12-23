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
% DateTime   : Thu Dec  3 12:38:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 158 expanded)
%              Number of leaves         :   13 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :   74 ( 192 expanded)
%              Number of equality atoms :   29 ( 129 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,plain,(
    $false ),
    inference(subsumption_resolution,[],[f230,f24])).

fof(f24,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f230,plain,(
    r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f81,f206])).

fof(f206,plain,(
    sK1 = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f202,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(resolution,[],[f46,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f26,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f202,plain,(
    k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) = k3_xboole_0(sK1,k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f57,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f57,plain,(
    k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) = k3_xboole_0(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(resolution,[],[f53,f32])).

fof(f53,plain,(
    r1_tarski(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(backward_demodulation,[],[f45,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f29,f42,f42])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f45,plain,(
    r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1) ),
    inference(definition_unfolding,[],[f23,f43,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f42])).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f81,plain,(
    ! [X10,X8,X9] : r2_hidden(X8,k3_tarski(k4_enumset1(X9,X9,X9,X9,X9,k4_enumset1(X10,X10,X10,X10,X10,X8)))) ),
    inference(resolution,[],[f64,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0))) ),
    inference(superposition,[],[f46,f48])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (17659)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.41  % (17659)Refutation not found, incomplete strategy% (17659)------------------------------
% 0.20/0.41  % (17659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (17659)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (17659)Memory used [KB]: 10618
% 0.20/0.41  % (17659)Time elapsed: 0.003 s
% 0.20/0.41  % (17659)------------------------------
% 0.20/0.41  % (17659)------------------------------
% 0.20/0.44  % (17662)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.45  % (17662)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f240,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f230,f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ~r2_hidden(sK0,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.20/0.45    inference(negated_conjecture,[],[f14])).
% 0.20/0.45  fof(f14,conjecture,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 0.20/0.45  fof(f230,plain,(
% 0.20/0.45    r2_hidden(sK0,sK1)),
% 0.20/0.45    inference(superposition,[],[f81,f206])).
% 0.20/0.45  fof(f206,plain,(
% 0.20/0.45    sK1 = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),
% 0.20/0.45    inference(forward_demodulation,[],[f202,f54])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = X0) )),
% 0.20/0.45    inference(resolution,[],[f46,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f26,f43])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f30,f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f31,f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f33,f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f38,f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.45  fof(f202,plain,(
% 0.20/0.45    k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) = k3_xboole_0(sK1,k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))),
% 0.20/0.45    inference(superposition,[],[f57,f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) = k3_xboole_0(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 0.20/0.45    inference(resolution,[],[f53,f32])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    r1_tarski(k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 0.20/0.45    inference(backward_demodulation,[],[f45,f48])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f29,f42,f42])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)),sK1)),
% 0.20/0.45    inference(definition_unfolding,[],[f23,f43,f44])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f25,f42])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    ( ! [X10,X8,X9] : (r2_hidden(X8,k3_tarski(k4_enumset1(X9,X9,X9,X9,X9,k4_enumset1(X10,X10,X10,X10,X10,X8))))) )),
% 0.20/0.45    inference(resolution,[],[f64,f51])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f36,f42])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.45    inference(flattening,[],[f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.45    inference(nnf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0)))) )),
% 0.20/0.45    inference(superposition,[],[f46,f48])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (17662)------------------------------
% 0.20/0.45  % (17662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (17662)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (17662)Memory used [KB]: 6396
% 0.20/0.45  % (17662)Time elapsed: 0.014 s
% 0.20/0.45  % (17662)------------------------------
% 0.20/0.45  % (17662)------------------------------
% 0.20/0.45  % (17646)Success in time 0.096 s
%------------------------------------------------------------------------------
