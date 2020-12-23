%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 199 expanded)
%              Number of leaves         :    9 (  64 expanded)
%              Depth                    :   13
%              Number of atoms          :   74 ( 274 expanded)
%              Number of equality atoms :   49 ( 223 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(resolution,[],[f68,f43])).

fof(f43,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k4_enumset1(X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f17,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(f17,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f68,plain,(
    ~ r1_tarski(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f66,f62])).

fof(f62,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f44,f61])).

fof(f61,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f55])).

fof(f55,plain,
    ( sK0 != sK0
    | ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f35,f53])).

fof(f53,plain,
    ( sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,
    ( sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f41,f34])).

fof(f34,plain,
    ( r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))
    | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f16,f31,f31])).

fof(f16,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X1))
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f23,f31,f31])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,
    ( sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f15,f31,f31])).

fof(f15,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f37,f38])).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))),k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f19,f29,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f18,f29])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f66,plain,(
    ~ r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f36,f62])).

fof(f36,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f14,f31])).

fof(f14,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:21:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (1880)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (1893)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.50  % (1893)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (1885)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(resolution,[],[f68,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(k1_xboole_0,k4_enumset1(X1,X1,X1,X1,X1,X1))) )),
% 0.20/0.51    inference(equality_resolution,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f24,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f17,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f26,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ~r1_tarski(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.51    inference(forward_demodulation,[],[f66,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    k1_xboole_0 = sK0),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f44,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK0) | k1_xboole_0 = sK0),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    sK0 != sK0 | ~r1_tarski(sK0,sK0) | k1_xboole_0 = sK0),
% 0.20/0.51    inference(superposition,[],[f35,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.20/0.51    inference(resolution,[],[f41,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.20/0.51    inference(definition_unfolding,[],[f16,f31,f31])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | r1_tarski(sK0,k1_tarski(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <~> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.51    inference(negated_conjecture,[],[f11])).
% 0.20/0.51  fof(f11,conjecture,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f23,f31,f31])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | ~r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.51    inference(definition_unfolding,[],[f15,f31,f31])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.51    inference(superposition,[],[f37,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))),k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f19,f29,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f22,f20])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1))),X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f18,f29])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ~r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f65])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.51    inference(backward_demodulation,[],[f36,f62])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.51    inference(definition_unfolding,[],[f14,f31])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (1893)------------------------------
% 0.20/0.51  % (1893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1893)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (1893)Memory used [KB]: 6268
% 0.20/0.51  % (1893)Time elapsed: 0.101 s
% 0.20/0.51  % (1893)------------------------------
% 0.20/0.51  % (1893)------------------------------
% 0.20/0.51  % (1876)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (1864)Success in time 0.152 s
%------------------------------------------------------------------------------
