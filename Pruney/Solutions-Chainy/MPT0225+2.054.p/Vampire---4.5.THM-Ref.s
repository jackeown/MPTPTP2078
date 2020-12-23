%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 166 expanded)
%              Number of leaves         :    7 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :   59 ( 209 expanded)
%              Number of equality atoms :   44 ( 185 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f27,f40,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f40,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(trivial_inequality_removal,[],[f39])).

fof(f39,plain,
    ( sK0 != sK0
    | k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f37,f35])).

fof(f35,plain,(
    sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f33])).

fof(f33,plain,
    ( sK0 = sK1
    | sK0 = sK1 ),
    inference(resolution,[],[f25,f30])).

fof(f30,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f29])).

fof(f29,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK1
    | ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f23,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f23,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | sK0 = sK1 ),
    inference(definition_unfolding,[],[f13,f22,f22,f22])).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f14,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f15,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f15,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f14,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f13,plain,
    ( sK0 = sK1
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f16,f22,f22])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f37,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 != sK1 ),
    inference(backward_demodulation,[],[f24,f35])).

fof(f24,plain,
    ( sK0 != sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f12,f22,f22,f22])).

fof(f12,plain,
    ( sK0 != sK1
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X1] : ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f19,f22,f22])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:14:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (5319)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (5321)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (5310)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (5294)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (5297)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (5321)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f27,f40,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    sK0 != sK0 | k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.52    inference(forward_demodulation,[],[f37,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    sK0 = sK1),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    sK0 = sK1 | sK0 = sK1),
% 0.22/0.52    inference(resolution,[],[f25,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | sK0 = sK1),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | sK0 = sK1 | ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.22/0.52    inference(superposition,[],[f23,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | sK0 = sK1),
% 0.22/0.52    inference(definition_unfolding,[],[f13,f22,f22,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f14,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f15,f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.52    inference(negated_conjecture,[],[f7])).
% 0.22/0.52  fof(f7,conjecture,(
% 0.22/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 0.22/0.52    inference(definition_unfolding,[],[f16,f22,f22])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ( ! [X0,X1] : (X0 = X1 | r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 != sK1),
% 0.22/0.52    inference(backward_demodulation,[],[f24,f35])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    sK0 != sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.22/0.52    inference(definition_unfolding,[],[f12,f22,f22,f22])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X1] : (~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 != X1) )),
% 0.22/0.52    inference(definition_unfolding,[],[f19,f22,f22])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (5321)------------------------------
% 0.22/0.52  % (5321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (5321)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (5321)Memory used [KB]: 6140
% 0.22/0.52  % (5321)Time elapsed: 0.086 s
% 0.22/0.52  % (5321)------------------------------
% 0.22/0.52  % (5321)------------------------------
% 0.22/0.53  % (5301)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (5287)Success in time 0.161 s
%------------------------------------------------------------------------------
