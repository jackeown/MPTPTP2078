%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 (  49 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  69 expanded)
%              Number of equality atoms :   27 (  35 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f36])).

fof(f36,plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(superposition,[],[f26,f35])).

fof(f35,plain,(
    ! [X0] : o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X0) ),
    inference(forward_demodulation,[],[f34,f32])).

fof(f32,plain,(
    o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(forward_demodulation,[],[f31,f28])).

fof(f28,plain,(
    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f20,f19,f19])).

fof(f19,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f20,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f31,plain,(
    o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,k1_relat_1(o_0_0_xboole_0)) ),
    inference(resolution,[],[f24,f30])).

fof(f30,plain,(
    v1_relat_1(o_0_0_xboole_0) ),
    inference(resolution,[],[f23,f18])).

fof(f18,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f34,plain,(
    ! [X0] : k7_relat_1(o_0_0_xboole_0,o_0_0_xboole_0) = k7_relat_1(k7_relat_1(o_0_0_xboole_0,o_0_0_xboole_0),X0) ),
    inference(resolution,[],[f33,f30])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,o_0_0_xboole_0) = k7_relat_1(k7_relat_1(X0,o_0_0_xboole_0),X1) ) ),
    inference(resolution,[],[f25,f29])).

fof(f29,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f26,plain,(
    o_0_0_xboole_0 != k7_relat_1(o_0_0_xboole_0,sK0) ),
    inference(definition_unfolding,[],[f17,f19,f19])).

fof(f17,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f15])).

fof(f15,plain,
    ( ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:02 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.40  % (6901)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.40  % (6901)Refutation found. Thanks to Tanya!
% 0.19/0.40  % SZS status Theorem for theBenchmark
% 0.19/0.40  % SZS output start Proof for theBenchmark
% 0.19/0.40  fof(f37,plain,(
% 0.19/0.40    $false),
% 0.19/0.40    inference(trivial_inequality_removal,[],[f36])).
% 0.19/0.40  fof(f36,plain,(
% 0.19/0.40    o_0_0_xboole_0 != o_0_0_xboole_0),
% 0.19/0.40    inference(superposition,[],[f26,f35])).
% 0.19/0.40  fof(f35,plain,(
% 0.19/0.40    ( ! [X0] : (o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X0)) )),
% 0.19/0.40    inference(forward_demodulation,[],[f34,f32])).
% 0.19/0.40  fof(f32,plain,(
% 0.19/0.40    o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,o_0_0_xboole_0)),
% 0.19/0.40    inference(forward_demodulation,[],[f31,f28])).
% 0.19/0.40  fof(f28,plain,(
% 0.19/0.40    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 0.19/0.40    inference(definition_unfolding,[],[f20,f19,f19])).
% 0.19/0.40  fof(f19,plain,(
% 0.19/0.40    k1_xboole_0 = o_0_0_xboole_0),
% 0.19/0.40    inference(cnf_transformation,[],[f1])).
% 0.19/0.40  fof(f1,axiom,(
% 0.19/0.40    k1_xboole_0 = o_0_0_xboole_0),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.19/0.40  fof(f20,plain,(
% 0.19/0.40    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.40    inference(cnf_transformation,[],[f6])).
% 0.19/0.40  fof(f6,axiom,(
% 0.19/0.40    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.19/0.40  fof(f31,plain,(
% 0.19/0.40    o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,k1_relat_1(o_0_0_xboole_0))),
% 0.19/0.40    inference(resolution,[],[f24,f30])).
% 0.19/0.40  fof(f30,plain,(
% 0.19/0.40    v1_relat_1(o_0_0_xboole_0)),
% 0.19/0.40    inference(resolution,[],[f23,f18])).
% 0.19/0.40  fof(f18,plain,(
% 0.19/0.40    v1_xboole_0(o_0_0_xboole_0)),
% 0.19/0.40    inference(cnf_transformation,[],[f2])).
% 0.19/0.40  fof(f2,axiom,(
% 0.19/0.40    v1_xboole_0(o_0_0_xboole_0)),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 0.19/0.40  fof(f23,plain,(
% 0.19/0.40    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f11])).
% 0.19/0.40  fof(f11,plain,(
% 0.19/0.40    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.19/0.40    inference(ennf_transformation,[],[f4])).
% 0.19/0.40  fof(f4,axiom,(
% 0.19/0.40    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.19/0.40  fof(f24,plain,(
% 0.19/0.40    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.19/0.40    inference(cnf_transformation,[],[f12])).
% 0.19/0.40  fof(f12,plain,(
% 0.19/0.40    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.19/0.40    inference(ennf_transformation,[],[f7])).
% 0.19/0.40  fof(f7,axiom,(
% 0.19/0.40    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.19/0.40  fof(f34,plain,(
% 0.19/0.40    ( ! [X0] : (k7_relat_1(o_0_0_xboole_0,o_0_0_xboole_0) = k7_relat_1(k7_relat_1(o_0_0_xboole_0,o_0_0_xboole_0),X0)) )),
% 0.19/0.40    inference(resolution,[],[f33,f30])).
% 0.19/0.40  fof(f33,plain,(
% 0.19/0.40    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,o_0_0_xboole_0) = k7_relat_1(k7_relat_1(X0,o_0_0_xboole_0),X1)) )),
% 0.19/0.40    inference(resolution,[],[f25,f29])).
% 0.19/0.40  fof(f29,plain,(
% 0.19/0.40    ( ! [X0] : (r1_tarski(o_0_0_xboole_0,X0)) )),
% 0.19/0.40    inference(definition_unfolding,[],[f22,f19])).
% 0.19/0.40  fof(f22,plain,(
% 0.19/0.40    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f3])).
% 0.19/0.40  fof(f3,axiom,(
% 0.19/0.40    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.40  fof(f25,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f14])).
% 0.19/0.40  fof(f14,plain,(
% 0.19/0.40    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.19/0.40    inference(flattening,[],[f13])).
% 0.19/0.40  fof(f13,plain,(
% 0.19/0.40    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.19/0.40    inference(ennf_transformation,[],[f5])).
% 0.19/0.40  fof(f5,axiom,(
% 0.19/0.40    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 0.19/0.40  fof(f26,plain,(
% 0.19/0.40    o_0_0_xboole_0 != k7_relat_1(o_0_0_xboole_0,sK0)),
% 0.19/0.40    inference(definition_unfolding,[],[f17,f19,f19])).
% 0.19/0.40  fof(f17,plain,(
% 0.19/0.40    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.19/0.40    inference(cnf_transformation,[],[f16])).
% 0.19/0.40  fof(f16,plain,(
% 0.19/0.40    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.19/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f15])).
% 0.19/0.40  fof(f15,plain,(
% 0.19/0.40    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.19/0.40    introduced(choice_axiom,[])).
% 0.19/0.40  fof(f10,plain,(
% 0.19/0.40    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)),
% 0.19/0.40    inference(ennf_transformation,[],[f9])).
% 0.19/0.40  fof(f9,negated_conjecture,(
% 0.19/0.40    ~! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.19/0.40    inference(negated_conjecture,[],[f8])).
% 0.19/0.40  fof(f8,conjecture,(
% 0.19/0.40    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.19/0.40  % SZS output end Proof for theBenchmark
% 0.19/0.40  % (6901)------------------------------
% 0.19/0.40  % (6901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.40  % (6901)Termination reason: Refutation
% 0.19/0.40  
% 0.19/0.40  % (6901)Memory used [KB]: 1535
% 0.19/0.40  % (6901)Time elapsed: 0.003 s
% 0.19/0.40  % (6901)------------------------------
% 0.19/0.40  % (6901)------------------------------
% 0.19/0.41  % (6887)Success in time 0.056 s
%------------------------------------------------------------------------------
