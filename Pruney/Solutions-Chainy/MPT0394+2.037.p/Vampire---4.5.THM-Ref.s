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
% DateTime   : Thu Dec  3 12:46:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 206 expanded)
%              Number of leaves         :   13 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :   77 ( 248 expanded)
%              Number of equality atoms :   63 ( 207 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f180])).

fof(f180,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f38,f159])).

fof(f159,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(forward_demodulation,[],[f158,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) ),
    inference(definition_unfolding,[],[f33,f34,f35])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f23,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f158,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))) ),
    inference(forward_demodulation,[],[f157,f39])).

fof(f39,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f20,f35])).

fof(f20,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f157,plain,(
    ! [X0,X1] : k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))) = k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),X1)) ),
    inference(forward_demodulation,[],[f156,f66])).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f40,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f54,f40])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X0))) ),
    inference(unit_resulting_resolution,[],[f46,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(unit_resulting_resolution,[],[f40,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f156,plain,(
    ! [X0,X1] : k1_setfam_1(k3_tarski(k1_enumset1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0),k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0),k1_enumset1(X1,X1,X1)))) = k4_xboole_0(k1_setfam_1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0)),k4_xboole_0(k1_setfam_1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0)),X1)) ),
    inference(forward_demodulation,[],[f155,f39])).

fof(f155,plain,(
    ! [X0,X1] : k1_setfam_1(k3_tarski(k1_enumset1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0),k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0),k1_enumset1(X1,X1,X1)))) = k4_xboole_0(k1_setfam_1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0)),k4_xboole_0(k1_setfam_1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0)),k1_setfam_1(k1_enumset1(X1,X1,X1)))) ),
    inference(forward_demodulation,[],[f140,f66])).

fof(f140,plain,(
    ! [X0,X1] : k1_setfam_1(k3_tarski(k1_enumset1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0),k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0),k4_xboole_0(k1_enumset1(X1,X1,X1),k1_xboole_0)))) = k4_xboole_0(k1_setfam_1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0)),k4_xboole_0(k1_setfam_1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0)),k1_setfam_1(k4_xboole_0(k1_enumset1(X1,X1,X1),k1_xboole_0)))) ),
    inference(unit_resulting_resolution,[],[f92,f92,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f30,f34,f25])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f85,f64])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0))) ),
    inference(unit_resulting_resolution,[],[f45,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X1] : ~ r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f31,f35,f35])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f38,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f19,f25,f24])).

fof(f19,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:34:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (23459)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (23460)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (23460)Refutation not found, incomplete strategy% (23460)------------------------------
% 0.21/0.54  % (23460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23460)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23460)Memory used [KB]: 10618
% 0.21/0.54  % (23460)Time elapsed: 0.099 s
% 0.21/0.54  % (23460)------------------------------
% 0.21/0.54  % (23460)------------------------------
% 0.21/0.54  % (23468)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (23476)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (23476)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f180])).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.54    inference(superposition,[],[f38,f159])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f158,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f32,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f33,f34,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f21,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f23,f24])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f157,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f20,f35])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)))) = k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),k4_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X0)),X1))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f156,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(backward_demodulation,[],[f40,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f54,f40])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X0)))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f46,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f29,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f40,f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f22,f25])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.54    inference(rectify,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0),k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0),k1_enumset1(X1,X1,X1)))) = k4_xboole_0(k1_setfam_1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0)),k4_xboole_0(k1_setfam_1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0)),X1))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f155,f39])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0),k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0),k1_enumset1(X1,X1,X1)))) = k4_xboole_0(k1_setfam_1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0)),k4_xboole_0(k1_setfam_1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0)),k1_setfam_1(k1_enumset1(X1,X1,X1))))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f140,f66])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0),k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0),k4_xboole_0(k1_enumset1(X1,X1,X1),k1_xboole_0)))) = k4_xboole_0(k1_setfam_1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0)),k4_xboole_0(k1_setfam_1(k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0)),k1_setfam_1(k4_xboole_0(k1_enumset1(X1,X1,X1),k1_xboole_0))))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f92,f92,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f30,f34,f25])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_xboole_0)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f85,f64])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0)))) )),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f45,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f28,f25])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X1] : (~r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) | X0 != X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f31,f35,f35])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),
% 0.21/0.54    inference(definition_unfolding,[],[f19,f25,f24])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.54    inference(negated_conjecture,[],[f13])).
% 0.21/0.54  fof(f13,conjecture,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (23476)------------------------------
% 0.21/0.54  % (23476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23476)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (23476)Memory used [KB]: 6268
% 0.21/0.54  % (23476)Time elapsed: 0.107 s
% 0.21/0.54  % (23476)------------------------------
% 0.21/0.54  % (23476)------------------------------
% 0.21/0.55  % (23451)Success in time 0.181 s
%------------------------------------------------------------------------------
