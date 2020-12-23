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
% DateTime   : Thu Dec  3 12:36:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 122 expanded)
%              Number of leaves         :   10 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :   63 ( 153 expanded)
%              Number of equality atoms :   43 ( 133 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144,plain,(
    $false ),
    inference(resolution,[],[f129,f38])).

fof(f38,plain,(
    ! [X1] : ~ r1_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f129,plain,(
    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f51,f120])).

fof(f120,plain,(
    ! [X0] : k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),X0) ),
    inference(backward_demodulation,[],[f43,f115])).

fof(f115,plain,(
    ! [X0] : k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),X0)) ),
    inference(superposition,[],[f37,f59])).

fof(f59,plain,(
    ! [X2] : k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),X2)) = k4_xboole_0(k1_tarski(sK0),X2) ),
    inference(forward_demodulation,[],[f58,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f58,plain,(
    ! [X2] : k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),X2)) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),X2))) ),
    inference(backward_demodulation,[],[f53,f54])).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0))) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),X0)) ),
    inference(unit_resulting_resolution,[],[f39,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,X2)) ) ),
    inference(definition_unfolding,[],[f29,f22,f22])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f39,plain,(
    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f20,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f20,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f53,plain,(
    ! [X2] : k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),X2)) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X2)))) ),
    inference(forward_demodulation,[],[f52,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f52,plain,(
    ! [X2] : k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X2))) = k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),X2)) ),
    inference(forward_demodulation,[],[f47,f28])).

fof(f47,plain,(
    ! [X2] : k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X2))) = k4_xboole_0(k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),X2) ),
    inference(superposition,[],[f32,f31])).

fof(f31,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f19,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f21,f22,f22])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f30,f22])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),X0))) = k4_xboole_0(k1_tarski(sK0),X0) ),
    inference(superposition,[],[f32,f31])).

fof(f51,plain,(
    r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f50,f48])).

fof(f48,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ),
    inference(backward_demodulation,[],[f31,f42])).

fof(f42,plain,(
    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f33,f31])).

fof(f50,plain,(
    r1_xboole_0(k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f45,f42])).

fof(f45,plain,(
    r1_xboole_0(k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(superposition,[],[f35,f31])).

fof(f35,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f25,f22])).

fof(f25,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:16:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (18124)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (18123)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (18129)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (18126)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (18125)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (18140)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (18127)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (18125)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f144,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(resolution,[],[f129,f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X1] : (~r1_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.22/0.55    inference(equality_resolution,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.22/0.55    inference(backward_demodulation,[],[f51,f120])).
% 0.22/0.55  fof(f120,plain,(
% 0.22/0.55    ( ! [X0] : (k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),X0)) )),
% 0.22/0.55    inference(backward_demodulation,[],[f43,f115])).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    ( ! [X0] : (k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),X0))) )),
% 0.22/0.55    inference(superposition,[],[f37,f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ( ! [X2] : (k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),X2)) = k4_xboole_0(k1_tarski(sK0),X2)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f58,f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f23,f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X2] : (k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),X2)) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),X2)))) )),
% 0.22/0.55    inference(backward_demodulation,[],[f53,f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X0] : (k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X0))) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),X0))) )),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f39,f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,X2))) )),
% 0.22/0.55    inference(definition_unfolding,[],[f29,f22,f22])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f20,f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    sK0 != sK1),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.22/0.55    inference(negated_conjecture,[],[f12])).
% 0.22/0.55  fof(f12,conjecture,(
% 0.22/0.55    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X2] : (k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),X2)) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),X2))))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f52,f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X2] : (k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X2))) = k4_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),X2))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f47,f28])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X2] : (k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X2))) = k4_xboole_0(k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),X2)) )),
% 0.22/0.55    inference(superposition,[],[f32,f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.22/0.55    inference(definition_unfolding,[],[f19,f22])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f21,f22,f22])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 0.22/0.55    inference(definition_unfolding,[],[f30,f22])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ( ! [X0] : (k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),X0))) = k4_xboole_0(k1_tarski(sK0),X0)) )),
% 0.22/0.55    inference(superposition,[],[f32,f31])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))),
% 0.22/0.55    inference(forward_demodulation,[],[f50,f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))),
% 0.22/0.55    inference(backward_demodulation,[],[f31,f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.22/0.55    inference(superposition,[],[f33,f31])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    r1_xboole_0(k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))),
% 0.22/0.55    inference(forward_demodulation,[],[f45,f42])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    r1_xboole_0(k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.22/0.55    inference(superposition,[],[f35,f31])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f25,f22])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (18125)------------------------------
% 0.22/0.55  % (18125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18125)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (18125)Memory used [KB]: 6268
% 0.22/0.55  % (18125)Time elapsed: 0.133 s
% 0.22/0.55  % (18125)------------------------------
% 0.22/0.55  % (18125)------------------------------
% 0.22/0.55  % (18132)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (18121)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (18131)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (18132)Refutation not found, incomplete strategy% (18132)------------------------------
% 0.22/0.55  % (18132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18132)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18132)Memory used [KB]: 10618
% 0.22/0.55  % (18132)Time elapsed: 0.130 s
% 0.22/0.55  % (18132)------------------------------
% 0.22/0.55  % (18132)------------------------------
% 0.22/0.55  % (18141)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (18131)Refutation not found, incomplete strategy% (18131)------------------------------
% 0.22/0.55  % (18131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18131)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18131)Memory used [KB]: 10618
% 0.22/0.55  % (18131)Time elapsed: 0.136 s
% 0.22/0.55  % (18131)------------------------------
% 0.22/0.55  % (18131)------------------------------
% 0.22/0.55  % (18142)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (18122)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (18120)Success in time 0.192 s
%------------------------------------------------------------------------------
