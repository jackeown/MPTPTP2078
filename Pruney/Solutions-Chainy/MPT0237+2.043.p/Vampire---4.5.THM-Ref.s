%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  54 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :   57 (  71 expanded)
%              Number of equality atoms :   45 (  59 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(subsumption_resolution,[],[f122,f31])).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f122,plain,(
    k1_tarski(sK0) != k2_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f117,f74])).

fof(f74,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = X1 ),
    inference(forward_demodulation,[],[f73,f30])).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f73,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f70,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f70,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f35,f60])).

fof(f60,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f36,f30])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f117,plain,(
    k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f47,f115])).

fof(f115,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f114,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f114,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | sK0 = sK1 ),
    inference(superposition,[],[f111,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f111,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f47,f59])).

fof(f59,plain,(
    ! [X2,X1] :
      ( k2_xboole_0(X2,X1) = k5_xboole_0(X2,X1)
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(superposition,[],[f35,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f47,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f28,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f28,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f26])).

fof(f26,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:40:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (30849)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (30837)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (30834)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (30848)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (30835)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (30847)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (30837)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f122,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    k1_tarski(sK0) != k2_tarski(sK0,sK0)),
% 0.22/0.48    inference(forward_demodulation,[],[f117,f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) )),
% 0.22/0.48    inference(forward_demodulation,[],[f73,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X1] : (k2_xboole_0(X1,X1) = k4_xboole_0(X1,k1_xboole_0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f70,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ( ! [X1] : (k2_xboole_0(X1,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) )),
% 0.22/0.48    inference(superposition,[],[f35,f60])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.48    inference(superposition,[],[f36,f30])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.22/0.48    inference(backward_demodulation,[],[f47,f115])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    sK0 = sK1),
% 0.22/0.48    inference(subsumption_resolution,[],[f114,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.22/0.48    inference(ennf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,axiom,(
% 0.22/0.48    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | sK0 = sK1),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f113])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | sK0 = sK1),
% 0.22/0.48    inference(superposition,[],[f111,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.22/0.48    inference(ennf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,axiom,(
% 0.22/0.48    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.22/0.48    inference(superposition,[],[f47,f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k5_xboole_0(X2,X1) | ~r1_xboole_0(X1,X2)) )),
% 0.22/0.48    inference(superposition,[],[f35,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 0.22/0.48    inference(unused_predicate_definition_removal,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.48    inference(superposition,[],[f28,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.49    inference(negated_conjecture,[],[f18])).
% 0.22/0.49  fof(f18,conjecture,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (30837)------------------------------
% 0.22/0.49  % (30837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (30837)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (30837)Memory used [KB]: 1663
% 0.22/0.49  % (30837)Time elapsed: 0.062 s
% 0.22/0.49  % (30837)------------------------------
% 0.22/0.49  % (30837)------------------------------
% 0.22/0.49  % (30846)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (30833)Success in time 0.122 s
%------------------------------------------------------------------------------
