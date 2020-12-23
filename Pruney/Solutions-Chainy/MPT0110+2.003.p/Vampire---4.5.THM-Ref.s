%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:29 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :   46 (  82 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :   15
%              Number of atoms          :   56 ( 104 expanded)
%              Number of equality atoms :   33 (  62 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(resolution,[],[f182,f30])).

fof(f30,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f18,f24])).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f18,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
   => ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

% (24741)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_xboole_1)).

fof(f182,plain,(
    ! [X2,X3] : r1_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(trivial_inequality_removal,[],[f175])).

fof(f175,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X2,k4_xboole_0(X3,X2)) ) ),
    inference(superposition,[],[f27,f157])).

fof(f157,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f131,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f131,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X6,X7),X6) ),
    inference(superposition,[],[f104,f35])).

fof(f35,plain,(
    ! [X4,X3] : k2_xboole_0(k3_xboole_0(X3,X4),X3) = X3 ),
    inference(resolution,[],[f25,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f104,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f89,f37])).

fof(f37,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f35,f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f29,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f46,f50])).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f49,f35])).

fof(f49,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k2_xboole_0(k3_xboole_0(X0,X0),X0) ),
    inference(forward_demodulation,[],[f48,f20])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(k3_xboole_0(X0,X0),X0) = k2_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) ),
    inference(superposition,[],[f23,f46])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f31,f34])).

fof(f34,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = X2 ),
    inference(resolution,[],[f25,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f21,f20])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X0,X0),k3_xboole_0(X0,X0)) ),
    inference(definition_unfolding,[],[f19,f24])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (813957123)
% 0.14/0.38  ipcrm: permission denied for id (813989901)
% 0.21/0.42  ipcrm: permission denied for id (814121006)
% 0.21/0.46  ipcrm: permission denied for id (814186572)
% 0.21/0.46  ipcrm: permission denied for id (814219341)
% 0.21/0.47  ipcrm: permission denied for id (814284879)
% 0.21/0.49  ipcrm: permission denied for id (814317666)
% 0.90/0.62  % (24745)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.90/0.62  % (24750)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.90/0.63  % (24745)Refutation found. Thanks to Tanya!
% 0.90/0.63  % SZS status Theorem for theBenchmark
% 0.90/0.63  % (24732)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.90/0.64  % (24734)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.90/0.64  % (24748)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.90/0.64  % SZS output start Proof for theBenchmark
% 0.90/0.64  fof(f188,plain,(
% 0.90/0.64    $false),
% 0.90/0.64    inference(resolution,[],[f182,f30])).
% 0.90/0.64  fof(f30,plain,(
% 0.90/0.64    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 0.90/0.64    inference(definition_unfolding,[],[f18,f24])).
% 0.90/0.64  fof(f24,plain,(
% 0.90/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.90/0.64    inference(cnf_transformation,[],[f2])).
% 0.90/0.64  fof(f2,axiom,(
% 0.90/0.64    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.90/0.64  fof(f18,plain,(
% 0.90/0.64    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.90/0.64    inference(cnf_transformation,[],[f16])).
% 0.90/0.64  fof(f16,plain,(
% 0.90/0.64    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.90/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).
% 0.90/0.64  fof(f15,plain,(
% 0.90/0.64    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) => ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.90/0.64    introduced(choice_axiom,[])).
% 0.90/0.64  fof(f13,plain,(
% 0.90/0.64    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.90/0.64    inference(ennf_transformation,[],[f12])).
% 0.90/0.64  % (24741)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.90/0.64  fof(f12,negated_conjecture,(
% 0.90/0.64    ~! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.90/0.64    inference(negated_conjecture,[],[f11])).
% 0.90/0.64  fof(f11,conjecture,(
% 0.90/0.64    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_xboole_1)).
% 0.90/0.64  fof(f182,plain,(
% 0.90/0.64    ( ! [X2,X3] : (r1_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 0.90/0.64    inference(trivial_inequality_removal,[],[f175])).
% 0.90/0.64  fof(f175,plain,(
% 0.90/0.64    ( ! [X2,X3] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 0.90/0.64    inference(superposition,[],[f27,f157])).
% 0.90/0.64  fof(f157,plain,(
% 0.90/0.64    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.90/0.64    inference(superposition,[],[f131,f28])).
% 0.90/0.64  fof(f28,plain,(
% 0.90/0.64    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.90/0.64    inference(cnf_transformation,[],[f7])).
% 0.90/0.64  fof(f7,axiom,(
% 0.90/0.64    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.90/0.64  fof(f131,plain,(
% 0.90/0.64    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X6,X7),X6)) )),
% 0.90/0.64    inference(superposition,[],[f104,f35])).
% 0.90/0.64  fof(f35,plain,(
% 0.90/0.64    ( ! [X4,X3] : (k2_xboole_0(k3_xboole_0(X3,X4),X3) = X3) )),
% 0.90/0.64    inference(resolution,[],[f25,f22])).
% 0.90/0.64  fof(f22,plain,(
% 0.90/0.64    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.90/0.64    inference(cnf_transformation,[],[f4])).
% 0.90/0.64  fof(f4,axiom,(
% 0.90/0.64    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.90/0.64  fof(f25,plain,(
% 0.90/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.90/0.64    inference(cnf_transformation,[],[f14])).
% 0.90/0.64  fof(f14,plain,(
% 0.90/0.64    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.90/0.64    inference(ennf_transformation,[],[f3])).
% 0.90/0.64  fof(f3,axiom,(
% 0.90/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.90/0.64  fof(f104,plain,(
% 0.90/0.64    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.90/0.64    inference(forward_demodulation,[],[f89,f37])).
% 0.90/0.64  fof(f37,plain,(
% 0.90/0.64    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 0.90/0.64    inference(superposition,[],[f35,f20])).
% 0.90/0.64  fof(f20,plain,(
% 0.90/0.64    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.90/0.64    inference(cnf_transformation,[],[f5])).
% 0.90/0.64  fof(f5,axiom,(
% 0.90/0.64    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.90/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.12/0.64  fof(f89,plain,(
% 1.12/0.64    ( ! [X0,X1] : (k3_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.12/0.64    inference(superposition,[],[f29,f51])).
% 1.12/0.64  fof(f51,plain,(
% 1.12/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.12/0.64    inference(backward_demodulation,[],[f46,f50])).
% 1.12/0.64  fof(f50,plain,(
% 1.12/0.64    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.12/0.64    inference(forward_demodulation,[],[f49,f35])).
% 1.12/0.64  fof(f49,plain,(
% 1.12/0.64    ( ! [X0] : (k3_xboole_0(X0,X0) = k2_xboole_0(k3_xboole_0(X0,X0),X0)) )),
% 1.12/0.64    inference(forward_demodulation,[],[f48,f20])).
% 1.12/0.64  fof(f48,plain,(
% 1.12/0.64    ( ! [X0] : (k2_xboole_0(k3_xboole_0(X0,X0),X0) = k2_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0)) )),
% 1.12/0.64    inference(superposition,[],[f23,f46])).
% 1.12/0.64  fof(f23,plain,(
% 1.12/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.12/0.64    inference(cnf_transformation,[],[f6])).
% 1.12/0.64  fof(f6,axiom,(
% 1.12/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.12/0.64  fof(f46,plain,(
% 1.12/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.12/0.64    inference(forward_demodulation,[],[f31,f34])).
% 1.12/0.64  fof(f34,plain,(
% 1.12/0.64    ( ! [X2] : (k2_xboole_0(X2,X2) = X2) )),
% 1.12/0.64    inference(resolution,[],[f25,f32])).
% 1.12/0.64  fof(f32,plain,(
% 1.12/0.64    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.12/0.64    inference(superposition,[],[f21,f20])).
% 1.12/0.64  fof(f21,plain,(
% 1.12/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.12/0.64    inference(cnf_transformation,[],[f9])).
% 1.12/0.64  fof(f9,axiom,(
% 1.12/0.64    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.12/0.64  fof(f31,plain,(
% 1.12/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X0,X0),k3_xboole_0(X0,X0))) )),
% 1.12/0.64    inference(definition_unfolding,[],[f19,f24])).
% 1.12/0.64  fof(f19,plain,(
% 1.12/0.64    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.12/0.64    inference(cnf_transformation,[],[f10])).
% 1.12/0.64  fof(f10,axiom,(
% 1.12/0.64    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.12/0.64  fof(f29,plain,(
% 1.12/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 1.12/0.64    inference(cnf_transformation,[],[f8])).
% 1.12/0.64  fof(f8,axiom,(
% 1.12/0.64    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 1.12/0.64  fof(f27,plain,(
% 1.12/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.12/0.64    inference(cnf_transformation,[],[f17])).
% 1.12/0.64  fof(f17,plain,(
% 1.12/0.64    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.12/0.64    inference(nnf_transformation,[],[f1])).
% 1.12/0.64  fof(f1,axiom,(
% 1.12/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.12/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.12/0.64  % SZS output end Proof for theBenchmark
% 1.12/0.64  % (24745)------------------------------
% 1.12/0.64  % (24745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.12/0.64  % (24745)Termination reason: Refutation
% 1.12/0.64  
% 1.12/0.64  % (24745)Memory used [KB]: 1663
% 1.12/0.64  % (24745)Time elapsed: 0.058 s
% 1.12/0.64  % (24745)------------------------------
% 1.12/0.64  % (24745)------------------------------
% 1.12/0.64  % (24511)Success in time 0.284 s
%------------------------------------------------------------------------------
