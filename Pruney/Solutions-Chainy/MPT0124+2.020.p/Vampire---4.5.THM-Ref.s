%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 490 expanded)
%              Number of leaves         :    9 ( 144 expanded)
%              Depth                    :   22
%              Number of atoms          :   72 ( 752 expanded)
%              Number of equality atoms :   55 ( 456 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1689,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1674])).

fof(f1674,plain,(
    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f502,f1653])).

fof(f1653,plain,(
    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f1652,f527])).

fof(f527,plain,(
    ! [X5] : sK2 = k4_xboole_0(sK2,k4_xboole_0(X5,sK1)) ),
    inference(forward_demodulation,[],[f492,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f23,f20])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f492,plain,(
    ! [X5] : k4_xboole_0(sK2,k4_xboole_0(X5,sK1)) = k2_xboole_0(k4_xboole_0(sK2,X5),sK2) ),
    inference(superposition,[],[f26,f30])).

fof(f30,plain,(
    sK2 = k3_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f21,f28])).

fof(f28,plain,(
    sK1 = k2_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f23,f17])).

fof(f17,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f1652,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f1598,f94])).

fof(f94,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f22,f85])).

fof(f85,plain,(
    sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f24,f17])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1598,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f524,f363])).

fof(f363,plain,(
    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f341,f280])).

fof(f280,plain,(
    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f261,f91])).

fof(f91,plain,(
    sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))) ),
    inference(resolution,[],[f24,f37])).

fof(f37,plain,(
    r1_tarski(k4_xboole_0(sK1,sK1),sK2) ),
    inference(superposition,[],[f20,f32])).

fof(f32,plain,(
    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f22,f28])).

fof(f261,plain,(
    ! [X1] : k4_xboole_0(sK2,X1) = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X1)) ),
    inference(superposition,[],[f29,f257])).

fof(f257,plain,(
    ! [X0] : k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK2,X0),sK1) ),
    inference(forward_demodulation,[],[f256,f32])).

fof(f256,plain,(
    ! [X0] : k4_xboole_0(sK2,sK1) = k4_xboole_0(k4_xboole_0(sK2,X0),sK1) ),
    inference(forward_demodulation,[],[f250,f229])).

fof(f229,plain,(
    ! [X5] : k3_xboole_0(sK2,k4_xboole_0(sK1,X5)) = k4_xboole_0(sK2,X5) ),
    inference(superposition,[],[f25,f30])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f250,plain,(
    ! [X0] : k4_xboole_0(k4_xboole_0(sK2,X0),sK1) = k3_xboole_0(sK2,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f246,f33])).

fof(f33,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f22,f29])).

fof(f246,plain,(
    ! [X0,X1] : k3_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X0),X1)) = k4_xboole_0(k4_xboole_0(sK2,X0),X1) ),
    inference(superposition,[],[f25,f229])).

fof(f341,plain,(
    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f336,f123])).

fof(f123,plain,(
    k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f22,f91])).

fof(f336,plain,(
    ! [X1] : k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),X1) ),
    inference(superposition,[],[f230,f262])).

fof(f262,plain,(
    ! [X2] : k4_xboole_0(sK1,sK1) = k3_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X2)) ),
    inference(superposition,[],[f31,f257])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f21,f29])).

fof(f230,plain,(
    ! [X6] : k3_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X6)) = k4_xboole_0(k4_xboole_0(sK1,sK1),X6) ),
    inference(superposition,[],[f25,f40])).

fof(f40,plain,(
    k4_xboole_0(sK1,sK1) = k3_xboole_0(k4_xboole_0(sK1,sK1),sK2) ),
    inference(superposition,[],[f21,f36])).

fof(f36,plain,(
    sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),sK2) ),
    inference(superposition,[],[f29,f32])).

fof(f524,plain,(
    ! [X23] : k4_xboole_0(sK2,k4_xboole_0(sK2,X23)) = k4_xboole_0(sK2,k4_xboole_0(sK1,X23)) ),
    inference(forward_demodulation,[],[f489,f486])).

fof(f486,plain,(
    ! [X20] : k4_xboole_0(sK2,k4_xboole_0(sK1,X20)) = k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK2,X20)) ),
    inference(superposition,[],[f26,f32])).

fof(f489,plain,(
    ! [X23] : k4_xboole_0(sK2,k4_xboole_0(sK2,X23)) = k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK2,X23)) ),
    inference(superposition,[],[f26,f363])).

fof(f502,plain,(
    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f18,f26])).

fof(f18,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:07:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.41  % (12012)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.45  % (12011)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.45  % (12009)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.45  % (12010)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.48  % (12009)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f1689,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f1674])).
% 0.21/0.48  fof(f1674,plain,(
% 0.21/0.48    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2)),
% 0.21/0.48    inference(superposition,[],[f502,f1653])).
% 0.21/0.48  fof(f1653,plain,(
% 0.21/0.48    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 0.21/0.48    inference(forward_demodulation,[],[f1652,f527])).
% 0.21/0.48  fof(f527,plain,(
% 0.21/0.48    ( ! [X5] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(X5,sK1))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f492,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 0.21/0.48    inference(resolution,[],[f23,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.48  fof(f492,plain,(
% 0.21/0.48    ( ! [X5] : (k4_xboole_0(sK2,k4_xboole_0(X5,sK1)) = k2_xboole_0(k4_xboole_0(sK2,X5),sK2)) )),
% 0.21/0.48    inference(superposition,[],[f26,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    sK2 = k3_xboole_0(sK2,sK1)),
% 0.21/0.48    inference(superposition,[],[f21,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    sK1 = k2_xboole_0(sK2,sK1)),
% 0.21/0.48    inference(resolution,[],[f23,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    r1_tarski(sK2,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.21/0.48  fof(f1652,plain,(
% 0.21/0.48    k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 0.21/0.48    inference(forward_demodulation,[],[f1598,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 0.21/0.48    inference(superposition,[],[f22,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 0.21/0.48    inference(resolution,[],[f24,f17])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.48  fof(f1598,plain,(
% 0.21/0.48    k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 0.21/0.48    inference(superposition,[],[f524,f363])).
% 0.21/0.48  fof(f363,plain,(
% 0.21/0.48    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK2,sK2)),
% 0.21/0.48    inference(forward_demodulation,[],[f341,f280])).
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))),
% 0.21/0.48    inference(superposition,[],[f261,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)))),
% 0.21/0.48    inference(resolution,[],[f24,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    r1_tarski(k4_xboole_0(sK1,sK1),sK2)),
% 0.21/0.48    inference(superposition,[],[f20,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK1,sK1)),
% 0.21/0.48    inference(superposition,[],[f22,f28])).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    ( ! [X1] : (k4_xboole_0(sK2,X1) = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X1))) )),
% 0.21/0.48    inference(superposition,[],[f29,f257])).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK2,X0),sK1)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f256,f32])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(sK2,sK1) = k4_xboole_0(k4_xboole_0(sK2,X0),sK1)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f250,f229])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    ( ! [X5] : (k3_xboole_0(sK2,k4_xboole_0(sK1,X5)) = k4_xboole_0(sK2,X5)) )),
% 0.21/0.48    inference(superposition,[],[f25,f30])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK2,X0),sK1) = k3_xboole_0(sK2,k4_xboole_0(sK1,sK1))) )),
% 0.21/0.48    inference(superposition,[],[f246,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(X1,X1)) )),
% 0.21/0.48    inference(superposition,[],[f22,f29])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,X0),X1)) = k4_xboole_0(k4_xboole_0(sK2,X0),X1)) )),
% 0.21/0.48    inference(superposition,[],[f25,f229])).
% 0.21/0.48  fof(f341,plain,(
% 0.21/0.48    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)))),
% 0.21/0.48    inference(superposition,[],[f336,f123])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,sK1)))),
% 0.21/0.48    inference(superposition,[],[f22,f91])).
% 0.21/0.48  fof(f336,plain,(
% 0.21/0.48    ( ! [X1] : (k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),X1)) )),
% 0.21/0.48    inference(superposition,[],[f230,f262])).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    ( ! [X2] : (k4_xboole_0(sK1,sK1) = k3_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X2))) )),
% 0.21/0.48    inference(superposition,[],[f31,f257])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.48    inference(superposition,[],[f21,f29])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    ( ! [X6] : (k3_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK2,X6)) = k4_xboole_0(k4_xboole_0(sK1,sK1),X6)) )),
% 0.21/0.48    inference(superposition,[],[f25,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    k4_xboole_0(sK1,sK1) = k3_xboole_0(k4_xboole_0(sK1,sK1),sK2)),
% 0.21/0.48    inference(superposition,[],[f21,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    sK2 = k2_xboole_0(k4_xboole_0(sK1,sK1),sK2)),
% 0.21/0.48    inference(superposition,[],[f29,f32])).
% 0.21/0.48  fof(f524,plain,(
% 0.21/0.48    ( ! [X23] : (k4_xboole_0(sK2,k4_xboole_0(sK2,X23)) = k4_xboole_0(sK2,k4_xboole_0(sK1,X23))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f489,f486])).
% 0.21/0.48  fof(f486,plain,(
% 0.21/0.48    ( ! [X20] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X20)) = k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK2,X20))) )),
% 0.21/0.48    inference(superposition,[],[f26,f32])).
% 0.21/0.48  fof(f489,plain,(
% 0.21/0.48    ( ! [X23] : (k4_xboole_0(sK2,k4_xboole_0(sK2,X23)) = k2_xboole_0(k4_xboole_0(sK1,sK1),k3_xboole_0(sK2,X23))) )),
% 0.21/0.48    inference(superposition,[],[f26,f363])).
% 0.21/0.48  fof(f502,plain,(
% 0.21/0.48    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.21/0.48    inference(superposition,[],[f18,f26])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (12009)------------------------------
% 0.21/0.48  % (12009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12009)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (12009)Memory used [KB]: 7164
% 0.21/0.48  % (12009)Time elapsed: 0.033 s
% 0.21/0.48  % (12009)------------------------------
% 0.21/0.48  % (12009)------------------------------
% 0.21/0.48  % (12004)Success in time 0.128 s
%------------------------------------------------------------------------------
