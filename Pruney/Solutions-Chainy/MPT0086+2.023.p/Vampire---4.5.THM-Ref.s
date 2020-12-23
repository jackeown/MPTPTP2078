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
% DateTime   : Thu Dec  3 12:31:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  56 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :   41 (  63 expanded)
%              Number of equality atoms :   28 (  50 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f50])).

fof(f50,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f44,f42])).

fof(f42,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f34,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f34,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f20,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f21,f15])).

fof(f15,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f14,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f20,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f44,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f43,f17])).

fof(f43,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f35,f33])).

fof(f33,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0)) ),
    inference(superposition,[],[f20,f15])).

fof(f35,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0)))) ),
    inference(superposition,[],[f28,f20])).

fof(f28,plain,(
    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f27,f25])).

fof(f25,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f17,f24])).

fof(f27,plain,(
    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f26,f20])).

fof(f26,plain,(
    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) ),
    inference(resolution,[],[f22,f13])).

fof(f13,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1)
   => ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f19,f16])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:18:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (24944)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (24945)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (24945)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    k1_xboole_0 != k1_xboole_0),
% 0.21/0.46    inference(superposition,[],[f44,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 0.21/0.46    inference(forward_demodulation,[],[f34,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 0.21/0.46    inference(superposition,[],[f20,f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.46    inference(backward_demodulation,[],[f21,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f14,f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))),
% 0.21/0.46    inference(forward_demodulation,[],[f43,f17])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 0.21/0.46    inference(forward_demodulation,[],[f35,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))) )),
% 0.21/0.46    inference(superposition,[],[f20,f15])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0))))),
% 0.21/0.46    inference(superposition,[],[f28,f20])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,k1_xboole_0)))),
% 0.21/0.46    inference(forward_demodulation,[],[f27,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.46    inference(superposition,[],[f17,f24])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK1,sK1)))),
% 0.21/0.46    inference(forward_demodulation,[],[f26,f20])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),
% 0.21/0.46    inference(resolution,[],[f22,f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1) => ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.46    inference(negated_conjecture,[],[f7])).
% 0.21/0.46  fof(f7,conjecture,(
% 0.21/0.46    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f19,f16])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (24945)------------------------------
% 0.21/0.46  % (24945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (24945)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (24945)Memory used [KB]: 1663
% 0.21/0.46  % (24945)Time elapsed: 0.061 s
% 0.21/0.46  % (24945)------------------------------
% 0.21/0.46  % (24945)------------------------------
% 0.21/0.47  % (24960)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (24946)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (24962)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (24947)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (24951)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (24952)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (24941)Success in time 0.121 s
%------------------------------------------------------------------------------
