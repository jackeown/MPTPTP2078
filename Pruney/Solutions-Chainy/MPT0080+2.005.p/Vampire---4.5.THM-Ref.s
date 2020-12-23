%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  77 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :   77 ( 138 expanded)
%              Number of equality atoms :   33 (  45 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f545,plain,(
    $false ),
    inference(global_subsumption,[],[f22,f542])).

fof(f542,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f500,f210])).

fof(f210,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f136,f40])).

fof(f40,plain,(
    sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f28,f20])).

fof(f20,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).

% (13182)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f136,plain,(
    ! [X15] : k3_xboole_0(sK0,X15) = k3_xboole_0(sK0,k2_xboole_0(X15,sK2)) ),
    inference(forward_demodulation,[],[f135,f84])).

fof(f84,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f81,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f81,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f71,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f27,f55])).

fof(f55,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(X4,X4) ),
    inference(resolution,[],[f32,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f24,f23])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f135,plain,(
    ! [X15] : k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X15)) = k3_xboole_0(sK0,k2_xboole_0(X15,sK2)) ),
    inference(forward_demodulation,[],[f109,f26])).

fof(f109,plain,(
    ! [X15] : k3_xboole_0(sK0,k2_xboole_0(X15,sK2)) = k2_xboole_0(k3_xboole_0(sK0,X15),k1_xboole_0) ),
    inference(superposition,[],[f33,f50])).

fof(f50,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f500,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f460,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f460,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X2,X3),X2) ),
    inference(superposition,[],[f114,f42])).

fof(f42,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X3,X2)) = X2 ),
    inference(resolution,[],[f28,f35])).

fof(f35,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f24,f26])).

fof(f114,plain,(
    ! [X4,X2,X3] : r1_tarski(k3_xboole_0(X2,X3),k3_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f24,f33])).

fof(f22,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:49:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (13190)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.42  % (13189)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.42  % (13193)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.43  % (13186)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.43  % (13192)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.44  % (13186)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f545,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(global_subsumption,[],[f22,f542])).
% 0.20/0.44  fof(f542,plain,(
% 0.20/0.44    r1_tarski(sK0,sK1)),
% 0.20/0.44    inference(superposition,[],[f500,f210])).
% 0.20/0.44  fof(f210,plain,(
% 0.20/0.44    sK0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.44    inference(superposition,[],[f136,f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    sK0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.44    inference(resolution,[],[f28,f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).
% 0.20/0.44  % (13182)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.44    inference(flattening,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.20/0.44    inference(negated_conjecture,[],[f10])).
% 0.20/0.44  fof(f10,conjecture,(
% 0.20/0.44    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.44  fof(f136,plain,(
% 0.20/0.44    ( ! [X15] : (k3_xboole_0(sK0,X15) = k3_xboole_0(sK0,k2_xboole_0(X15,sK2))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f135,f84])).
% 0.20/0.44  fof(f84,plain,(
% 0.20/0.44    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.20/0.44    inference(superposition,[],[f81,f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.44  fof(f81,plain,(
% 0.20/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.44    inference(forward_demodulation,[],[f71,f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.44    inference(rectify,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.44  fof(f71,plain,(
% 0.20/0.44    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.44    inference(superposition,[],[f27,f55])).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(X4,X4)) )),
% 0.20/0.44    inference(resolution,[],[f32,f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.44    inference(superposition,[],[f24,f23])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.44    inference(nnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.44  fof(f135,plain,(
% 0.20/0.44    ( ! [X15] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X15)) = k3_xboole_0(sK0,k2_xboole_0(X15,sK2))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f109,f26])).
% 0.20/0.44  fof(f109,plain,(
% 0.20/0.44    ( ! [X15] : (k3_xboole_0(sK0,k2_xboole_0(X15,sK2)) = k2_xboole_0(k3_xboole_0(sK0,X15),k1_xboole_0)) )),
% 0.20/0.44    inference(superposition,[],[f33,f50])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.20/0.44    inference(resolution,[],[f29,f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    r1_xboole_0(sK0,sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.44    inference(nnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.20/0.44  fof(f500,plain,(
% 0.20/0.44    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 0.20/0.44    inference(superposition,[],[f460,f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.44  fof(f460,plain,(
% 0.20/0.44    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X2,X3),X2)) )),
% 0.20/0.44    inference(superposition,[],[f114,f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X3,X2)) = X2) )),
% 0.20/0.44    inference(resolution,[],[f28,f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 0.20/0.44    inference(superposition,[],[f24,f26])).
% 0.20/0.44  fof(f114,plain,(
% 0.20/0.44    ( ! [X4,X2,X3] : (r1_tarski(k3_xboole_0(X2,X3),k3_xboole_0(X2,k2_xboole_0(X3,X4)))) )),
% 0.20/0.44    inference(superposition,[],[f24,f33])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ~r1_tarski(sK0,sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (13186)------------------------------
% 0.20/0.44  % (13186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (13186)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (13186)Memory used [KB]: 6652
% 0.20/0.45  % (13186)Time elapsed: 0.019 s
% 0.20/0.45  % (13186)------------------------------
% 0.20/0.45  % (13186)------------------------------
% 0.20/0.45  % (13179)Success in time 0.092 s
%------------------------------------------------------------------------------
