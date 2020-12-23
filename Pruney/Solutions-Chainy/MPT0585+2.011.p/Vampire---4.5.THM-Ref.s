%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 169 expanded)
%              Number of leaves         :    9 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :   92 ( 444 expanded)
%              Number of equality atoms :   40 ( 175 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f759,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f750])).

fof(f750,plain,(
    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f52,f728])).

fof(f728,plain,(
    ! [X1] : k7_relat_1(sK0,X1) = k7_relat_1(sK0,k3_xboole_0(X1,k1_relat_1(sK0))) ),
    inference(superposition,[],[f268,f102])).

fof(f102,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),X0)) ),
    inference(superposition,[],[f71,f40])).

fof(f40,plain,(
    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(resolution,[],[f31,f28])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f71,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f37,f28])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f268,plain,(
    ! [X6] : k7_relat_1(sK0,X6) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),k3_xboole_0(X6,k1_relat_1(sK0)))) ),
    inference(backward_demodulation,[],[f190,f258])).

fof(f258,plain,(
    ! [X0,X1] : k3_xboole_0(k1_relat_1(sK0),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(k1_relat_1(sK0),X0),X1) ),
    inference(forward_demodulation,[],[f257,f49])).

fof(f49,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0) ),
    inference(resolution,[],[f35,f28])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f257,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(sK0,k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(k1_relat_1(sK0),X0),X1) ),
    inference(forward_demodulation,[],[f256,f71])).

fof(f256,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1)) = k3_xboole_0(k3_xboole_0(k1_relat_1(sK0),X0),X1) ),
    inference(forward_demodulation,[],[f253,f49])).

fof(f253,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1)) = k3_xboole_0(k1_relat_1(k7_relat_1(sK0,X0)),X1) ),
    inference(resolution,[],[f51,f28])).

fof(f51,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | k1_relat_1(k7_relat_1(k7_relat_1(X2,X3),X4)) = k3_xboole_0(k1_relat_1(k7_relat_1(X2,X3)),X4) ) ),
    inference(resolution,[],[f35,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f190,plain,(
    ! [X6] : k7_relat_1(sK0,k3_xboole_0(k3_xboole_0(k1_relat_1(sK0),X6),k1_relat_1(sK0))) = k7_relat_1(sK0,X6) ),
    inference(forward_demodulation,[],[f185,f102])).

fof(f185,plain,(
    ! [X6] : k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),X6)) = k7_relat_1(sK0,k3_xboole_0(k3_xboole_0(k1_relat_1(sK0),X6),k1_relat_1(sK0))) ),
    inference(resolution,[],[f139,f70])).

fof(f70,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(k1_relat_1(sK0),X0),k1_relat_1(sK0)) ),
    inference(resolution,[],[f54,f28])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK0)
      | r1_tarski(k3_xboole_0(k1_relat_1(sK0),X0),k1_relat_1(sK0)) ) ),
    inference(superposition,[],[f34,f49])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k7_relat_1(sK0,X0) = k7_relat_1(sK0,k3_xboole_0(X0,X1)) ) ),
    inference(forward_demodulation,[],[f136,f71])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),X1) ) ),
    inference(resolution,[],[f39,f28])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f52,plain,(
    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))) ),
    inference(backward_demodulation,[],[f30,f50])).

fof(f50,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(k1_relat_1(sK1),X1) ),
    inference(resolution,[],[f35,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f30,plain,(
    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:42:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.43  % (19694)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.45  % (19711)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.45  % (19702)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.47  % (19712)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.49  % (19692)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.49  % (19702)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f759,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f750])).
% 0.20/0.49  fof(f750,plain,(
% 0.20/0.49    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(sK1))),
% 0.20/0.49    inference(superposition,[],[f52,f728])).
% 0.20/0.49  fof(f728,plain,(
% 0.20/0.49    ( ! [X1] : (k7_relat_1(sK0,X1) = k7_relat_1(sK0,k3_xboole_0(X1,k1_relat_1(sK0)))) )),
% 0.20/0.49    inference(superposition,[],[f268,f102])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),X0))) )),
% 0.20/0.49    inference(superposition,[],[f71,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.49    inference(resolution,[],[f31,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    v1_relat_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    (k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f26,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0)))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ? [X1] : (k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0)))) & v1_relat_1(X1)) => (k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) & v1_relat_1(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(resolution,[],[f37,f28])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.20/0.49  fof(f268,plain,(
% 0.20/0.49    ( ! [X6] : (k7_relat_1(sK0,X6) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),k3_xboole_0(X6,k1_relat_1(sK0))))) )),
% 0.20/0.49    inference(backward_demodulation,[],[f190,f258])).
% 0.20/0.49  fof(f258,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(sK0),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(k1_relat_1(sK0),X0),X1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f257,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k7_relat_1(sK0,X0)) = k3_xboole_0(k1_relat_1(sK0),X0)) )),
% 0.20/0.49    inference(resolution,[],[f35,f28])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 0.20/0.49  fof(f257,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(sK0,k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(k1_relat_1(sK0),X0),X1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f256,f71])).
% 0.20/0.49  fof(f256,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1)) = k3_xboole_0(k3_xboole_0(k1_relat_1(sK0),X0),X1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f253,f49])).
% 0.20/0.49  fof(f253,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1)) = k3_xboole_0(k1_relat_1(k7_relat_1(sK0,X0)),X1)) )),
% 0.20/0.49    inference(resolution,[],[f51,f28])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k1_relat_1(k7_relat_1(k7_relat_1(X2,X3),X4)) = k3_xboole_0(k1_relat_1(k7_relat_1(X2,X3)),X4)) )),
% 0.20/0.49    inference(resolution,[],[f35,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    ( ! [X6] : (k7_relat_1(sK0,k3_xboole_0(k3_xboole_0(k1_relat_1(sK0),X6),k1_relat_1(sK0))) = k7_relat_1(sK0,X6)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f185,f102])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    ( ! [X6] : (k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),X6)) = k7_relat_1(sK0,k3_xboole_0(k3_xboole_0(k1_relat_1(sK0),X6),k1_relat_1(sK0)))) )),
% 0.20/0.49    inference(resolution,[],[f139,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k3_xboole_0(k1_relat_1(sK0),X0),k1_relat_1(sK0))) )),
% 0.20/0.49    inference(resolution,[],[f54,f28])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(sK0) | r1_tarski(k3_xboole_0(k1_relat_1(sK0),X0),k1_relat_1(sK0))) )),
% 0.20/0.49    inference(superposition,[],[f34,f49])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK0,X0) = k7_relat_1(sK0,k3_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f136,f71])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),X1)) )),
% 0.20/0.49    inference(resolution,[],[f39,f28])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))),
% 0.20/0.49    inference(backward_demodulation,[],[f30,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(k1_relat_1(sK1),X1)) )),
% 0.20/0.49    inference(resolution,[],[f35,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    v1_relat_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (19702)------------------------------
% 0.20/0.49  % (19702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (19702)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (19702)Memory used [KB]: 2046
% 0.20/0.49  % (19702)Time elapsed: 0.095 s
% 0.20/0.49  % (19702)------------------------------
% 0.20/0.49  % (19702)------------------------------
% 0.20/0.49  % (19695)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (19688)Success in time 0.143 s
%------------------------------------------------------------------------------
