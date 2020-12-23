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
% DateTime   : Thu Dec  3 12:30:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 392 expanded)
%              Number of leaves         :    9 ( 113 expanded)
%              Depth                    :   21
%              Number of atoms          :   91 ( 890 expanded)
%              Number of equality atoms :   70 ( 543 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f263,plain,(
    $false ),
    inference(subsumption_resolution,[],[f262,f19])).

% (7926)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f19,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f262,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f261,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f261,plain,(
    sK2 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f260,f255])).

fof(f255,plain,(
    sK2 = k3_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f252,f20])).

fof(f252,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f228,f251])).

fof(f251,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f245,f63])).

fof(f63,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f62,f37])).

fof(f37,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f30,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f30,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f18,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f18,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    k3_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f23,f50])).

fof(f50,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f49,f20])).

fof(f49,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f24,f37])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f245,plain,(
    k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(superposition,[],[f115,f72])).

fof(f72,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f28,f63])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f115,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f61,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f61,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[],[f28,f50])).

fof(f228,plain,(
    k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,sK3)) = k3_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f227,f21])).

fof(f227,plain,(
    k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,sK3)) = k3_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f225,f91])).

fof(f91,plain,(
    ! [X2] : k3_xboole_0(sK2,k2_xboole_0(sK0,X2)) = k3_xboole_0(sK2,X2) ),
    inference(forward_demodulation,[],[f89,f23])).

fof(f89,plain,(
    ! [X2] : k3_xboole_0(sK2,k2_xboole_0(sK0,X2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X2)) ),
    inference(superposition,[],[f23,f45])).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f28,f36])).

fof(f36,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f33,f20])).

fof(f33,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f24,f29])).

fof(f29,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f17,f26])).

fof(f17,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f225,plain,(
    k3_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,sK3)) ),
    inference(superposition,[],[f23,f109])).

fof(f109,plain,(
    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f58,f16])).

fof(f16,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f28,f48])).

fof(f48,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f47,f31])).

fof(f31,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f29,f21])).

fof(f47,plain,(
    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f46,f21])).

fof(f46,plain,(
    k3_xboole_0(sK2,sK0) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f23,f36])).

fof(f260,plain,(
    k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f23,f250])).

fof(f250,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f249,f132])).

fof(f132,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f128,f48])).

fof(f128,plain,(
    k4_xboole_0(sK2,sK2) = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[],[f86,f58])).

fof(f86,plain,(
    ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k2_xboole_0(X0,sK0)) ),
    inference(superposition,[],[f45,f22])).

fof(f249,plain,(
    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f244,f189])).

fof(f189,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f72,f22])).

fof(f244,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f115,f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (7946)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (7938)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (7938)Refutation not found, incomplete strategy% (7938)------------------------------
% 0.21/0.50  % (7938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7938)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (7938)Memory used [KB]: 6140
% 0.21/0.50  % (7938)Time elapsed: 0.003 s
% 0.21/0.50  % (7938)------------------------------
% 0.21/0.50  % (7938)------------------------------
% 0.21/0.50  % (7928)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (7930)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (7946)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f263,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f262,f19])).
% 0.21/0.51  % (7926)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    sK1 != sK2),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    sK1 = sK2),
% 0.21/0.51    inference(forward_demodulation,[],[f261,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    sK2 = k4_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.51    inference(forward_demodulation,[],[f260,f255])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    sK2 = k3_xboole_0(sK1,sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f252,f20])).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    k4_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK1,sK2)),
% 0.21/0.51    inference(backward_demodulation,[],[f228,f251])).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3)),
% 0.21/0.51    inference(forward_demodulation,[],[f245,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 0.21/0.51    inference(forward_demodulation,[],[f62,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 0.21/0.51    inference(superposition,[],[f30,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(sK3,sK1)),
% 0.21/0.51    inference(resolution,[],[f18,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    r1_xboole_0(sK3,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    k3_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK1)),
% 0.21/0.51    inference(superposition,[],[f23,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    sK1 = k4_xboole_0(sK1,sK3)),
% 0.21/0.51    inference(forward_demodulation,[],[f49,f20])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.51    inference(superposition,[],[f24,f37])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_xboole_0,sK3)),
% 0.21/0.51    inference(superposition,[],[f115,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(sK1,X0))) )),
% 0.21/0.51    inference(superposition,[],[f28,f63])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK3))) )),
% 0.21/0.51    inference(superposition,[],[f61,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0)) )),
% 0.21/0.51    inference(superposition,[],[f28,f50])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,sK3)) = k3_xboole_0(sK1,sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f227,f21])).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,sK3)) = k3_xboole_0(sK2,sK1)),
% 0.21/0.51    inference(forward_demodulation,[],[f225,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X2] : (k3_xboole_0(sK2,k2_xboole_0(sK0,X2)) = k3_xboole_0(sK2,X2)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f89,f23])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X2] : (k3_xboole_0(sK2,k2_xboole_0(sK0,X2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,X2))) )),
% 0.21/0.51    inference(superposition,[],[f23,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 0.21/0.51    inference(superposition,[],[f28,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    sK2 = k4_xboole_0(sK2,sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f33,f20])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 0.21/0.51    inference(superposition,[],[f24,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(sK2,sK0)),
% 0.21/0.51    inference(resolution,[],[f17,f26])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    r1_xboole_0(sK2,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    k3_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,sK3))),
% 0.21/0.51    inference(superposition,[],[f23,f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 0.21/0.51    inference(superposition,[],[f58,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(superposition,[],[f28,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f47,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.21/0.51    inference(superposition,[],[f29,f21])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK2,sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f46,f21])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    k3_xboole_0(sK2,sK0) = k4_xboole_0(sK2,sK2)),
% 0.21/0.51    inference(superposition,[],[f23,f36])).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    k4_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,sK2)),
% 0.21/0.51    inference(superposition,[],[f23,f250])).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f249,f132])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f128,f48])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    k4_xboole_0(sK2,sK2) = k4_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.51    inference(superposition,[],[f86,f58])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k2_xboole_0(X0,sK0))) )),
% 0.21/0.51    inference(superposition,[],[f45,f22])).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(sK1,sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f244,f189])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK1))) )),
% 0.21/0.51    inference(superposition,[],[f72,f22])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 0.21/0.51    inference(superposition,[],[f115,f16])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (7946)------------------------------
% 0.21/0.51  % (7946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7946)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (7946)Memory used [KB]: 1918
% 0.21/0.51  % (7946)Time elapsed: 0.058 s
% 0.21/0.51  % (7946)------------------------------
% 0.21/0.51  % (7946)------------------------------
% 0.21/0.52  % (7922)Success in time 0.154 s
%------------------------------------------------------------------------------
