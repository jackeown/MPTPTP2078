%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  61 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   21
%              Number of atoms          :  102 ( 160 expanded)
%              Number of equality atoms :  101 ( 159 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f158,plain,(
    $false ),
    inference(subsumption_resolution,[],[f156,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f156,plain,(
    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f36,f88])).

fof(f88,plain,(
    k1_xboole_0 = k1_tarski(sK1) ),
    inference(condensation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tarski(sK1)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | k1_xboole_0 = k1_tarski(sK1)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f83,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k1_xboole_0) != k1_tarski(X1)
      | k1_xboole_0 = k1_tarski(sK1)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X5,X3] :
      ( k1_tarski(sK1) != k1_tarski(X3)
      | k1_xboole_0 = X4
      | k1_xboole_0 = k1_tarski(sK1)
      | k1_tarski(X5) != k2_xboole_0(X4,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f81,f23])).

fof(f81,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = X4
      | k1_xboole_0 = k1_tarski(sK1)
      | k1_tarski(sK1) != k1_tarski(X3)
      | k1_tarski(X5) != k2_xboole_0(X4,k4_xboole_0(k1_xboole_0,k1_tarski(sK1))) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = X4
      | k1_xboole_0 = k1_tarski(sK1)
      | k1_tarski(sK1) != k1_tarski(X3)
      | k1_xboole_0 = X4
      | k1_tarski(X5) != k2_xboole_0(X4,k4_xboole_0(k1_xboole_0,k1_tarski(sK1))) ) ),
    inference(forward_demodulation,[],[f79,f23])).

fof(f79,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k1_tarski(sK1)
      | k1_tarski(sK1) != k1_tarski(X3)
      | k1_xboole_0 = X4
      | k4_xboole_0(k1_xboole_0,k1_tarski(sK1)) = X4
      | k1_tarski(X5) != k2_xboole_0(X4,k4_xboole_0(k1_xboole_0,k1_tarski(sK1))) ) ),
    inference(forward_demodulation,[],[f77,f23])).

fof(f77,plain,(
    ! [X4,X5,X3] :
      ( k1_tarski(sK1) != k1_tarski(X3)
      | k1_tarski(sK1) = k4_xboole_0(k1_xboole_0,k1_tarski(sK1))
      | k1_xboole_0 = X4
      | k4_xboole_0(k1_xboole_0,k1_tarski(sK1)) = X4
      | k1_tarski(X5) != k2_xboole_0(X4,k4_xboole_0(k1_xboole_0,k1_tarski(sK1))) ) ),
    inference(superposition,[],[f49,f24])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tarski(X1) != k2_xboole_0(k1_tarski(sK1),X0)
      | k1_tarski(sK1) = k4_xboole_0(X0,k1_tarski(sK1))
      | k1_xboole_0 = X2
      | k4_xboole_0(X0,k1_tarski(sK1)) = X2
      | k1_tarski(X3) != k2_xboole_0(X2,k4_xboole_0(X0,k1_tarski(sK1))) ) ),
    inference(superposition,[],[f46,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tarski(X1) != k5_xboole_0(k1_tarski(sK1),X0)
      | k1_tarski(sK1) = X0
      | k1_xboole_0 = X2
      | X0 = X2
      | k1_tarski(X3) != k2_xboole_0(X2,X0) ) ),
    inference(superposition,[],[f44,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f44,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k5_xboole_0(k1_tarski(sK1),k1_xboole_0)
      | k1_xboole_0 = k1_tarski(sK1) ) ),
    inference(subsumption_resolution,[],[f43,f22])).

fof(f22,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK0 != k1_tarski(sK1)
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK0 != k1_tarski(sK1)
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f43,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k5_xboole_0(k1_tarski(sK1),k1_xboole_0)
      | k1_xboole_0 = k1_tarski(sK1)
      | sK0 = k1_tarski(sK1) ) ),
    inference(subsumption_resolution,[],[f42,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k5_xboole_0(k1_tarski(sK1),k1_xboole_0)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k1_tarski(sK1)
      | sK0 = k1_tarski(sK1) ) ),
    inference(superposition,[],[f35,f37])).

fof(f37,plain,(
    k2_xboole_0(k1_tarski(sK1),sK0) = k5_xboole_0(k1_tarski(sK1),k1_xboole_0) ),
    inference(superposition,[],[f30,f20])).

fof(f20,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:46:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (28005)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (27997)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (27989)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (27997)Refutation not found, incomplete strategy% (27997)------------------------------
% 0.21/0.51  % (27997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27997)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (27997)Memory used [KB]: 6268
% 0.21/0.51  % (27997)Time elapsed: 0.063 s
% 0.21/0.51  % (27997)------------------------------
% 0.21/0.51  % (27997)------------------------------
% 0.21/0.51  % (27982)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (27982)Refutation not found, incomplete strategy% (27982)------------------------------
% 0.21/0.51  % (27982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27982)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (27982)Memory used [KB]: 1663
% 0.21/0.51  % (27982)Time elapsed: 0.104 s
% 0.21/0.51  % (27982)------------------------------
% 0.21/0.51  % (27982)------------------------------
% 0.21/0.52  % (28005)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f156,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    inference(superposition,[],[f36,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    k1_xboole_0 = k1_tarski(sK1)),
% 0.21/0.52    inference(condensation,[],[f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_tarski(X1) != X0 | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(superposition,[],[f83,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,k1_xboole_0) != k1_tarski(X1) | k1_xboole_0 = k1_tarski(sK1) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(equality_resolution,[],[f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (k1_tarski(sK1) != k1_tarski(X3) | k1_xboole_0 = X4 | k1_xboole_0 = k1_tarski(sK1) | k1_tarski(X5) != k2_xboole_0(X4,k1_xboole_0)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f81,f23])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (k1_xboole_0 = X4 | k1_xboole_0 = k1_tarski(sK1) | k1_tarski(sK1) != k1_tarski(X3) | k1_tarski(X5) != k2_xboole_0(X4,k4_xboole_0(k1_xboole_0,k1_tarski(sK1)))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (k1_xboole_0 = X4 | k1_xboole_0 = k1_tarski(sK1) | k1_tarski(sK1) != k1_tarski(X3) | k1_xboole_0 = X4 | k1_tarski(X5) != k2_xboole_0(X4,k4_xboole_0(k1_xboole_0,k1_tarski(sK1)))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f79,f23])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (k1_xboole_0 = k1_tarski(sK1) | k1_tarski(sK1) != k1_tarski(X3) | k1_xboole_0 = X4 | k4_xboole_0(k1_xboole_0,k1_tarski(sK1)) = X4 | k1_tarski(X5) != k2_xboole_0(X4,k4_xboole_0(k1_xboole_0,k1_tarski(sK1)))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f77,f23])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (k1_tarski(sK1) != k1_tarski(X3) | k1_tarski(sK1) = k4_xboole_0(k1_xboole_0,k1_tarski(sK1)) | k1_xboole_0 = X4 | k4_xboole_0(k1_xboole_0,k1_tarski(sK1)) = X4 | k1_tarski(X5) != k2_xboole_0(X4,k4_xboole_0(k1_xboole_0,k1_tarski(sK1)))) )),
% 0.21/0.52    inference(superposition,[],[f49,f24])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k1_tarski(X1) != k2_xboole_0(k1_tarski(sK1),X0) | k1_tarski(sK1) = k4_xboole_0(X0,k1_tarski(sK1)) | k1_xboole_0 = X2 | k4_xboole_0(X0,k1_tarski(sK1)) = X2 | k1_tarski(X3) != k2_xboole_0(X2,k4_xboole_0(X0,k1_tarski(sK1)))) )),
% 0.21/0.52    inference(superposition,[],[f46,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k1_tarski(X1) != k5_xboole_0(k1_tarski(sK1),X0) | k1_tarski(sK1) = X0 | k1_xboole_0 = X2 | X0 = X2 | k1_tarski(X3) != k2_xboole_0(X2,X0)) )),
% 0.21/0.52    inference(superposition,[],[f44,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) != k5_xboole_0(k1_tarski(sK1),k1_xboole_0) | k1_xboole_0 = k1_tarski(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f43,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    sK0 != k1_tarski(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.52    inference(negated_conjecture,[],[f13])).
% 0.21/0.52  fof(f13,conjecture,(
% 0.21/0.52    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) != k5_xboole_0(k1_tarski(sK1),k1_xboole_0) | k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_tarski(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f42,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) != k5_xboole_0(k1_tarski(sK1),k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = k1_tarski(sK1) | sK0 = k1_tarski(sK1)) )),
% 0.21/0.52    inference(superposition,[],[f35,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    k2_xboole_0(k1_tarski(sK1),sK0) = k5_xboole_0(k1_tarski(sK1),k1_xboole_0)),
% 0.21/0.52    inference(superposition,[],[f30,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (28005)------------------------------
% 0.21/0.52  % (28005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28005)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (28005)Memory used [KB]: 1791
% 0.21/0.52  % (28005)Time elapsed: 0.068 s
% 0.21/0.52  % (28005)------------------------------
% 0.21/0.52  % (28005)------------------------------
% 0.21/0.52  % (27986)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (27981)Success in time 0.153 s
%------------------------------------------------------------------------------
