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
% DateTime   : Thu Dec  3 12:39:55 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   45 (  98 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   17
%              Number of atoms          :   63 ( 141 expanded)
%              Number of equality atoms :   36 (  70 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(subsumption_resolution,[],[f99,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f99,plain,(
    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f64,f94])).

fof(f94,plain,(
    k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    inference(superposition,[],[f91,f43])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f91,plain,(
    k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f89,f90])).

fof(f90,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f85,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f85,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f83,f38])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f83,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f51,f81])).

fof(f81,plain,(
    k1_xboole_0 = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f79,f39])).

fof(f39,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f79,plain,(
    k3_tarski(k1_xboole_0) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f47,f75])).

fof(f75,plain,(
    k1_xboole_0 = k2_tarski(sK0,sK1) ),
    inference(resolution,[],[f71,f44])).

fof(f71,plain,(
    v1_xboole_0(k2_tarski(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f69,f38])).

fof(f69,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f51,f37])).

fof(f37,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X0,X1))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_xboole_0)).

fof(f89,plain,(
    k1_xboole_0 = k2_tarski(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f75,f86])).

fof(f86,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f84,f44])).

fof(f84,plain,(
    v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f82,f38])).

fof(f82,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f52,f81])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

fof(f64,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

% (8535)Refutation not found, incomplete strategy% (8535)------------------------------
% (8535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f24,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:49:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (8547)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (8542)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.52  % (8564)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.25/0.53  % (8535)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.53  % (8542)Refutation found. Thanks to Tanya!
% 1.25/0.53  % SZS status Theorem for theBenchmark
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.53  fof(f100,plain,(
% 1.25/0.53    $false),
% 1.25/0.53    inference(subsumption_resolution,[],[f99,f40])).
% 1.25/0.53  fof(f40,plain,(
% 1.25/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f8])).
% 1.25/0.53  fof(f8,axiom,(
% 1.25/0.53    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.25/0.53  fof(f99,plain,(
% 1.25/0.53    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.25/0.53    inference(superposition,[],[f64,f94])).
% 1.25/0.53  fof(f94,plain,(
% 1.25/0.53    k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 1.25/0.53    inference(superposition,[],[f91,f43])).
% 1.25/0.53  fof(f43,plain,(
% 1.25/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f16])).
% 1.25/0.53  fof(f16,axiom,(
% 1.25/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.25/0.53  fof(f91,plain,(
% 1.25/0.53    k1_xboole_0 = k2_tarski(k1_xboole_0,k1_xboole_0)),
% 1.25/0.53    inference(backward_demodulation,[],[f89,f90])).
% 1.25/0.53  fof(f90,plain,(
% 1.25/0.53    k1_xboole_0 = sK0),
% 1.25/0.53    inference(resolution,[],[f85,f44])).
% 1.25/0.53  fof(f44,plain,(
% 1.25/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.25/0.53    inference(cnf_transformation,[],[f31])).
% 1.25/0.53  fof(f31,plain,(
% 1.25/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f4])).
% 1.25/0.53  fof(f4,axiom,(
% 1.25/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.25/0.53  fof(f85,plain,(
% 1.25/0.53    v1_xboole_0(sK0)),
% 1.25/0.53    inference(subsumption_resolution,[],[f83,f38])).
% 1.25/0.53  fof(f38,plain,(
% 1.25/0.53    v1_xboole_0(k1_xboole_0)),
% 1.25/0.53    inference(cnf_transformation,[],[f1])).
% 1.25/0.53  fof(f1,axiom,(
% 1.25/0.53    v1_xboole_0(k1_xboole_0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.25/0.53  fof(f83,plain,(
% 1.25/0.53    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK0)),
% 1.25/0.53    inference(superposition,[],[f51,f81])).
% 1.25/0.53  fof(f81,plain,(
% 1.25/0.53    k1_xboole_0 = k2_xboole_0(sK0,sK1)),
% 1.25/0.53    inference(forward_demodulation,[],[f79,f39])).
% 1.25/0.53  fof(f39,plain,(
% 1.25/0.53    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.25/0.53    inference(cnf_transformation,[],[f25])).
% 1.25/0.53  fof(f25,axiom,(
% 1.25/0.53    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 1.25/0.53  fof(f79,plain,(
% 1.25/0.53    k3_tarski(k1_xboole_0) = k2_xboole_0(sK0,sK1)),
% 1.25/0.53    inference(superposition,[],[f47,f75])).
% 1.25/0.53  fof(f75,plain,(
% 1.25/0.53    k1_xboole_0 = k2_tarski(sK0,sK1)),
% 1.25/0.53    inference(resolution,[],[f71,f44])).
% 1.25/0.53  fof(f71,plain,(
% 1.25/0.53    v1_xboole_0(k2_tarski(sK0,sK1))),
% 1.25/0.53    inference(subsumption_resolution,[],[f69,f38])).
% 1.25/0.53  fof(f69,plain,(
% 1.25/0.53    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_tarski(sK0,sK1))),
% 1.25/0.53    inference(superposition,[],[f51,f37])).
% 1.25/0.53  fof(f37,plain,(
% 1.25/0.53    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.25/0.53    inference(cnf_transformation,[],[f35])).
% 1.25/0.53  fof(f35,plain,(
% 1.25/0.53    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.25/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34])).
% 1.25/0.53  fof(f34,plain,(
% 1.25/0.53    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.25/0.53    introduced(choice_axiom,[])).
% 1.25/0.53  fof(f30,plain,(
% 1.25/0.53    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.25/0.53    inference(ennf_transformation,[],[f27])).
% 1.25/0.53  fof(f27,negated_conjecture,(
% 1.25/0.53    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.25/0.53    inference(negated_conjecture,[],[f26])).
% 1.25/0.53  fof(f26,conjecture,(
% 1.25/0.53    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 1.25/0.53  fof(f47,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f23])).
% 1.25/0.53  fof(f23,axiom,(
% 1.25/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.25/0.53  fof(f51,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X0,X1)) | v1_xboole_0(X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f32])).
% 1.25/0.53  fof(f32,plain,(
% 1.25/0.53    ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X0,X1)) | v1_xboole_0(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f5])).
% 1.25/0.53  fof(f5,axiom,(
% 1.25/0.53    ! [X0,X1] : (~v1_xboole_0(X0) => ~v1_xboole_0(k2_xboole_0(X0,X1)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_xboole_0)).
% 1.25/0.53  fof(f89,plain,(
% 1.25/0.53    k1_xboole_0 = k2_tarski(sK0,k1_xboole_0)),
% 1.25/0.53    inference(backward_demodulation,[],[f75,f86])).
% 1.25/0.53  fof(f86,plain,(
% 1.25/0.53    k1_xboole_0 = sK1),
% 1.25/0.53    inference(resolution,[],[f84,f44])).
% 1.25/0.53  fof(f84,plain,(
% 1.25/0.53    v1_xboole_0(sK1)),
% 1.25/0.53    inference(subsumption_resolution,[],[f82,f38])).
% 1.25/0.53  fof(f82,plain,(
% 1.25/0.53    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK1)),
% 1.25/0.53    inference(superposition,[],[f52,f81])).
% 1.25/0.53  fof(f52,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | v1_xboole_0(X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f33])).
% 1.25/0.53  fof(f33,plain,(
% 1.25/0.53    ! [X0,X1] : (~v1_xboole_0(k2_xboole_0(X1,X0)) | v1_xboole_0(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f6])).
% 1.25/0.53  fof(f6,axiom,(
% 1.25/0.53    ! [X0,X1] : (~v1_xboole_0(X0) => ~v1_xboole_0(k2_xboole_0(X1,X0)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).
% 1.25/0.53  fof(f64,plain,(
% 1.25/0.53    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 1.25/0.53    inference(equality_resolution,[],[f53])).
% 1.25/0.53  fof(f53,plain,(
% 1.25/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f36])).
% 1.25/0.53  fof(f36,plain,(
% 1.25/0.53    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.25/0.53    inference(nnf_transformation,[],[f24])).
% 1.25/0.53  % (8535)Refutation not found, incomplete strategy% (8535)------------------------------
% 1.25/0.53  % (8535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  fof(f24,axiom,(
% 1.25/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.25/0.53  % SZS output end Proof for theBenchmark
% 1.25/0.53  % (8542)------------------------------
% 1.25/0.53  % (8542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (8542)Termination reason: Refutation
% 1.25/0.53  
% 1.25/0.53  % (8542)Memory used [KB]: 6268
% 1.25/0.53  % (8542)Time elapsed: 0.107 s
% 1.25/0.53  % (8542)------------------------------
% 1.25/0.53  % (8542)------------------------------
% 1.25/0.53  % (8534)Success in time 0.165 s
%------------------------------------------------------------------------------
