%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:14 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   45 (  67 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 131 expanded)
%              Number of equality atoms :   43 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(subsumption_resolution,[],[f33,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f79,f63])).

fof(f63,plain,(
    k1_xboole_0 = k8_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f62,f35])).

fof(f35,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f62,plain,(
    k1_xboole_0 = k8_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f61,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

fof(f61,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f60,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f60,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f55,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f58,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f45,f42])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f79,plain,(
    ! [X0] : k8_relat_1(k1_xboole_0,k1_xboole_0) = k8_relat_1(X0,k8_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f78,f61])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(k1_xboole_0,X0) = k8_relat_1(X1,k8_relat_1(k1_xboole_0,X0)) ) ),
    inference(resolution,[],[f47,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f33,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f27])).

fof(f27,plain,
    ( ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)
   => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : run_vampire %s %d
% 0.11/0.31  % Computer   : n014.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 16:20:07 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.17/0.42  % (11509)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.17/0.43  % (11501)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.17/0.43  % (11501)Refutation found. Thanks to Tanya!
% 0.17/0.43  % SZS status Theorem for theBenchmark
% 0.17/0.43  % SZS output start Proof for theBenchmark
% 0.17/0.43  fof(f83,plain,(
% 0.17/0.43    $false),
% 0.17/0.43    inference(subsumption_resolution,[],[f33,f82])).
% 0.17/0.43  fof(f82,plain,(
% 0.17/0.43    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) )),
% 0.17/0.43    inference(forward_demodulation,[],[f79,f63])).
% 0.17/0.43  fof(f63,plain,(
% 0.17/0.43    k1_xboole_0 = k8_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.17/0.43    inference(forward_demodulation,[],[f62,f35])).
% 0.17/0.43  fof(f35,plain,(
% 0.17/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.17/0.43    inference(cnf_transformation,[],[f17])).
% 0.17/0.43  fof(f17,axiom,(
% 0.17/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.17/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.17/0.43  fof(f62,plain,(
% 0.17/0.43    k1_xboole_0 = k8_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.17/0.43    inference(resolution,[],[f61,f39])).
% 0.17/0.43  fof(f39,plain,(
% 0.17/0.43    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0) )),
% 0.17/0.43    inference(cnf_transformation,[],[f23])).
% 0.17/0.43  fof(f23,plain,(
% 0.17/0.43    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 0.17/0.43    inference(ennf_transformation,[],[f15])).
% 0.17/0.43  fof(f15,axiom,(
% 0.17/0.43    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.17/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).
% 0.17/0.43  fof(f61,plain,(
% 0.17/0.43    v1_relat_1(k1_xboole_0)),
% 0.17/0.43    inference(resolution,[],[f60,f40])).
% 0.17/0.43  fof(f40,plain,(
% 0.17/0.43    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 0.17/0.43    inference(cnf_transformation,[],[f30])).
% 0.17/0.43  fof(f30,plain,(
% 0.17/0.43    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 0.17/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f29])).
% 0.17/0.43  fof(f29,plain,(
% 0.17/0.43    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 0.17/0.43    introduced(choice_axiom,[])).
% 0.17/0.43  fof(f24,plain,(
% 0.17/0.43    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.17/0.43    inference(ennf_transformation,[],[f21])).
% 0.17/0.43  fof(f21,plain,(
% 0.17/0.43    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.17/0.43    inference(unused_predicate_definition_removal,[],[f14])).
% 0.17/0.43  fof(f14,axiom,(
% 0.17/0.43    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.17/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.17/0.43  fof(f60,plain,(
% 0.17/0.43    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.17/0.43    inference(superposition,[],[f55,f59])).
% 0.17/0.43  fof(f59,plain,(
% 0.17/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.17/0.43    inference(forward_demodulation,[],[f58,f37])).
% 0.17/0.43  fof(f37,plain,(
% 0.17/0.43    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.17/0.43    inference(cnf_transformation,[],[f4])).
% 0.17/0.43  fof(f4,axiom,(
% 0.17/0.43    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.17/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.17/0.43  fof(f58,plain,(
% 0.17/0.43    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 0.17/0.43    inference(superposition,[],[f45,f42])).
% 0.17/0.43  fof(f42,plain,(
% 0.17/0.43    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.17/0.43    inference(cnf_transformation,[],[f20])).
% 0.17/0.43  fof(f20,plain,(
% 0.17/0.43    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.17/0.43    inference(rectify,[],[f1])).
% 0.17/0.43  fof(f1,axiom,(
% 0.17/0.43    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.17/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.17/0.43  fof(f45,plain,(
% 0.17/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.17/0.43    inference(cnf_transformation,[],[f2])).
% 0.17/0.43  fof(f2,axiom,(
% 0.17/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.17/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.17/0.43  fof(f55,plain,(
% 0.17/0.43    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.17/0.43    inference(equality_resolution,[],[f49])).
% 0.17/0.43  fof(f49,plain,(
% 0.17/0.43    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.17/0.43    inference(cnf_transformation,[],[f32])).
% 0.17/0.43  fof(f32,plain,(
% 0.17/0.43    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.17/0.43    inference(flattening,[],[f31])).
% 0.17/0.43  fof(f31,plain,(
% 0.17/0.43    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.17/0.43    inference(nnf_transformation,[],[f12])).
% 0.17/0.43  fof(f12,axiom,(
% 0.17/0.43    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.17/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.17/0.43  fof(f79,plain,(
% 0.17/0.43    ( ! [X0] : (k8_relat_1(k1_xboole_0,k1_xboole_0) = k8_relat_1(X0,k8_relat_1(k1_xboole_0,k1_xboole_0))) )),
% 0.17/0.43    inference(resolution,[],[f78,f61])).
% 0.17/0.43  fof(f78,plain,(
% 0.17/0.43    ( ! [X0,X1] : (~v1_relat_1(X0) | k8_relat_1(k1_xboole_0,X0) = k8_relat_1(X1,k8_relat_1(k1_xboole_0,X0))) )),
% 0.17/0.43    inference(resolution,[],[f47,f36])).
% 0.17/0.43  fof(f36,plain,(
% 0.17/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.17/0.43    inference(cnf_transformation,[],[f3])).
% 0.17/0.43  fof(f3,axiom,(
% 0.17/0.43    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.17/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.17/0.43  fof(f47,plain,(
% 0.17/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) )),
% 0.17/0.43    inference(cnf_transformation,[],[f26])).
% 0.17/0.43  fof(f26,plain,(
% 0.17/0.43    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.17/0.43    inference(flattening,[],[f25])).
% 0.17/0.43  fof(f25,plain,(
% 0.17/0.43    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.17/0.43    inference(ennf_transformation,[],[f16])).
% 0.17/0.43  fof(f16,axiom,(
% 0.17/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.17/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 0.17/0.43  fof(f33,plain,(
% 0.17/0.43    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.17/0.43    inference(cnf_transformation,[],[f28])).
% 0.17/0.43  fof(f28,plain,(
% 0.17/0.43    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.17/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f27])).
% 0.17/0.43  fof(f27,plain,(
% 0.17/0.43    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.17/0.43    introduced(choice_axiom,[])).
% 0.17/0.43  fof(f22,plain,(
% 0.17/0.43    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.17/0.43    inference(ennf_transformation,[],[f19])).
% 0.17/0.43  fof(f19,negated_conjecture,(
% 0.17/0.43    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.17/0.43    inference(negated_conjecture,[],[f18])).
% 0.17/0.43  fof(f18,conjecture,(
% 0.17/0.43    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.17/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
% 0.17/0.43  % SZS output end Proof for theBenchmark
% 0.17/0.43  % (11501)------------------------------
% 0.17/0.43  % (11501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.43  % (11501)Termination reason: Refutation
% 0.17/0.43  
% 0.17/0.43  % (11501)Memory used [KB]: 6268
% 0.17/0.43  % (11501)Time elapsed: 0.057 s
% 0.17/0.43  % (11501)------------------------------
% 0.17/0.43  % (11501)------------------------------
% 0.17/0.43  % (11493)Success in time 0.109 s
%------------------------------------------------------------------------------
