%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:49 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   56 (  87 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   98 ( 155 expanded)
%              Number of equality atoms :   57 (  89 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(subsumption_resolution,[],[f36,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f88,f76])).

fof(f76,plain,(
    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f64,f74])).

fof(f74,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f59,f73])).

fof(f73,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_tarski(X3),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f71,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f71,plain,(
    ! [X3] : k4_xboole_0(k1_tarski(X3),k1_tarski(X3)) = k5_xboole_0(k1_tarski(X3),k1_tarski(X3)) ),
    inference(superposition,[],[f49,f66])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f48,f41])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f64,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_tarski(sK1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f63,f37])).

fof(f37,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f63,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | k1_xboole_0 = k1_tarski(sK1(k1_xboole_0)) ),
    inference(resolution,[],[f42,f62])).

fof(f62,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_tarski(sK1(k1_xboole_0)) ),
    inference(resolution,[],[f61,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK1(X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f61,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(resolution,[],[f50,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f88,plain,(
    ! [X0] : k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0),X0) ),
    inference(resolution,[],[f87,f39])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k7_relat_1(k1_xboole_0,X0) = k7_relat_1(k7_relat_1(k1_xboole_0,X0),X1) ) ),
    inference(resolution,[],[f54,f77])).

fof(f77,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f62,f74])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f36,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f31])).

fof(f31,plain,
    ( ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (3407)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (3399)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (3389)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (3407)Refutation not found, incomplete strategy% (3407)------------------------------
% 0.20/0.52  % (3407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3390)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (3407)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (3407)Memory used [KB]: 10618
% 0.20/0.52  % (3407)Time elapsed: 0.061 s
% 0.20/0.52  % (3407)------------------------------
% 0.20/0.52  % (3407)------------------------------
% 1.24/0.52  % (3391)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.24/0.52  % (3391)Refutation found. Thanks to Tanya!
% 1.24/0.52  % SZS status Theorem for theBenchmark
% 1.24/0.52  % SZS output start Proof for theBenchmark
% 1.24/0.52  fof(f91,plain,(
% 1.24/0.52    $false),
% 1.24/0.52    inference(subsumption_resolution,[],[f36,f90])).
% 1.24/0.52  fof(f90,plain,(
% 1.24/0.52    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 1.24/0.52    inference(forward_demodulation,[],[f88,f76])).
% 1.24/0.52  fof(f76,plain,(
% 1.24/0.52    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.24/0.52    inference(subsumption_resolution,[],[f64,f74])).
% 1.24/0.52  fof(f74,plain,(
% 1.24/0.52    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 1.24/0.52    inference(backward_demodulation,[],[f59,f73])).
% 1.24/0.52  fof(f73,plain,(
% 1.24/0.52    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X3),k1_tarski(X3))) )),
% 1.24/0.52    inference(forward_demodulation,[],[f71,f40])).
% 1.24/0.52  fof(f40,plain,(
% 1.24/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f4])).
% 1.24/0.52  fof(f4,axiom,(
% 1.24/0.52    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.24/0.52  fof(f71,plain,(
% 1.24/0.52    ( ! [X3] : (k4_xboole_0(k1_tarski(X3),k1_tarski(X3)) = k5_xboole_0(k1_tarski(X3),k1_tarski(X3))) )),
% 1.24/0.52    inference(superposition,[],[f49,f66])).
% 1.24/0.52  fof(f66,plain,(
% 1.24/0.52    ( ! [X0] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 1.24/0.52    inference(superposition,[],[f48,f41])).
% 1.24/0.52  fof(f41,plain,(
% 1.24/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f5])).
% 1.24/0.52  fof(f5,axiom,(
% 1.24/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.24/0.52  fof(f48,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.24/0.52    inference(cnf_transformation,[],[f13])).
% 1.24/0.52  fof(f13,axiom,(
% 1.24/0.52    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 1.24/0.52  fof(f49,plain,(
% 1.24/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.24/0.52    inference(cnf_transformation,[],[f1])).
% 1.24/0.52  fof(f1,axiom,(
% 1.24/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.24/0.52  fof(f59,plain,(
% 1.24/0.52    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 1.24/0.52    inference(equality_resolution,[],[f51])).
% 1.24/0.52  fof(f51,plain,(
% 1.24/0.52    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.24/0.52    inference(cnf_transformation,[],[f35])).
% 1.24/0.52  fof(f35,plain,(
% 1.24/0.52    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.24/0.52    inference(nnf_transformation,[],[f14])).
% 1.24/0.52  fof(f14,axiom,(
% 1.24/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.24/0.52  fof(f64,plain,(
% 1.24/0.52    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_tarski(sK1(k1_xboole_0))),
% 1.24/0.52    inference(forward_demodulation,[],[f63,f37])).
% 1.24/0.52  fof(f37,plain,(
% 1.24/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.24/0.52    inference(cnf_transformation,[],[f18])).
% 1.24/0.52  fof(f18,axiom,(
% 1.24/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.24/0.52  fof(f63,plain,(
% 1.24/0.52    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | k1_xboole_0 = k1_tarski(sK1(k1_xboole_0))),
% 1.24/0.52    inference(resolution,[],[f42,f62])).
% 1.24/0.52  fof(f62,plain,(
% 1.24/0.52    v1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_tarski(sK1(k1_xboole_0))),
% 1.24/0.52    inference(resolution,[],[f61,f44])).
% 1.24/0.52  fof(f44,plain,(
% 1.24/0.52    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f34])).
% 1.24/0.52  fof(f34,plain,(
% 1.24/0.52    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f33])).
% 1.24/0.52  fof(f33,plain,(
% 1.24/0.52    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK1(X0) & r2_hidden(sK1(X0),X0)))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f27,plain,(
% 1.24/0.52    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.24/0.52    inference(ennf_transformation,[],[f22])).
% 1.24/0.52  fof(f22,plain,(
% 1.24/0.52    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 1.24/0.52    inference(unused_predicate_definition_removal,[],[f16])).
% 1.24/0.52  fof(f16,axiom,(
% 1.24/0.52    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.24/0.52  fof(f61,plain,(
% 1.24/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.24/0.52    inference(resolution,[],[f50,f43])).
% 1.24/0.52  fof(f43,plain,(
% 1.24/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.24/0.52    inference(cnf_transformation,[],[f26])).
% 1.24/0.52  fof(f26,plain,(
% 1.24/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.24/0.52    inference(ennf_transformation,[],[f3])).
% 1.24/0.52  fof(f3,axiom,(
% 1.24/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.24/0.52  fof(f50,plain,(
% 1.24/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f28])).
% 1.24/0.52  fof(f28,plain,(
% 1.24/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 1.24/0.52    inference(ennf_transformation,[],[f23])).
% 1.24/0.52  fof(f23,plain,(
% 1.24/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 1.24/0.52    inference(unused_predicate_definition_removal,[],[f12])).
% 1.24/0.52  fof(f12,axiom,(
% 1.24/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.24/0.52  fof(f42,plain,(
% 1.24/0.52    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 1.24/0.52    inference(cnf_transformation,[],[f25])).
% 1.24/0.52  fof(f25,plain,(
% 1.24/0.52    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.24/0.52    inference(ennf_transformation,[],[f19])).
% 1.24/0.52  fof(f19,axiom,(
% 1.24/0.52    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 1.24/0.52  fof(f88,plain,(
% 1.24/0.52    ( ! [X0] : (k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0),X0)) )),
% 1.24/0.52    inference(resolution,[],[f87,f39])).
% 1.24/0.52  fof(f39,plain,(
% 1.24/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f2])).
% 1.24/0.52  fof(f2,axiom,(
% 1.24/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.24/0.52  fof(f87,plain,(
% 1.24/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(k1_xboole_0,X0) = k7_relat_1(k7_relat_1(k1_xboole_0,X0),X1)) )),
% 1.24/0.52    inference(resolution,[],[f54,f77])).
% 1.24/0.52  fof(f77,plain,(
% 1.24/0.52    v1_relat_1(k1_xboole_0)),
% 1.24/0.52    inference(subsumption_resolution,[],[f62,f74])).
% 1.24/0.52  fof(f54,plain,(
% 1.24/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f30])).
% 1.24/0.52  fof(f30,plain,(
% 1.24/0.52    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.24/0.52    inference(flattening,[],[f29])).
% 1.24/0.52  fof(f29,plain,(
% 1.24/0.52    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.24/0.52    inference(ennf_transformation,[],[f17])).
% 1.24/0.52  fof(f17,axiom,(
% 1.24/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 1.24/0.52  fof(f36,plain,(
% 1.24/0.52    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 1.24/0.52    inference(cnf_transformation,[],[f32])).
% 1.24/0.52  fof(f32,plain,(
% 1.24/0.52    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f31])).
% 1.24/0.52  fof(f31,plain,(
% 1.24/0.52    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f24,plain,(
% 1.24/0.52    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)),
% 1.24/0.52    inference(ennf_transformation,[],[f21])).
% 1.24/0.52  fof(f21,negated_conjecture,(
% 1.24/0.52    ~! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 1.24/0.52    inference(negated_conjecture,[],[f20])).
% 1.24/0.52  fof(f20,conjecture,(
% 1.24/0.52    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 1.24/0.52  % SZS output end Proof for theBenchmark
% 1.24/0.52  % (3391)------------------------------
% 1.24/0.52  % (3391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (3391)Termination reason: Refutation
% 1.24/0.52  
% 1.24/0.52  % (3391)Memory used [KB]: 6268
% 1.24/0.52  % (3391)Time elapsed: 0.111 s
% 1.24/0.52  % (3391)------------------------------
% 1.24/0.52  % (3391)------------------------------
% 1.24/0.52  % (3383)Success in time 0.162 s
%------------------------------------------------------------------------------
