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
% DateTime   : Thu Dec  3 12:51:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 102 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 241 expanded)
%              Number of equality atoms :   28 (  72 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f315,plain,(
    $false ),
    inference(subsumption_resolution,[],[f314,f290])).

fof(f290,plain,(
    ! [X17] : r1_xboole_0(k4_xboole_0(X17,sK1),sK0) ),
    inference(resolution,[],[f279,f67])).

fof(f67,plain,(
    ! [X0] : r1_xboole_0(sK0,k4_xboole_0(X0,sK1)) ),
    inference(resolution,[],[f39,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f39,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

fof(f279,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(forward_demodulation,[],[f270,f89])).

fof(f89,plain,(
    ! [X1] : k4_xboole_0(X1,k4_xboole_0(sK0,sK1)) = X1 ),
    inference(resolution,[],[f84,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f84,plain,(
    ! [X0] : r1_xboole_0(X0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f67,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f270,plain,(
    ! [X6,X7] :
      ( r1_xboole_0(X7,X6)
      | ~ r1_xboole_0(X6,k4_xboole_0(X7,k4_xboole_0(sK0,sK1))) ) ),
    inference(superposition,[],[f59,f89])).

fof(f314,plain,(
    ~ r1_xboole_0(k4_xboole_0(k1_relat_1(sK2),sK1),sK0) ),
    inference(forward_demodulation,[],[f313,f66])).

fof(f66,plain,(
    ! [X2] : k4_xboole_0(k1_relat_1(sK2),X2) = k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X2))) ),
    inference(forward_demodulation,[],[f65,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f65,plain,(
    ! [X2] : k1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X2))) = k4_xboole_0(k1_relat_1(sK2),X2) ),
    inference(forward_demodulation,[],[f63,f44])).

fof(f63,plain,(
    ! [X2] : k1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X2))) = k6_subset_1(k1_relat_1(sK2),X2) ),
    inference(resolution,[],[f38,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

fof(f38,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f313,plain,(
    ~ r1_xboole_0(k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))),sK0) ),
    inference(subsumption_resolution,[],[f310,f64])).

fof(f64,plain,(
    ! [X3] : v1_relat_1(k4_xboole_0(sK2,X3)) ),
    inference(resolution,[],[f38,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f310,plain,
    ( ~ r1_xboole_0(k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))) ),
    inference(trivial_inequality_removal,[],[f309])).

fof(f309,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))),sK0)
    | ~ v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))) ),
    inference(superposition,[],[f60,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f60,plain,(
    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(forward_demodulation,[],[f40,f44])).

fof(f40,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:35:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (28537)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (28529)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (28514)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (28521)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (28525)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (28524)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (28537)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f315,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f314,f290])).
% 0.22/0.52  fof(f290,plain,(
% 0.22/0.52    ( ! [X17] : (r1_xboole_0(k4_xboole_0(X17,sK1),sK0)) )),
% 0.22/0.52    inference(resolution,[],[f279,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X0] : (r1_xboole_0(sK0,k4_xboole_0(X0,sK1))) )),
% 0.22/0.52    inference(resolution,[],[f39,f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    r1_tarski(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f15])).
% 0.22/0.52  fof(f15,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).
% 0.22/0.52  fof(f279,plain,(
% 0.22/0.52    ( ! [X6,X7] : (~r1_xboole_0(X6,X7) | r1_xboole_0(X7,X6)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f270,f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(sK0,sK1)) = X1) )),
% 0.22/0.52    inference(resolution,[],[f84,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(sK0,sK1))) )),
% 0.22/0.52    inference(resolution,[],[f67,f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.22/0.52  fof(f270,plain,(
% 0.22/0.52    ( ! [X6,X7] : (r1_xboole_0(X7,X6) | ~r1_xboole_0(X6,k4_xboole_0(X7,k4_xboole_0(sK0,sK1)))) )),
% 0.22/0.52    inference(superposition,[],[f59,f89])).
% 0.22/0.52  fof(f314,plain,(
% 0.22/0.52    ~r1_xboole_0(k4_xboole_0(k1_relat_1(sK2),sK1),sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f313,f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X2] : (k4_xboole_0(k1_relat_1(sK2),X2) = k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X2)))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f65,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X2] : (k1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X2))) = k4_xboole_0(k1_relat_1(sK2),X2)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f63,f44])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X2] : (k1_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X2))) = k6_subset_1(k1_relat_1(sK2),X2)) )),
% 0.22/0.52    inference(resolution,[],[f38,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    v1_relat_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f313,plain,(
% 0.22/0.52    ~r1_xboole_0(k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))),sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f310,f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X3] : (v1_relat_1(k4_xboole_0(sK2,X3))) )),
% 0.22/0.52    inference(resolution,[],[f38,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.22/0.52  fof(f310,plain,(
% 0.22/0.52    ~r1_xboole_0(k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))),sK0) | ~v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f309])).
% 0.22/0.52  fof(f309,plain,(
% 0.22/0.52    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))),sK0) | ~v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))),
% 0.22/0.52    inference(superposition,[],[f60,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f40,f44])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (28537)------------------------------
% 0.22/0.52  % (28537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28537)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (28537)Memory used [KB]: 1918
% 0.22/0.52  % (28537)Time elapsed: 0.065 s
% 0.22/0.52  % (28537)------------------------------
% 0.22/0.52  % (28537)------------------------------
% 0.22/0.52  % (28526)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (28513)Success in time 0.165 s
%------------------------------------------------------------------------------
