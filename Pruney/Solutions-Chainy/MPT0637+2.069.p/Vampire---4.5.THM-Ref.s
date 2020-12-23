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
% DateTime   : Thu Dec  3 12:52:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 (  88 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :   83 ( 148 expanded)
%              Number of equality atoms :   42 (  60 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1367,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1366,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f1366,plain,(
    ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1363,f85])).

fof(f85,plain,(
    ! [X2,X1] : k8_relat_1(X2,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),X1) ),
    inference(subsumption_resolution,[],[f84,f42])).

fof(f84,plain,(
    ! [X2,X1] :
      ( k8_relat_1(X2,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),X1)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f75,f42])).

fof(f75,plain,(
    ! [X2,X1] :
      ( k8_relat_1(X2,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),X1)
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f53,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f1363,plain,
    ( k8_relat_1(sK0,k6_relat_1(sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f1310,f52])).

fof(f1310,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f40,f1290])).

fof(f1290,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3)) ),
    inference(subsumption_resolution,[],[f1264,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1264,plain,(
    ! [X2,X3] :
      ( k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3))
      | ~ r1_tarski(k3_xboole_0(X2,X3),X2) ) ),
    inference(superposition,[],[f129,f194])).

fof(f194,plain,(
    ! [X4,X3] :
      ( k6_relat_1(X4) = k7_relat_1(k6_relat_1(X3),X4)
      | ~ r1_tarski(X4,X3) ) ),
    inference(forward_demodulation,[],[f193,f44])).

fof(f44,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f193,plain,(
    ! [X4,X3] :
      ( k6_relat_1(X4) = k7_relat_1(k6_relat_1(X3),X4)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X4)),X3) ) ),
    inference(subsumption_resolution,[],[f185,f42])).

fof(f185,plain,(
    ! [X4,X3] :
      ( k6_relat_1(X4) = k7_relat_1(k6_relat_1(X3),X4)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X4)),X3)
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(superposition,[],[f85,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f129,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    inference(subsumption_resolution,[],[f125,f42])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f60,f83])).

fof(f83,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f82,f44])).

fof(f82,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0) ),
    inference(subsumption_resolution,[],[f81,f42])).

fof(f81,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f74,f42])).

fof(f74,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f53,f45])).

fof(f45,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f40,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f38])).

fof(f38,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:15:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (20432)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.44  % (20425)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.45  % (20428)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (20416)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (20429)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (20422)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (20436)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (20431)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (20430)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (20426)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (20427)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (20419)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (20434)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (20439)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (20437)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (20438)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (20433)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.51  % (20433)Refutation not found, incomplete strategy% (20433)------------------------------
% 0.20/0.51  % (20433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (20433)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (20433)Memory used [KB]: 10618
% 0.20/0.51  % (20433)Time elapsed: 0.103 s
% 0.20/0.51  % (20433)------------------------------
% 0.20/0.51  % (20433)------------------------------
% 0.20/0.51  % (20435)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.53  % (20425)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f1367,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f1366,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f19])).
% 0.20/0.53  fof(f19,axiom,(
% 0.20/0.53    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.53  fof(f1366,plain,(
% 0.20/0.53    ~v1_relat_1(k6_relat_1(sK1))),
% 0.20/0.53    inference(subsumption_resolution,[],[f1363,f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X2,X1] : (k8_relat_1(X2,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),X1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f84,f42])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X2,X1] : (k8_relat_1(X2,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),X1) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f75,f42])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X2,X1] : (k8_relat_1(X2,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X2),X1) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.20/0.53    inference(superposition,[],[f53,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.53  fof(f1363,plain,(
% 0.20/0.53    k8_relat_1(sK0,k6_relat_1(sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.20/0.53    inference(superposition,[],[f1310,f52])).
% 0.20/0.53  fof(f1310,plain,(
% 0.20/0.53    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.20/0.53    inference(backward_demodulation,[],[f40,f1290])).
% 0.20/0.53  fof(f1290,plain,(
% 0.20/0.53    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f1264,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.53  fof(f1264,plain,(
% 0.20/0.53    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k6_relat_1(k3_xboole_0(X2,X3)) | ~r1_tarski(k3_xboole_0(X2,X3),X2)) )),
% 0.20/0.53    inference(superposition,[],[f129,f194])).
% 0.20/0.53  fof(f194,plain,(
% 0.20/0.53    ( ! [X4,X3] : (k6_relat_1(X4) = k7_relat_1(k6_relat_1(X3),X4) | ~r1_tarski(X4,X3)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f193,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    ( ! [X4,X3] : (k6_relat_1(X4) = k7_relat_1(k6_relat_1(X3),X4) | ~r1_tarski(k2_relat_1(k6_relat_1(X4)),X3)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f185,f42])).
% 0.20/0.53  fof(f185,plain,(
% 0.20/0.53    ( ! [X4,X3] : (k6_relat_1(X4) = k7_relat_1(k6_relat_1(X3),X4) | ~r1_tarski(k2_relat_1(k6_relat_1(X4)),X3) | ~v1_relat_1(k6_relat_1(X4))) )),
% 0.20/0.53    inference(superposition,[],[f85,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f125,f42])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.53    inference(superposition,[],[f60,f83])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f82,f44])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f81,f42])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f74,f42])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0))),X0) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X0)))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.53    inference(superposition,[],[f53,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.53    inference(negated_conjecture,[],[f20])).
% 0.20/0.53  fof(f20,conjecture,(
% 0.20/0.53    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (20425)------------------------------
% 0.20/0.53  % (20425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20425)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (20425)Memory used [KB]: 2814
% 0.20/0.53  % (20425)Time elapsed: 0.118 s
% 0.20/0.53  % (20425)------------------------------
% 0.20/0.53  % (20425)------------------------------
% 0.20/0.53  % (20413)Success in time 0.174 s
%------------------------------------------------------------------------------
