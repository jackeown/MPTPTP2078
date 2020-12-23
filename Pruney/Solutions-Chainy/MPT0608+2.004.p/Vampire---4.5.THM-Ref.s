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
% DateTime   : Thu Dec  3 12:51:23 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   37 (  54 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 116 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f228])).

fof(f228,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f36,f198])).

fof(f198,plain,(
    ! [X2] : k6_subset_1(k1_relat_1(sK1),X2) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X2))) ),
    inference(backward_demodulation,[],[f90,f102])).

fof(f102,plain,(
    ! [X0] : k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0)) ),
    inference(superposition,[],[f54,f80])).

fof(f80,plain,(
    sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(resolution,[],[f57,f52])).

% (4185)Termination reason: Refutation not found, incomplete strategy
fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f57,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_relat_1(sK1),X5)
      | sK1 = k7_relat_1(sK1,X5) ) ),
    inference(resolution,[],[f35,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

fof(f54,plain,(
    ! [X2,X1] : k7_relat_1(sK1,k6_subset_1(X1,X2)) = k6_subset_1(k7_relat_1(sK1,X1),k7_relat_1(sK1,X2)) ),
    inference(resolution,[],[f35,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

fof(f90,plain,(
    ! [X2] : k6_subset_1(k1_relat_1(sK1),X2) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X2))) ),
    inference(resolution,[],[f56,f50])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f49,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f56,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,k1_relat_1(sK1))
      | k1_relat_1(k7_relat_1(sK1,X4)) = X4 ) ),
    inference(resolution,[],[f35,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f36,plain,(
    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (4157)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (4169)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (4185)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (4160)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.28/0.52  % (4177)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.28/0.52  % (4185)Refutation not found, incomplete strategy% (4185)------------------------------
% 1.28/0.52  % (4185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (4173)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.28/0.53  % (4156)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.28/0.53  % (4157)Refutation found. Thanks to Tanya!
% 1.28/0.53  % SZS status Theorem for theBenchmark
% 1.28/0.53  % SZS output start Proof for theBenchmark
% 1.28/0.53  fof(f229,plain,(
% 1.28/0.53    $false),
% 1.28/0.53    inference(trivial_inequality_removal,[],[f228])).
% 1.28/0.53  fof(f228,plain,(
% 1.28/0.53    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 1.28/0.53    inference(superposition,[],[f36,f198])).
% 1.28/0.53  fof(f198,plain,(
% 1.28/0.53    ( ! [X2] : (k6_subset_1(k1_relat_1(sK1),X2) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X2)))) )),
% 1.28/0.53    inference(backward_demodulation,[],[f90,f102])).
% 1.28/0.53  fof(f102,plain,(
% 1.28/0.53    ( ! [X0] : (k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0))) )),
% 1.28/0.53    inference(superposition,[],[f54,f80])).
% 1.28/0.53  fof(f80,plain,(
% 1.28/0.53    sK1 = k7_relat_1(sK1,k1_relat_1(sK1))),
% 1.28/0.53    inference(resolution,[],[f57,f52])).
% 1.28/0.53  % (4185)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  fof(f52,plain,(
% 1.28/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.28/0.53    inference(equality_resolution,[],[f43])).
% 1.28/0.53  fof(f43,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.28/0.53    inference(cnf_transformation,[],[f34])).
% 1.28/0.53  fof(f34,plain,(
% 1.28/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.28/0.53    inference(flattening,[],[f33])).
% 1.28/0.53  fof(f33,plain,(
% 1.28/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.28/0.53    inference(nnf_transformation,[],[f2])).
% 1.28/0.53  fof(f2,axiom,(
% 1.28/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.28/0.53  fof(f57,plain,(
% 1.28/0.53    ( ! [X5] : (~r1_tarski(k1_relat_1(sK1),X5) | sK1 = k7_relat_1(sK1,X5)) )),
% 1.28/0.53    inference(resolution,[],[f35,f37])).
% 1.28/0.53  fof(f37,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 1.28/0.53    inference(cnf_transformation,[],[f24])).
% 1.28/0.53  fof(f24,plain,(
% 1.28/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.28/0.53    inference(flattening,[],[f23])).
% 1.28/0.53  fof(f23,plain,(
% 1.28/0.53    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.28/0.53    inference(ennf_transformation,[],[f19])).
% 1.28/0.53  fof(f19,axiom,(
% 1.28/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.28/0.53  fof(f35,plain,(
% 1.28/0.53    v1_relat_1(sK1)),
% 1.28/0.53    inference(cnf_transformation,[],[f32])).
% 1.28/0.53  fof(f32,plain,(
% 1.28/0.53    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) & v1_relat_1(sK1)),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f31])).
% 1.28/0.53  fof(f31,plain,(
% 1.28/0.53    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),X0) & v1_relat_1(X1)) => (k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) & v1_relat_1(sK1))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f22,plain,(
% 1.28/0.53    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),X0) & v1_relat_1(X1))),
% 1.28/0.53    inference(ennf_transformation,[],[f21])).
% 1.28/0.53  fof(f21,negated_conjecture,(
% 1.28/0.53    ~! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0))),
% 1.28/0.53    inference(negated_conjecture,[],[f20])).
% 1.28/0.53  fof(f20,conjecture,(
% 1.28/0.53    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).
% 1.28/0.53  fof(f54,plain,(
% 1.28/0.53    ( ! [X2,X1] : (k7_relat_1(sK1,k6_subset_1(X1,X2)) = k6_subset_1(k7_relat_1(sK1,X1),k7_relat_1(sK1,X2))) )),
% 1.28/0.53    inference(resolution,[],[f35,f40])).
% 1.28/0.53  fof(f40,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  fof(f28,plain,(
% 1.28/0.53    ! [X0,X1,X2] : (k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.28/0.53    inference(ennf_transformation,[],[f16])).
% 1.28/0.53  fof(f16,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).
% 1.28/0.53  fof(f90,plain,(
% 1.28/0.53    ( ! [X2] : (k6_subset_1(k1_relat_1(sK1),X2) = k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X2)))) )),
% 1.28/0.53    inference(resolution,[],[f56,f50])).
% 1.28/0.53  fof(f50,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f49,f41])).
% 1.28/0.53  fof(f41,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f13])).
% 1.28/0.53  fof(f13,axiom,(
% 1.28/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.28/0.53  fof(f49,plain,(
% 1.28/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f6])).
% 1.28/0.53  fof(f6,axiom,(
% 1.28/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.28/0.53  fof(f56,plain,(
% 1.28/0.53    ( ! [X4] : (~r1_tarski(X4,k1_relat_1(sK1)) | k1_relat_1(k7_relat_1(sK1,X4)) = X4) )),
% 1.28/0.53    inference(resolution,[],[f35,f38])).
% 1.28/0.53  fof(f38,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.28/0.53    inference(cnf_transformation,[],[f26])).
% 1.28/0.53  fof(f26,plain,(
% 1.28/0.53    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.28/0.53    inference(flattening,[],[f25])).
% 1.28/0.53  fof(f25,plain,(
% 1.28/0.53    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.28/0.53    inference(ennf_transformation,[],[f18])).
% 1.28/0.53  fof(f18,axiom,(
% 1.28/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.28/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.28/0.53  fof(f36,plain,(
% 1.28/0.53    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 1.28/0.53    inference(cnf_transformation,[],[f32])).
% 1.28/0.53  % SZS output end Proof for theBenchmark
% 1.28/0.53  % (4157)------------------------------
% 1.28/0.53  % (4157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (4157)Termination reason: Refutation
% 1.28/0.53  
% 1.28/0.53  % (4157)Memory used [KB]: 1791
% 1.28/0.53  % (4157)Time elapsed: 0.115 s
% 1.28/0.53  % (4157)------------------------------
% 1.28/0.53  % (4157)------------------------------
% 1.28/0.53  
% 1.28/0.53  % (4185)Memory used [KB]: 1663
% 1.28/0.53  % (4185)Time elapsed: 0.111 s
% 1.28/0.53  % (4185)------------------------------
% 1.28/0.53  % (4185)------------------------------
% 1.28/0.53  % (4155)Success in time 0.176 s
%------------------------------------------------------------------------------
