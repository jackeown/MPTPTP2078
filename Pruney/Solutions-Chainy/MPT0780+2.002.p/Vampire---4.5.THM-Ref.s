%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  66 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 133 expanded)
%              Number of equality atoms :   41 (  63 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f264])).

% (11709)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f264,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
    inference(backward_demodulation,[],[f189,f263])).

fof(f263,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f249,f53])).

fof(f53,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f249,plain,(
    k3_xboole_0(sK0,sK1) = k1_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[],[f53,f227])).

fof(f227,plain,(
    k6_relat_1(sK0) = k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f130,f50])).

fof(f50,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(f130,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k6_relat_1(k3_xboole_0(X1,X2)) ) ),
    inference(forward_demodulation,[],[f129,f114])).

fof(f114,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(k3_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f112,f62])).

fof(f62,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f112,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f64,f52])).

fof(f52,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f129,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f127,f53])).

fof(f127,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X1)),X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f70,f52])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f189,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f155,f187])).

fof(f187,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f92,f61])).

fof(f61,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f92,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f61,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f155,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f51,f133])).

fof(f133,plain,(
    ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f75,f49])).

fof(f49,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

fof(f51,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (11691)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (11701)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (11694)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (11689)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (11690)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (11688)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (11688)Refutation not found, incomplete strategy% (11688)------------------------------
% 0.20/0.52  % (11688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11688)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (11688)Memory used [KB]: 1663
% 0.20/0.52  % (11688)Time elapsed: 0.115 s
% 0.20/0.52  % (11688)------------------------------
% 0.20/0.52  % (11688)------------------------------
% 0.20/0.52  % (11705)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (11706)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (11692)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (11708)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (11694)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f265,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f264])).
% 0.20/0.53  % (11709)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  fof(f264,plain,(
% 0.20/0.53    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)),
% 0.20/0.53    inference(backward_demodulation,[],[f189,f263])).
% 0.20/0.53  fof(f263,plain,(
% 0.20/0.53    sK0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.53    inference(forward_demodulation,[],[f249,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.53  fof(f249,plain,(
% 0.20/0.53    k3_xboole_0(sK0,sK1) = k1_relat_1(k6_relat_1(sK0))),
% 0.20/0.53    inference(superposition,[],[f53,f227])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    k6_relat_1(sK0) = k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.53    inference(resolution,[],[f130,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    r1_tarski(sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 0.20/0.53    inference(negated_conjecture,[],[f26])).
% 0.20/0.53  fof(f26,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k6_relat_1(k3_xboole_0(X1,X2))) )),
% 0.20/0.53    inference(forward_demodulation,[],[f129,f114])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k6_relat_1(k3_xboole_0(X1,X2))) )),
% 0.20/0.53    inference(forward_demodulation,[],[f112,f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,axiom,(
% 0.20/0.53    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 0.20/0.53    inference(resolution,[],[f64,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f19])).
% 0.20/0.53  fof(f19,axiom,(
% 0.20/0.53    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f127,f53])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X1)),X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 0.20/0.53    inference(resolution,[],[f70,f52])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.53  fof(f189,plain,(
% 0.20/0.53    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))),
% 0.20/0.53    inference(backward_demodulation,[],[f155,f187])).
% 0.20/0.53  fof(f187,plain,(
% 0.20/0.53    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.20/0.53    inference(superposition,[],[f92,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.20/0.53    inference(superposition,[],[f61,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,k3_xboole_0(sK1,sK0))),
% 0.20/0.53    inference(superposition,[],[f51,f133])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(sK2,k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(resolution,[],[f75,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    v1_relat_1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f46])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f46])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (11694)------------------------------
% 0.20/0.53  % (11694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11694)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (11694)Memory used [KB]: 1918
% 0.20/0.53  % (11694)Time elapsed: 0.017 s
% 0.20/0.53  % (11694)------------------------------
% 0.20/0.53  % (11694)------------------------------
% 0.20/0.53  % (11687)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (11699)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (11686)Success in time 0.18 s
%------------------------------------------------------------------------------
