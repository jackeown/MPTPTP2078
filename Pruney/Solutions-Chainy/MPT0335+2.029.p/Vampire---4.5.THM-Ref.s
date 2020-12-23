%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:18 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 188 expanded)
%              Number of leaves         :   15 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :   98 ( 335 expanded)
%              Number of equality atoms :   66 ( 232 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(subsumption_resolution,[],[f130,f105])).

fof(f105,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f71,f72])).

fof(f72,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(definition_unfolding,[],[f39,f70,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_tarski(X3) != k3_xboole_0(X0,X2)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k1_tarski(sK3) != k3_xboole_0(sK0,sK2)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

% (18528)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f71,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(definition_unfolding,[],[f41,f70,f49])).

fof(f41,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f130,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f129,f85])).

fof(f85,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f76,f84])).

fof(f84,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f75,f81])).

fof(f81,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f38,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

% (18537)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (18539)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f38,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f47,f49])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f76,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f52,f49,f49,f49,f49])).

fof(f52,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f129,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f125,f72])).

fof(f125,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    inference(resolution,[],[f83,f40])).

fof(f40,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3))) ) ),
    inference(forward_demodulation,[],[f82,f74])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f46,f49,f49])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f82,plain,(
    ! [X0] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK0))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f40,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f69,f49,f69])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:41:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (18529)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (18521)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (18520)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (18516)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (18538)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (18524)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (18519)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.53  % (18544)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.53  % (18517)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.53  % (18522)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.53  % (18532)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.54  % (18543)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (18518)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.54  % (18524)Refutation found. Thanks to Tanya!
% 1.36/0.54  % SZS status Theorem for theBenchmark
% 1.36/0.54  % (18545)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.54  % (18535)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.54  % (18536)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.54  % (18541)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f131,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(subsumption_resolution,[],[f130,f105])).
% 1.36/0.54  fof(f105,plain,(
% 1.36/0.54    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.36/0.54    inference(superposition,[],[f71,f72])).
% 1.36/0.54  fof(f72,plain,(
% 1.36/0.54    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.36/0.54    inference(definition_unfolding,[],[f39,f70,f49])).
% 1.36/0.54  fof(f49,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f10])).
% 1.36/0.54  fof(f10,axiom,(
% 1.36/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.36/0.54  fof(f70,plain,(
% 1.36/0.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f42,f69])).
% 1.36/0.54  fof(f69,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f48,f68])).
% 1.36/0.54  fof(f68,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f51,f67])).
% 1.36/0.54  fof(f67,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f61,f66])).
% 1.36/0.54  fof(f66,plain,(
% 1.36/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f62,f65])).
% 1.36/0.54  fof(f65,plain,(
% 1.36/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f63,f64])).
% 1.36/0.54  fof(f64,plain,(
% 1.36/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f17])).
% 1.36/0.54  fof(f17,axiom,(
% 1.36/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.36/0.54  fof(f63,plain,(
% 1.36/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f16])).
% 1.36/0.54  fof(f16,axiom,(
% 1.36/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.36/0.54  fof(f62,plain,(
% 1.36/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f15])).
% 1.36/0.54  fof(f15,axiom,(
% 1.36/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.36/0.54  fof(f61,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f14])).
% 1.36/0.54  fof(f14,axiom,(
% 1.36/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.36/0.54  fof(f51,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f13])).
% 1.36/0.54  fof(f13,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.36/0.54  fof(f48,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f12])).
% 1.36/0.54  fof(f12,axiom,(
% 1.36/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.54  fof(f42,plain,(
% 1.36/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f11])).
% 1.36/0.54  fof(f11,axiom,(
% 1.36/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.36/0.54  fof(f39,plain,(
% 1.36/0.54    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 1.36/0.54    inference(cnf_transformation,[],[f30])).
% 1.36/0.54  fof(f30,plain,(
% 1.36/0.54    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f29])).
% 1.36/0.54  fof(f29,plain,(
% 1.36/0.54    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k1_tarski(sK3) != k3_xboole_0(sK0,sK2) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f23,plain,(
% 1.36/0.54    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 1.36/0.54    inference(flattening,[],[f22])).
% 1.36/0.54  fof(f22,plain,(
% 1.36/0.54    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 1.36/0.54    inference(ennf_transformation,[],[f20])).
% 1.36/0.54  fof(f20,negated_conjecture,(
% 1.36/0.54    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.36/0.54    inference(negated_conjecture,[],[f19])).
% 1.36/0.54  fof(f19,conjecture,(
% 1.36/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 1.36/0.55  % (18528)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.55  fof(f71,plain,(
% 1.36/0.55    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.36/0.55    inference(definition_unfolding,[],[f41,f70,f49])).
% 1.36/0.55  fof(f41,plain,(
% 1.36/0.55    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 1.36/0.55    inference(cnf_transformation,[],[f30])).
% 1.36/0.55  fof(f130,plain,(
% 1.36/0.55    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.36/0.55    inference(forward_demodulation,[],[f129,f85])).
% 1.36/0.55  fof(f85,plain,(
% 1.36/0.55    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) )),
% 1.36/0.55    inference(superposition,[],[f76,f84])).
% 1.36/0.55  fof(f84,plain,(
% 1.36/0.55    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.36/0.55    inference(superposition,[],[f75,f81])).
% 1.36/0.55  fof(f81,plain,(
% 1.36/0.55    sK1 = k2_xboole_0(sK0,sK1)),
% 1.36/0.55    inference(resolution,[],[f38,f50])).
% 1.36/0.55  fof(f50,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.36/0.55    inference(cnf_transformation,[],[f25])).
% 1.36/0.55  % (18537)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.55  % (18539)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.55  fof(f25,plain,(
% 1.36/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.36/0.55    inference(ennf_transformation,[],[f6])).
% 1.36/0.55  fof(f6,axiom,(
% 1.36/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.36/0.55  fof(f38,plain,(
% 1.36/0.55    r1_tarski(sK0,sK1)),
% 1.36/0.55    inference(cnf_transformation,[],[f30])).
% 1.36/0.55  fof(f75,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 1.36/0.55    inference(definition_unfolding,[],[f47,f49])).
% 1.36/0.55  fof(f47,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f8])).
% 1.36/0.55  fof(f8,axiom,(
% 1.36/0.55    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.36/0.55  fof(f76,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f52,f49,f49,f49,f49])).
% 1.36/0.55  fof(f52,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f7])).
% 1.36/0.55  fof(f7,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.36/0.55  fof(f129,plain,(
% 1.36/0.55    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 1.36/0.55    inference(forward_demodulation,[],[f125,f72])).
% 1.36/0.55  fof(f125,plain,(
% 1.36/0.55    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 1.36/0.55    inference(resolution,[],[f83,f40])).
% 1.36/0.55  fof(f40,plain,(
% 1.36/0.55    r2_hidden(sK3,sK0)),
% 1.36/0.55    inference(cnf_transformation,[],[f30])).
% 1.36/0.55  fof(f83,plain,(
% 1.36/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3)))) )),
% 1.36/0.55    inference(forward_demodulation,[],[f82,f74])).
% 1.36/0.55  fof(f74,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f46,f49,f49])).
% 1.36/0.55  fof(f46,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f1])).
% 1.36/0.55  fof(f1,axiom,(
% 1.36/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.36/0.55  fof(f82,plain,(
% 1.36/0.55    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK3),sK0)) | ~r2_hidden(X0,sK0)) )),
% 1.36/0.55    inference(resolution,[],[f40,f77])).
% 1.36/0.55  fof(f77,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)) | ~r2_hidden(X0,X1)) )),
% 1.36/0.55    inference(definition_unfolding,[],[f54,f69,f49,f69])).
% 1.36/0.55  fof(f54,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f28])).
% 1.36/0.55  fof(f28,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 1.36/0.55    inference(flattening,[],[f27])).
% 1.36/0.55  fof(f27,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 1.36/0.55    inference(ennf_transformation,[],[f18])).
% 1.36/0.55  fof(f18,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 1.36/0.55  % SZS output end Proof for theBenchmark
% 1.36/0.55  % (18524)------------------------------
% 1.36/0.55  % (18524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (18524)Termination reason: Refutation
% 1.36/0.55  
% 1.36/0.55  % (18524)Memory used [KB]: 10746
% 1.36/0.55  % (18524)Time elapsed: 0.144 s
% 1.36/0.55  % (18524)------------------------------
% 1.36/0.55  % (18524)------------------------------
% 1.36/0.55  % (18533)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.55  % (18515)Success in time 0.192 s
%------------------------------------------------------------------------------
