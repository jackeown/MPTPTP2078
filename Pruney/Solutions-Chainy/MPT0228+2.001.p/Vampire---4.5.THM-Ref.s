%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  61 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  81 expanded)
%              Number of equality atoms :   39 (  80 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(subsumption_resolution,[],[f241,f75])).

fof(f75,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f23,f42])).

% (10008)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f42,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f35,f25,f25,f25])).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f23,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
        & X0 != X1 )
   => ( k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

fof(f241,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f84,f69])).

fof(f69,plain,(
    ! [X2,X3] : k4_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)) = k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X3,X3,X3,X3)) ),
    inference(superposition,[],[f30,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ),
    inference(definition_unfolding,[],[f29,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ),
    inference(definition_unfolding,[],[f28,f25,f25])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f84,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f40,f41])).

fof(f40,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f24,f25,f39,f25])).

fof(f24,plain,(
    k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:11:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (10010)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.56  % (10029)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (10021)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (10010)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (10028)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.57  % (10013)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.57  % (10011)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  % (10018)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f251,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f241,f75])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f23,f42])).
% 0.21/0.58  % (10008)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 0.21/0.58    inference(definition_unfolding,[],[f35,f25,f25,f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f10])).
% 0.21/0.58  fof(f10,axiom,(
% 0.21/0.58    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.21/0.58    inference(nnf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    sK0 != sK1),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) & sK0 != sK1),
% 0.21/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f18])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) & X0 != X1) => (k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) & sK0 != sK1)),
% 0.21/0.58    introduced(choice_axiom,[])).
% 0.21/0.58  fof(f14,plain,(
% 0.21/0.58    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) & X0 != X1)),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,negated_conjecture,(
% 0.21/0.58    ~! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 0.21/0.58    inference(negated_conjecture,[],[f12])).
% 0.21/0.58  fof(f12,conjecture,(
% 0.21/0.58    ! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).
% 0.21/0.58  fof(f241,plain,(
% 0.21/0.58    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.58    inference(superposition,[],[f84,f69])).
% 0.21/0.58  fof(f69,plain,(
% 0.21/0.58    ( ! [X2,X3] : (k4_xboole_0(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)) = k4_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X3,X3,X3,X3))) )),
% 0.21/0.58    inference(superposition,[],[f30,f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f29,f39])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 0.21/0.58    inference(definition_unfolding,[],[f28,f25,f25])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.58  fof(f84,plain,(
% 0.21/0.58    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.58    inference(forward_demodulation,[],[f40,f41])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.58    inference(definition_unfolding,[],[f24,f25,f39,f25])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (10010)------------------------------
% 0.21/0.58  % (10010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (10010)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (10010)Memory used [KB]: 1918
% 0.21/0.58  % (10010)Time elapsed: 0.134 s
% 0.21/0.58  % (10010)------------------------------
% 0.21/0.58  % (10010)------------------------------
% 0.21/0.58  % (10005)Success in time 0.222 s
%------------------------------------------------------------------------------
