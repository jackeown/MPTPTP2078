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
% DateTime   : Thu Dec  3 12:35:56 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 (  51 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :   13
%              Number of atoms          :   42 (  83 expanded)
%              Number of equality atoms :   41 (  82 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(subsumption_resolution,[],[f159,f16])).

fof(f16,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f159,plain,(
    sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f158])).

fof(f158,plain,
    ( k1_tarski(sK1) != k1_tarski(sK1)
    | sK0 = sK1 ),
    inference(superposition,[],[f19,f115])).

fof(f115,plain,(
    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f20,f104])).

fof(f104,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f95,f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f95,plain,(
    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f46,f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),X0)) = k3_xboole_0(k1_tarski(sK0),X0) ),
    inference(superposition,[],[f18,f15])).

fof(f15,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f18,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f46,plain,(
    ! [X2] : k3_xboole_0(X2,k1_tarski(sK0)) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(X2,k1_tarski(sK0))) ),
    inference(superposition,[],[f29,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f29,plain,(
    ! [X2] : k3_xboole_0(k1_tarski(sK0),X2) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2)) ),
    inference(forward_demodulation,[],[f27,f25])).

fof(f27,plain,(
    ! [X2] : k3_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),X2)) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2)) ),
    inference(superposition,[],[f17,f15])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_xboole_1)).

% (10985)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% (10986)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:23:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.48  % (10995)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.48  % (11002)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.48  % (10994)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.49  % (10994)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f160,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(subsumption_resolution,[],[f159,f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    sK0 != sK1),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f11,plain,(
% 0.19/0.49    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.19/0.49    inference(ennf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.19/0.49    inference(negated_conjecture,[],[f8])).
% 0.19/0.49  fof(f8,conjecture,(
% 0.19/0.49    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 0.19/0.49  fof(f159,plain,(
% 0.19/0.49    sK0 = sK1),
% 0.19/0.49    inference(trivial_inequality_removal,[],[f158])).
% 0.19/0.49  fof(f158,plain,(
% 0.19/0.49    k1_tarski(sK1) != k1_tarski(sK1) | sK0 = sK1),
% 0.19/0.49    inference(superposition,[],[f19,f115])).
% 0.19/0.49  fof(f115,plain,(
% 0.19/0.49    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.19/0.49    inference(superposition,[],[f20,f104])).
% 0.19/0.49  fof(f104,plain,(
% 0.19/0.49    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.19/0.49    inference(forward_demodulation,[],[f95,f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.19/0.49    inference(cnf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,plain,(
% 0.19/0.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.19/0.49    inference(rectify,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.19/0.49  fof(f95,plain,(
% 0.19/0.49    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.19/0.49    inference(superposition,[],[f46,f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ( ! [X0] : (k3_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),X0)) = k3_xboole_0(k1_tarski(sK0),X0)) )),
% 0.19/0.49    inference(superposition,[],[f18,f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.19/0.49  fof(f46,plain,(
% 0.19/0.49    ( ! [X2] : (k3_xboole_0(X2,k1_tarski(sK0)) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(X2,k1_tarski(sK0)))) )),
% 0.19/0.49    inference(superposition,[],[f29,f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ( ! [X2] : (k3_xboole_0(k1_tarski(sK0),X2) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2))) )),
% 0.19/0.49    inference(forward_demodulation,[],[f27,f25])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ( ! [X2] : (k3_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK1),X2)) = k3_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),X2))) )),
% 0.19/0.49    inference(superposition,[],[f17,f15])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_xboole_1)).
% 0.19/0.50  % (10985)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (10986)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.19/0.50    inference(cnf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,plain,(
% 0.19/0.50    ! [X0,X1] : (X0 = X1 | k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (10994)------------------------------
% 0.19/0.50  % (10994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (10994)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (10994)Memory used [KB]: 1791
% 0.19/0.50  % (10994)Time elapsed: 0.090 s
% 0.19/0.50  % (10994)------------------------------
% 0.19/0.50  % (10994)------------------------------
% 0.19/0.50  % (10988)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.50  % (10979)Success in time 0.156 s
%------------------------------------------------------------------------------
