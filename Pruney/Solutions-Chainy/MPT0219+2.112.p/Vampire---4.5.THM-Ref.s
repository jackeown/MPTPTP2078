%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  22 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   29 (  41 expanded)
%              Number of equality atoms :   28 (  40 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f18])).

fof(f18,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f11,f16])).

fof(f16,plain,(
    sK0 = sK1 ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(sK0)
      | sK0 = sK1 ) ),
    inference(superposition,[],[f14,f10])).

fof(f10,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(k1_tarski(X1),k1_tarski(X2))
      | X1 = X2 ) ),
    inference(definition_unfolding,[],[f12,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | k1_tarski(X0) != k2_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( X1 = X2
      | k1_tarski(X0) != k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(f11,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:22:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (27195)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (27188)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.51  % (27211)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.51  % (27192)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (27192)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    sK0 != sK0),
% 0.22/0.51    inference(superposition,[],[f11,f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    sK0 = sK1),
% 0.22/0.51    inference(equality_resolution,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK0) | sK0 = sK1) )),
% 0.22/0.51    inference(superposition,[],[f14,f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f6,plain,(
% 0.22/0.51    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.22/0.51    inference(negated_conjecture,[],[f4])).
% 0.22/0.51  fof(f4,conjecture,(
% 0.22/0.51    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) | X1 = X2) )),
% 0.22/0.51    inference(definition_unfolding,[],[f12,f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (X1 = X2 | k1_tarski(X0) != k2_tarski(X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (X1 = X2 | k1_tarski(X0) != k2_tarski(X1,X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    sK0 != sK1),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (27192)------------------------------
% 0.22/0.51  % (27192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (27192)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (27192)Memory used [KB]: 1663
% 0.22/0.51  % (27192)Time elapsed: 0.099 s
% 0.22/0.51  % (27192)------------------------------
% 0.22/0.51  % (27192)------------------------------
% 0.22/0.52  % (27203)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (27204)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.52  % (27184)Success in time 0.158 s
%------------------------------------------------------------------------------
