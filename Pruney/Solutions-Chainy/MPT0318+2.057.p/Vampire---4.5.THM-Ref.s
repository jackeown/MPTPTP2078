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
% DateTime   : Thu Dec  3 12:42:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  57 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :   48 (  94 expanded)
%              Number of equality atoms :   47 (  93 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33,plain,(
    $false ),
    inference(subsumption_resolution,[],[f32,f10])).

fof(f10,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f32,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f31,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f20,f11])).

fof(f11,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f20,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f13,f18])).

fof(f18,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f12,f14])).

fof(f14,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f12,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f13,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f31,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f30])).

fof(f30,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f15,f29])).

fof(f29,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f28,f23])).

fof(f28,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f27,f10])).

fof(f27,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(trivial_inequality_removal,[],[f26])).

fof(f26,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(superposition,[],[f15,f19])).

fof(f19,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f9,f18,f18])).

fof(f9,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:17:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (11283)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (11283)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (11291)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f32,f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f31,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 0.21/0.52    inference(superposition,[],[f20,f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f13,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f12,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(superposition,[],[f15,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f28,f23])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f27,f10])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.21/0.52    inference(superposition,[],[f15,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.21/0.52    inference(definition_unfolding,[],[f9,f18,f18])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (11283)------------------------------
% 0.21/0.52  % (11283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11283)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (11283)Memory used [KB]: 6140
% 0.21/0.52  % (11283)Time elapsed: 0.105 s
% 0.21/0.52  % (11283)------------------------------
% 0.21/0.52  % (11283)------------------------------
% 0.21/0.52  % (11289)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (11276)Success in time 0.161 s
%------------------------------------------------------------------------------
