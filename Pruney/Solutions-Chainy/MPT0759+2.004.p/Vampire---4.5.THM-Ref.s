%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 (  47 expanded)
%              Number of equality atoms :   37 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f148])).

fof(f148,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f30,f143])).

fof(f143,plain,(
    sK0 = k1_ordinal1(sK0) ),
    inference(trivial_inequality_removal,[],[f142])).

fof(f142,plain,
    ( sK0 != sK0
    | sK0 = k1_ordinal1(sK0) ),
    inference(superposition,[],[f108,f131])).

fof(f131,plain,(
    ! [X0] :
      ( k4_xboole_0(X0,k1_tarski(X0)) = X0
      | k1_ordinal1(X0) = X0 ) ),
    inference(superposition,[],[f123,f32])).

fof(f32,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f123,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k1_tarski(X1)) = X0
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(superposition,[],[f35,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | k4_xboole_0(X1,k1_tarski(X0)) = X1 ) ),
    inference(resolution,[],[f41,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f108,plain,(
    sK0 != k4_xboole_0(sK0,k1_tarski(sK0)) ),
    inference(superposition,[],[f52,f81])).

fof(f81,plain,(
    ! [X9] : k4_xboole_0(X9,k1_tarski(X9)) = k4_xboole_0(k1_ordinal1(X9),k1_tarski(X9)) ),
    inference(superposition,[],[f40,f32])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f52,plain,(
    sK0 != k4_xboole_0(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f29,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f29,plain,(
    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f26])).

fof(f26,plain,
    ( ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0
   => sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).

fof(f30,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (17114)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.44  % (17117)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.45  % (17117)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f149,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f148])).
% 0.21/0.45  fof(f148,plain,(
% 0.21/0.45    sK0 != sK0),
% 0.21/0.45    inference(superposition,[],[f30,f143])).
% 0.21/0.45  fof(f143,plain,(
% 0.21/0.45    sK0 = k1_ordinal1(sK0)),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f142])).
% 0.21/0.45  fof(f142,plain,(
% 0.21/0.45    sK0 != sK0 | sK0 = k1_ordinal1(sK0)),
% 0.21/0.45    inference(superposition,[],[f108,f131])).
% 0.21/0.45  fof(f131,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_tarski(X0)) = X0 | k1_ordinal1(X0) = X0) )),
% 0.21/0.45    inference(superposition,[],[f123,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,axiom,(
% 0.21/0.45    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.45  fof(f123,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,k1_tarski(X1)) = X0 | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 0.21/0.45    inference(superposition,[],[f35,f107])).
% 0.21/0.45  fof(f107,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | k4_xboole_0(X1,k1_tarski(X0)) = X1) )),
% 0.21/0.45    inference(resolution,[],[f41,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,axiom,(
% 0.21/0.45    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,axiom,(
% 0.21/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    sK0 != k4_xboole_0(sK0,k1_tarski(sK0))),
% 0.21/0.45    inference(superposition,[],[f52,f81])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    ( ! [X9] : (k4_xboole_0(X9,k1_tarski(X9)) = k4_xboole_0(k1_ordinal1(X9),k1_tarski(X9))) )),
% 0.21/0.45    inference(superposition,[],[f40,f32])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    sK0 != k4_xboole_0(k1_ordinal1(sK0),k1_tarski(sK0))),
% 0.21/0.45    inference(superposition,[],[f29,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,axiom,(
% 0.21/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0))),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0 => sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0),
% 0.21/0.45    inference(ennf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,negated_conjecture,(
% 0.21/0.45    ~! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0),
% 0.21/0.45    inference(negated_conjecture,[],[f22])).
% 0.21/0.45  fof(f22,conjecture,(
% 0.21/0.45    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,axiom,(
% 0.21/0.45    ! [X0] : k1_ordinal1(X0) != X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (17117)------------------------------
% 0.21/0.45  % (17117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (17117)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (17117)Memory used [KB]: 6268
% 0.21/0.45  % (17117)Time elapsed: 0.039 s
% 0.21/0.45  % (17117)------------------------------
% 0.21/0.45  % (17117)------------------------------
% 0.21/0.45  % (17100)Success in time 0.098 s
%------------------------------------------------------------------------------
