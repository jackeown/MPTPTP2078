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
% DateTime   : Thu Dec  3 12:46:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 (  75 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   71 (  97 expanded)
%              Number of equality atoms :   30 (  51 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f58,f64])).

fof(f64,plain,(
    ~ spl1_3 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | ~ spl1_3 ),
    inference(global_subsumption,[],[f21,f62])).

fof(f62,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl1_3 ),
    inference(superposition,[],[f22,f57])).

fof(f57,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f22,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f21,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f58,plain,
    ( spl1_3
    | spl1_2 ),
    inference(avatar_split_clause,[],[f52,f48,f55])).

fof(f48,plain,
    ( spl1_2
  <=> m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f52,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK0)
    | spl1_2 ),
    inference(unit_resulting_resolution,[],[f40,f50,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f27,f38])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f50,plain,
    ( ~ m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f24,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f51,plain,(
    ~ spl1_2 ),
    inference(avatar_split_clause,[],[f39,f48])).

fof(f39,plain,(
    ~ m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(definition_unfolding,[],[f20,f38])).

fof(f20,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f18])).

fof(f18,plain,
    ( ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))
   => ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.43  % (16029)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.43  % (16029)Refutation found. Thanks to Tanya!
% 0.19/0.43  % SZS status Theorem for theBenchmark
% 0.19/0.43  % SZS output start Proof for theBenchmark
% 0.19/0.43  fof(f65,plain,(
% 0.19/0.43    $false),
% 0.19/0.43    inference(avatar_sat_refutation,[],[f51,f58,f64])).
% 0.19/0.43  fof(f64,plain,(
% 0.19/0.43    ~spl1_3),
% 0.19/0.43    inference(avatar_contradiction_clause,[],[f63])).
% 0.19/0.43  fof(f63,plain,(
% 0.19/0.43    $false | ~spl1_3),
% 0.19/0.43    inference(global_subsumption,[],[f21,f62])).
% 0.19/0.43  fof(f62,plain,(
% 0.19/0.43    ~v1_xboole_0(k1_xboole_0) | ~spl1_3),
% 0.19/0.43    inference(superposition,[],[f22,f57])).
% 0.19/0.43  fof(f57,plain,(
% 0.19/0.43    k1_xboole_0 = k1_zfmisc_1(sK0) | ~spl1_3),
% 0.19/0.43    inference(avatar_component_clause,[],[f55])).
% 0.19/0.43  fof(f55,plain,(
% 0.19/0.43    spl1_3 <=> k1_xboole_0 = k1_zfmisc_1(sK0)),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.19/0.43  fof(f22,plain,(
% 0.19/0.43    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f11])).
% 0.19/0.43  fof(f11,axiom,(
% 0.19/0.43    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.19/0.43  fof(f21,plain,(
% 0.19/0.43    v1_xboole_0(k1_xboole_0)),
% 0.19/0.43    inference(cnf_transformation,[],[f1])).
% 0.19/0.43  fof(f1,axiom,(
% 0.19/0.43    v1_xboole_0(k1_xboole_0)),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.43  fof(f58,plain,(
% 0.19/0.43    spl1_3 | spl1_2),
% 0.19/0.43    inference(avatar_split_clause,[],[f52,f48,f55])).
% 0.19/0.43  fof(f48,plain,(
% 0.19/0.43    spl1_2 <=> m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.19/0.43  fof(f52,plain,(
% 0.19/0.43    k1_xboole_0 = k1_zfmisc_1(sK0) | spl1_2),
% 0.19/0.43    inference(unit_resulting_resolution,[],[f40,f50,f41])).
% 0.19/0.43  fof(f41,plain,(
% 0.19/0.43    ( ! [X0,X1] : (m1_subset_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.19/0.43    inference(definition_unfolding,[],[f27,f38])).
% 0.19/0.43  fof(f38,plain,(
% 0.19/0.43    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.19/0.43    inference(definition_unfolding,[],[f25,f37])).
% 0.19/0.43  fof(f37,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.19/0.43    inference(definition_unfolding,[],[f26,f36])).
% 0.19/0.43  fof(f36,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.19/0.43    inference(definition_unfolding,[],[f28,f35])).
% 0.19/0.43  fof(f35,plain,(
% 0.19/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.19/0.43    inference(definition_unfolding,[],[f29,f34])).
% 0.19/0.43  fof(f34,plain,(
% 0.19/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.19/0.43    inference(definition_unfolding,[],[f30,f33])).
% 0.19/0.43  fof(f33,plain,(
% 0.19/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.43    inference(definition_unfolding,[],[f31,f32])).
% 0.19/0.43  fof(f32,plain,(
% 0.19/0.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f8])).
% 0.19/0.43  fof(f8,axiom,(
% 0.19/0.43    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.19/0.43  fof(f31,plain,(
% 0.19/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f7])).
% 0.19/0.43  fof(f7,axiom,(
% 0.19/0.43    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.19/0.43  fof(f30,plain,(
% 0.19/0.43    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f6])).
% 0.19/0.43  fof(f6,axiom,(
% 0.19/0.43    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.43  fof(f29,plain,(
% 0.19/0.43    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f5])).
% 0.19/0.43  fof(f5,axiom,(
% 0.19/0.43    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.43  fof(f28,plain,(
% 0.19/0.43    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f4])).
% 0.19/0.43  fof(f4,axiom,(
% 0.19/0.43    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.43  fof(f26,plain,(
% 0.19/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f3])).
% 0.19/0.43  fof(f3,axiom,(
% 0.19/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.43  fof(f25,plain,(
% 0.19/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f2])).
% 0.19/0.43  fof(f2,axiom,(
% 0.19/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.43  fof(f27,plain,(
% 0.19/0.43    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f17])).
% 0.19/0.43  fof(f17,plain,(
% 0.19/0.43    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.19/0.43    inference(flattening,[],[f16])).
% 0.19/0.43  fof(f16,plain,(
% 0.19/0.43    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.19/0.43    inference(ennf_transformation,[],[f12])).
% 0.19/0.43  fof(f12,axiom,(
% 0.19/0.43    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
% 0.19/0.43  fof(f50,plain,(
% 0.19/0.43    ~m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl1_2),
% 0.19/0.43    inference(avatar_component_clause,[],[f48])).
% 0.19/0.43  fof(f40,plain,(
% 0.19/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.19/0.43    inference(definition_unfolding,[],[f24,f23])).
% 0.19/0.43  fof(f23,plain,(
% 0.19/0.43    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.19/0.43    inference(cnf_transformation,[],[f9])).
% 0.19/0.43  fof(f9,axiom,(
% 0.19/0.43    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.19/0.43  fof(f24,plain,(
% 0.19/0.43    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.19/0.43    inference(cnf_transformation,[],[f10])).
% 0.19/0.43  fof(f10,axiom,(
% 0.19/0.43    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 0.19/0.43  fof(f51,plain,(
% 0.19/0.43    ~spl1_2),
% 0.19/0.43    inference(avatar_split_clause,[],[f39,f48])).
% 0.19/0.43  fof(f39,plain,(
% 0.19/0.43    ~m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.43    inference(definition_unfolding,[],[f20,f38])).
% 0.19/0.43  fof(f20,plain,(
% 0.19/0.43    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.43    inference(cnf_transformation,[],[f19])).
% 0.19/0.43  fof(f19,plain,(
% 0.19/0.43    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f18])).
% 0.19/0.43  fof(f18,plain,(
% 0.19/0.43    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) => ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.43    introduced(choice_axiom,[])).
% 0.19/0.43  fof(f15,plain,(
% 0.19/0.43    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.19/0.43    inference(ennf_transformation,[],[f14])).
% 0.19/0.43  fof(f14,negated_conjecture,(
% 0.19/0.43    ~! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.19/0.43    inference(negated_conjecture,[],[f13])).
% 0.19/0.43  fof(f13,conjecture,(
% 0.19/0.43    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.19/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).
% 0.19/0.43  % SZS output end Proof for theBenchmark
% 0.19/0.43  % (16029)------------------------------
% 0.19/0.43  % (16029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (16029)Termination reason: Refutation
% 0.19/0.43  
% 0.19/0.43  % (16029)Memory used [KB]: 10618
% 0.19/0.43  % (16029)Time elapsed: 0.039 s
% 0.19/0.43  % (16029)------------------------------
% 0.19/0.43  % (16029)------------------------------
% 0.19/0.44  % (16011)Success in time 0.084 s
%------------------------------------------------------------------------------
