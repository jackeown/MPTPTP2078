%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  57 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 (  90 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f72,f107,f129])).

fof(f129,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl1_5 ),
    inference(subsumption_resolution,[],[f127,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f127,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)),k1_zfmisc_1(k1_xboole_0))
    | spl1_5 ),
    inference(forward_demodulation,[],[f117,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f117,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)),k1_zfmisc_1(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0))))
    | spl1_5 ),
    inference(unit_resulting_resolution,[],[f106,f66])).

fof(f66,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(k1_zfmisc_1(X2),k1_zfmisc_1(X3)),k1_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X3))))
      | k1_xboole_0 = k4_xboole_0(k1_zfmisc_1(X2),k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f25,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_zfmisc_1(X0),k4_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))) ),
    inference(definition_unfolding,[],[f24,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f106,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0))
    | spl1_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl1_5
  <=> k1_xboole_0 = k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f107,plain,
    ( ~ spl1_5
    | spl1_4 ),
    inference(avatar_split_clause,[],[f73,f69,f104])).

fof(f69,plain,
    ( spl1_4
  <=> r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f73,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0))
    | spl1_4 ),
    inference(unit_resulting_resolution,[],[f71,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f71,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0))
    | spl1_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f72,plain,
    ( ~ spl1_4
    | spl1_1 ),
    inference(avatar_split_clause,[],[f51,f35,f69])).

fof(f35,plain,
    ( spl1_1
  <=> m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f51,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0))
    | spl1_1 ),
    inference(unit_resulting_resolution,[],[f37,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f37,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f38,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f33,f35])).

fof(f33,plain,(
    ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(backward_demodulation,[],[f30,f31])).

fof(f31,plain,(
    k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f30,plain,(
    ~ m1_subset_1(k2_tarski(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(definition_unfolding,[],[f18,f21])).

% (14212)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f18,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

% (14217)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f15,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f14])).

fof(f14,plain,
    ( ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))
   => ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:43:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (14227)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (14227)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f38,f72,f107,f129])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    spl1_5),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f128])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    $false | spl1_5),
% 0.21/0.47    inference(subsumption_resolution,[],[f127,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    ~r1_tarski(k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)),k1_zfmisc_1(k1_xboole_0)) | spl1_5),
% 0.21/0.47    inference(forward_demodulation,[],[f117,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ~r1_tarski(k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)),k1_zfmisc_1(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK0)))) | spl1_5),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f106,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X2,X3] : (~r1_tarski(k4_xboole_0(k1_zfmisc_1(X2),k1_zfmisc_1(X3)),k1_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)))) | k1_xboole_0 = k4_xboole_0(k1_zfmisc_1(X2),k1_zfmisc_1(X3))) )),
% 0.21/0.47    inference(superposition,[],[f25,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k1_zfmisc_1(X0),k4_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f24,f23,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_zfmisc_1)).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    k1_xboole_0 != k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)) | spl1_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f104])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    spl1_5 <=> k1_xboole_0 = k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ~spl1_5 | spl1_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f73,f69,f104])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl1_4 <=> r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    k1_xboole_0 != k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)) | spl1_4),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f71,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ~r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)) | spl1_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f69])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ~spl1_4 | spl1_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f51,f35,f69])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    spl1_1 <=> m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ~r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK0)) | spl1_1),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f37,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.47    inference(nnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl1_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f35])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ~spl1_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f35])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(backward_demodulation,[],[f30,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.47    inference(definition_unfolding,[],[f19,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ~m1_subset_1(k2_tarski(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(definition_unfolding,[],[f18,f21])).
% 0.21/0.47  % (14212)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  % (14217)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) => ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (14227)------------------------------
% 0.21/0.47  % (14227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (14227)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (14227)Memory used [KB]: 10618
% 0.21/0.47  % (14227)Time elapsed: 0.043 s
% 0.21/0.47  % (14227)------------------------------
% 0.21/0.47  % (14227)------------------------------
% 0.21/0.47  % (14222)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (14221)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (14210)Success in time 0.111 s
%------------------------------------------------------------------------------
