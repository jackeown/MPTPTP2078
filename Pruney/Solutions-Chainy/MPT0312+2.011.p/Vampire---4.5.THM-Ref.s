%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  71 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 142 expanded)
%              Number of equality atoms :   31 (  62 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f445,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f372,f375,f444])).

fof(f444,plain,(
    spl4_22 ),
    inference(avatar_contradiction_clause,[],[f443])).

fof(f443,plain,
    ( $false
    | spl4_22 ),
    inference(resolution,[],[f428,f15])).

fof(f15,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(f428,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl4_22 ),
    inference(trivial_inequality_removal,[],[f427])).

fof(f427,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2)
    | ~ r1_tarski(sK2,sK3)
    | spl4_22 ),
    inference(forward_demodulation,[],[f413,f17])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f413,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k4_xboole_0(sK2,k1_xboole_0))
    | ~ r1_tarski(sK2,sK3)
    | spl4_22 ),
    inference(superposition,[],[f371,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f371,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f369])).

fof(f369,plain,
    ( spl4_22
  <=> k2_zfmisc_1(sK0,sK2) = k2_zfmisc_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f375,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | spl4_21 ),
    inference(resolution,[],[f367,f14])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f367,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f365])).

fof(f365,plain,
    ( spl4_21
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f372,plain,
    ( ~ spl4_21
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f363,f369,f365])).

fof(f363,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ r1_tarski(sK0,sK1) ),
    inference(forward_demodulation,[],[f344,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f19,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f344,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)))
    | ~ r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f22,f72])).

fof(f72,plain,(
    ! [X6,X4,X5,X3] :
      ( k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k2_zfmisc_1(X3,k4_xboole_0(X5,k4_xboole_0(X5,X6)))
      | ~ r1_tarski(X3,X4) ) ),
    inference(forward_demodulation,[],[f59,f17])).

fof(f59,plain,(
    ! [X6,X4,X5,X3] :
      ( k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k2_zfmisc_1(k4_xboole_0(X3,k1_xboole_0),k4_xboole_0(X5,k4_xboole_0(X5,X6)))
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f24,f20])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f21,f19,f19,f19])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f22,plain,(
    k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))) ),
    inference(definition_unfolding,[],[f16,f19])).

fof(f16,plain,(
    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:37:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (15403)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (15398)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (15402)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (15401)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (15414)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (15402)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f445,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f372,f375,f444])).
% 0.21/0.48  fof(f444,plain,(
% 0.21/0.48    spl4_22),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f443])).
% 0.21/0.48  fof(f443,plain,(
% 0.21/0.48    $false | spl4_22),
% 0.21/0.48    inference(resolution,[],[f428,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    r1_tarski(sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).
% 0.21/0.48  fof(f428,plain,(
% 0.21/0.48    ~r1_tarski(sK2,sK3) | spl4_22),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f427])).
% 0.21/0.48  fof(f427,plain,(
% 0.21/0.48    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2) | ~r1_tarski(sK2,sK3) | spl4_22),
% 0.21/0.48    inference(forward_demodulation,[],[f413,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.48  fof(f413,plain,(
% 0.21/0.48    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k4_xboole_0(sK2,k1_xboole_0)) | ~r1_tarski(sK2,sK3) | spl4_22),
% 0.21/0.48    inference(superposition,[],[f371,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.48  fof(f371,plain,(
% 0.21/0.48    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) | spl4_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f369])).
% 0.21/0.48  fof(f369,plain,(
% 0.21/0.48    spl4_22 <=> k2_zfmisc_1(sK0,sK2) = k2_zfmisc_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.48  fof(f375,plain,(
% 0.21/0.48    spl4_21),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f374])).
% 0.21/0.48  fof(f374,plain,(
% 0.21/0.48    $false | spl4_21),
% 0.21/0.48    inference(resolution,[],[f367,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f367,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | spl4_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f365])).
% 0.21/0.48  fof(f365,plain,(
% 0.21/0.48    spl4_21 <=> r1_tarski(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.49  fof(f372,plain,(
% 0.21/0.49    ~spl4_21 | ~spl4_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f363,f369,f365])).
% 0.21/0.49  fof(f363,plain,(
% 0.21/0.49    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) | ~r1_tarski(sK0,sK1)),
% 0.21/0.49    inference(forward_demodulation,[],[f344,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f18,f19,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.49  fof(f344,plain,(
% 0.21/0.49    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK2))) | ~r1_tarski(sK0,sK1)),
% 0.21/0.49    inference(superposition,[],[f22,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k2_zfmisc_1(X3,k4_xboole_0(X5,k4_xboole_0(X5,X6))) | ~r1_tarski(X3,X4)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f59,f17])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k2_zfmisc_1(X3,X5),k4_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6))) = k2_zfmisc_1(k4_xboole_0(X3,k1_xboole_0),k4_xboole_0(X5,k4_xboole_0(X5,X6))) | ~r1_tarski(X3,X4)) )),
% 0.21/0.49    inference(superposition,[],[f24,f20])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f21,f19,f19,f19])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    inference(definition_unfolding,[],[f16,f19])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (15402)------------------------------
% 0.21/0.49  % (15402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15402)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (15402)Memory used [KB]: 6396
% 0.21/0.49  % (15402)Time elapsed: 0.060 s
% 0.21/0.49  % (15402)------------------------------
% 0.21/0.49  % (15402)------------------------------
% 0.21/0.49  % (15412)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (15399)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (15396)Success in time 0.126 s
%------------------------------------------------------------------------------
