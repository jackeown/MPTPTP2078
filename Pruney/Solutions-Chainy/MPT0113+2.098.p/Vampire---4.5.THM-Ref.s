%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  93 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :   86 ( 186 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f56,f169])).

fof(f169,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f159])).

fof(f159,plain,
    ( sK0 != sK0
    | spl3_2 ),
    inference(superposition,[],[f65,f148])).

fof(f148,plain,(
    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f141,f38])).

fof(f38,plain,(
    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f21,f25])).

fof(f25,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f17,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f141,plain,(
    ! [X1] : k5_xboole_0(sK0,k3_xboole_0(sK0,X1)) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X1))) ),
    inference(superposition,[],[f28,f55])).

fof(f55,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f51,f21])).

fof(f51,plain,(
    r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f44,f26])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f44,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f24,f25])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f23,f20,f20])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f65,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | spl3_2 ),
    inference(resolution,[],[f27,f36])).

fof(f36,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f56,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f51,f32])).

fof(f32,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f37,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f18,f34,f30])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:15:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (31085)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (31080)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (31082)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (31078)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (31079)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (31078)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f170,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f37,f56,f169])).
% 0.22/0.48  fof(f169,plain,(
% 0.22/0.48    spl3_2),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f168])).
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    $false | spl3_2),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f159])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    sK0 != sK0 | spl3_2),
% 0.22/0.48    inference(superposition,[],[f65,f148])).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 0.22/0.48    inference(superposition,[],[f141,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.22/0.48    inference(resolution,[],[f21,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.22/0.48    inference(definition_unfolding,[],[f17,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.48    inference(negated_conjecture,[],[f7])).
% 0.22/0.48  fof(f7,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    ( ! [X1] : (k5_xboole_0(sK0,k3_xboole_0(sK0,X1)) = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X1)))) )),
% 0.22/0.48    inference(superposition,[],[f28,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    sK0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.48    inference(resolution,[],[f51,f21])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    r1_tarski(sK0,sK1)),
% 0.22/0.48    inference(resolution,[],[f44,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f19,f20])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X0) | r1_tarski(sK0,X0)) )),
% 0.22/0.48    inference(resolution,[],[f24,f25])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f23,f20,f20])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | spl3_2),
% 0.22/0.48    inference(resolution,[],[f27,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ~r1_xboole_0(sK0,sK2) | spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0) )),
% 0.22/0.48    inference(definition_unfolding,[],[f22,f20])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 0.22/0.48    inference(unused_predicate_definition_removal,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    spl3_1),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    $false | spl3_1),
% 0.22/0.48    inference(resolution,[],[f51,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ~spl3_1 | ~spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f34,f30])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (31078)------------------------------
% 0.22/0.48  % (31078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (31078)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (31078)Memory used [KB]: 6140
% 0.22/0.48  % (31078)Time elapsed: 0.055 s
% 0.22/0.48  % (31078)------------------------------
% 0.22/0.48  % (31078)------------------------------
% 0.22/0.48  % (31075)Success in time 0.116 s
%------------------------------------------------------------------------------
