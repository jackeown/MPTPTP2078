%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  53 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 (  90 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f29,f34,f40,f95,f113])).

fof(f113,plain,
    ( ~ spl2_1
    | spl2_4
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl2_1
    | spl2_4
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f39,f109])).

fof(f109,plain,
    ( ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X8,X9)))
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(superposition,[],[f24,f94])).

fof(f94,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl2_10
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f24,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl2_1
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f39,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl2_4
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f95,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f20,f93])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f16,f15])).

fof(f15,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f16,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f40,plain,
    ( ~ spl2_4
    | ~ spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f35,f31,f27,f37])).

fof(f27,plain,
    ( spl2_2
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f31,plain,
    ( spl2_3
  <=> r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f35,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ spl2_2
    | spl2_3 ),
    inference(resolution,[],[f33,f28])).

fof(f28,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f33,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f34,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f21,f31])).

fof(f21,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f19,f20])).

fof(f19,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    inference(definition_unfolding,[],[f13,f15])).

fof(f13,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1] : ~ r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))
   => ~ r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : ~ r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f29,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f27])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f25,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f14,f23])).

fof(f14,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:57:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (27265)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (27272)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (27272)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (27280)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f25,f29,f34,f40,f95,f113])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ~spl2_1 | spl2_4 | ~spl2_10),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    $false | (~spl2_1 | spl2_4 | ~spl2_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f39,f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X8,X9)))) ) | (~spl2_1 | ~spl2_10)),
% 0.21/0.48    inference(superposition,[],[f24,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl2_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl2_10 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    spl2_1 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) | spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl2_4 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl2_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f93])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f16,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ~spl2_4 | ~spl2_2 | spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f31,f27,f37])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    spl2_2 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    spl2_3 <=> r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) | (~spl2_2 | spl2_3)),
% 0.21/0.48    inference(resolution,[],[f33,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) ) | ~spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f27])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) | spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f31])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ~spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f31])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 0.21/0.48    inference(backward_demodulation,[],[f19,f20])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ~r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),
% 0.21/0.48    inference(definition_unfolding,[],[f13,f15])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ~r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ~r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1] : ~r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) => ~r1_tarski(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1] : ~r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f27])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 => r1_tarski(X0,X1))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f14,f23])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (27272)------------------------------
% 0.21/0.48  % (27272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27272)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (27272)Memory used [KB]: 6268
% 0.21/0.48  % (27272)Time elapsed: 0.055 s
% 0.21/0.48  % (27272)------------------------------
% 0.21/0.48  % (27272)------------------------------
% 0.21/0.48  % (27264)Success in time 0.124 s
%------------------------------------------------------------------------------
