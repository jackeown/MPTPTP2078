%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  81 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :  115 ( 164 expanded)
%              Number of equality atoms :    7 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (4207)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f71,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f31,f35,f41,f48,f52,f64,f67,f70])).

fof(f70,plain,
    ( ~ spl2_2
    | ~ spl2_4
    | spl2_8 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_4
    | spl2_8 ),
    inference(subsumption_resolution,[],[f68,f40])).

fof(f40,plain,
    ( ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f68,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK1)))
    | ~ spl2_2
    | spl2_8 ),
    inference(resolution,[],[f63,f30])).

fof(f30,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_2
  <=> ! [X1,X0] :
        ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f63,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1))))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_8
  <=> r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f67,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | spl2_7 ),
    inference(subsumption_resolution,[],[f65,f26])).

fof(f26,plain,
    ( ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl2_1
  <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f65,plain,
    ( ~ r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1)))
    | ~ spl2_2
    | spl2_7 ),
    inference(resolution,[],[f59,f30])).

fof(f59,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1))))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_7
  <=> r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f64,plain,
    ( ~ spl2_7
    | ~ spl2_8
    | spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f53,f50,f45,f61,f57])).

fof(f45,plain,
    ( spl2_5
  <=> r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f50,plain,
    ( spl2_6
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f53,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1))))
    | ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1))))
    | spl2_5
    | ~ spl2_6 ),
    inference(resolution,[],[f51,f47])).

fof(f47,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1))))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f51,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f52,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f19,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f48,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1)))) ),
    inference(definition_unfolding,[],[f14,f17,f17])).

fof(f14,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).

fof(f41,plain,
    ( spl2_4
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f36,f33,f25,f39])).

fof(f33,plain,
    ( spl2_3
  <=> ! [X1,X0] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f36,plain,
    ( ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(superposition,[],[f26,f34])).

fof(f34,plain,
    ( ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f35,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f22,f33])).

fof(f22,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f16,f17,f17])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f31,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f29])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

% (4210)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f27,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f21,f25])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f15,f17])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:25:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.47  % (4223)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.47  % (4222)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (4214)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (4214)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  % (4207)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f27,f31,f35,f41,f48,f52,f64,f67,f70])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ~spl2_2 | ~spl2_4 | spl2_8),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f69])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    $false | (~spl2_2 | ~spl2_4 | spl2_8)),
% 0.22/0.48    inference(subsumption_resolution,[],[f68,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) ) | ~spl2_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    spl2_4 <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ~r1_tarski(sK1,k3_tarski(k2_tarski(sK0,sK1))) | (~spl2_2 | spl2_8)),
% 0.22/0.48    inference(resolution,[],[f63,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    spl2_2 <=> ! [X1,X0] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ~r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1)))) | spl2_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    spl2_8 <=> r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    ~spl2_1 | ~spl2_2 | spl2_7),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    $false | (~spl2_1 | ~spl2_2 | spl2_7)),
% 0.22/0.48    inference(subsumption_resolution,[],[f65,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ) | ~spl2_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    spl2_1 <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ~r1_tarski(sK0,k3_tarski(k2_tarski(sK0,sK1))) | (~spl2_2 | spl2_7)),
% 0.22/0.48    inference(resolution,[],[f59,f30])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1)))) | spl2_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    spl2_7 <=> r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ~spl2_7 | ~spl2_8 | spl2_5 | ~spl2_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f53,f50,f45,f61,f57])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    spl2_5 <=> r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    spl2_6 <=> ! [X1,X0,X2] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ~r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1)))) | ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1)))) | (spl2_5 | ~spl2_6)),
% 0.22/0.48    inference(resolution,[],[f51,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ~r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1)))) | spl2_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f45])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) ) | ~spl2_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f50])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    spl2_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f23,f50])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f19,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ~spl2_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f20,f45])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ~r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k2_tarski(sK0,sK1))))),
% 0.22/0.48    inference(definition_unfolding,[],[f14,f17,f17])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.22/0.48    inference(negated_conjecture,[],[f6])).
% 0.22/0.48  fof(f6,conjecture,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    spl2_4 | ~spl2_1 | ~spl2_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f36,f33,f25,f39])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    spl2_3 <=> ! [X1,X0] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) ) | (~spl2_1 | ~spl2_3)),
% 0.22/0.48    inference(superposition,[],[f26,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) ) | ~spl2_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f33])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    spl2_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f22,f33])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f16,f17,f17])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f29])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  % (4210)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    spl2_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f21,f25])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f15,f17])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (4214)------------------------------
% 0.22/0.48  % (4214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (4214)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (4214)Memory used [KB]: 6140
% 0.22/0.48  % (4214)Time elapsed: 0.058 s
% 0.22/0.48  % (4214)------------------------------
% 0.22/0.48  % (4214)------------------------------
% 0.22/0.48  % (4206)Success in time 0.11 s
%------------------------------------------------------------------------------
