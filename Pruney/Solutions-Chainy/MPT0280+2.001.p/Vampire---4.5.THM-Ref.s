%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  93 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :  118 ( 176 expanded)
%              Number of equality atoms :   10 (  31 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (23510)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f74,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f34,f38,f44,f51,f55,f67,f70,f73])).

fof(f73,plain,
    ( ~ spl2_2
    | ~ spl2_4
    | spl2_8 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_4
    | spl2_8 ),
    inference(subsumption_resolution,[],[f71,f43])).

fof(f43,plain,
    ( ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f71,plain,
    ( ~ r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ spl2_2
    | spl2_8 ),
    inference(resolution,[],[f66,f33])).

fof(f33,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_2
  <=> ! [X1,X0] :
        ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl2_8
  <=> r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f70,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | spl2_7 ),
    inference(subsumption_resolution,[],[f68,f29])).

fof(f29,plain,
    ( ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_1
  <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f68,plain,
    ( ~ r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1)))
    | ~ spl2_2
    | spl2_7 ),
    inference(resolution,[],[f62,f33])).

fof(f62,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_7
  <=> r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f67,plain,
    ( ~ spl2_7
    | ~ spl2_8
    | spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f56,f53,f48,f64,f60])).

fof(f48,plain,
    ( spl2_5
  <=> r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f53,plain,
    ( spl2_6
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f56,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
    | ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
    | spl2_5
    | ~ spl2_6 ),
    inference(resolution,[],[f54,f50])).

fof(f50,plain,
    ( ~ r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f54,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f55,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f51,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f23,plain,(
    ~ r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) ),
    inference(definition_unfolding,[],[f15,f22,f22])).

fof(f15,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).

fof(f44,plain,
    ( spl2_4
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f39,f36,f28,f42])).

fof(f36,plain,
    ( spl2_3
  <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f39,plain,
    ( ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(superposition,[],[f29,f37])).

fof(f37,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f36])).

% (23522)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f38,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f25,f36])).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f17,f18,f18])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f34,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f20,f32])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f30,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f24,f28])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f16,f22])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:12:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (23515)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (23515)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (23523)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  % (23510)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f30,f34,f38,f44,f51,f55,f67,f70,f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ~spl2_2 | ~spl2_4 | spl2_8),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    $false | (~spl2_2 | ~spl2_4 | spl2_8)),
% 0.21/0.47    inference(subsumption_resolution,[],[f71,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) ) | ~spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl2_4 <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ~r1_tarski(sK1,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | (~spl2_2 | spl2_8)),
% 0.21/0.47    inference(resolution,[],[f66,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    spl2_2 <=> ! [X1,X0] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ~r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) | spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl2_8 <=> r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ~spl2_1 | ~spl2_2 | spl2_7),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    $false | (~spl2_1 | ~spl2_2 | spl2_7)),
% 0.21/0.47    inference(subsumption_resolution,[],[f68,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) ) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    spl2_1 <=> ! [X1,X0] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ~r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) | (~spl2_2 | spl2_7)),
% 0.21/0.47    inference(resolution,[],[f62,f33])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) | spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl2_7 <=> r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ~spl2_7 | ~spl2_8 | spl2_5 | ~spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f56,f53,f48,f64,f60])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl2_5 <=> r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl2_6 <=> ! [X1,X0,X2] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ~r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) | ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) | (spl2_5 | ~spl2_6)),
% 0.21/0.47    inference(resolution,[],[f54,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ~r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1)))) | spl2_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f48])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) ) | ~spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f53])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f21,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f19,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ~spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f48])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ~r1_tarski(k3_tarski(k1_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k1_enumset1(sK0,sK0,sK1))))),
% 0.21/0.47    inference(definition_unfolding,[],[f15,f22,f22])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f7])).
% 0.21/0.47  fof(f7,conjecture,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl2_4 | ~spl2_1 | ~spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f39,f36,f28,f42])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    spl2_3 <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) ) | (~spl2_1 | ~spl2_3)),
% 0.21/0.47    inference(superposition,[],[f29,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) ) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f36])).
% 0.21/0.47  % (23522)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f36])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f17,f18,f18])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f20,f32])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f28])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f16,f22])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (23515)------------------------------
% 0.21/0.47  % (23515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23515)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (23515)Memory used [KB]: 6140
% 0.21/0.47  % (23515)Time elapsed: 0.047 s
% 0.21/0.47  % (23515)------------------------------
% 0.21/0.47  % (23515)------------------------------
% 0.21/0.47  % (23513)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (23507)Success in time 0.109 s
%------------------------------------------------------------------------------
