%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 (  95 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  158 ( 224 expanded)
%              Number of equality atoms :   47 (  71 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f39,f48,f50,f54,f59,f64,f87,f95,f104,f112])).

fof(f112,plain,
    ( ~ spl2_1
    | spl2_5
    | ~ spl2_7
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | ~ spl2_1
    | spl2_5
    | ~ spl2_7
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f110,f46])).

fof(f46,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_5
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

% (22523)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f110,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f109,f63])).

fof(f63,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_7
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f109,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f105,f30])).

fof(f30,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_1
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f105,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(superposition,[],[f86,f103])).

fof(f103,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_14
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f86,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_11
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f104,plain,
    ( spl2_14
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f99,f93,f41,f101])).

fof(f41,plain,
    ( spl2_4
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f93,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f99,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(resolution,[],[f94,f43])).

fof(f43,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f95,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f27,f93])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f87,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f22,f85])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f64,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f60,f57,f37,f62])).

fof(f37,plain,
    ( spl2_3
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f57,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f60,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(resolution,[],[f58,f38])).

fof(f38,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f54,plain,
    ( ~ spl2_2
    | spl2_4
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | ~ spl2_2
    | spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f52,f42])).

fof(f42,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f52,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(superposition,[],[f34,f47])).

fof(f47,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f34,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_2
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f50,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f49,f45,f41])).

fof(f49,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f17,f47])).

fof(f17,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( sK0 != k4_xboole_0(sK0,sK1)
      | ~ r1_xboole_0(sK0,sK1) )
    & ( sK0 = k4_xboole_0(sK0,sK1)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ( k4_xboole_0(X0,X1) != X0
          | ~ r1_xboole_0(X0,X1) )
        & ( k4_xboole_0(X0,X1) = X0
          | r1_xboole_0(X0,X1) ) )
   => ( ( sK0 != k4_xboole_0(sK0,sK1)
        | ~ r1_xboole_0(sK0,sK1) )
      & ( sK0 = k4_xboole_0(sK0,sK1)
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f48,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f16,f45,f41])).

fof(f16,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f20,f37])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

% (22513)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f33])).

fof(f19,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f31,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f18,f29])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (22516)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (22521)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (22516)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f113,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f31,f35,f39,f48,f50,f54,f59,f64,f87,f95,f104,f112])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    ~spl2_1 | spl2_5 | ~spl2_7 | ~spl2_11 | ~spl2_14),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f111])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    $false | (~spl2_1 | spl2_5 | ~spl2_7 | ~spl2_11 | ~spl2_14)),
% 0.20/0.46    inference(subsumption_resolution,[],[f110,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    sK0 != k4_xboole_0(sK0,sK1) | spl2_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    spl2_5 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.46  % (22523)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    sK0 = k4_xboole_0(sK0,sK1) | (~spl2_1 | ~spl2_7 | ~spl2_11 | ~spl2_14)),
% 0.20/0.46    inference(forward_demodulation,[],[f109,f63])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) ) | ~spl2_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f62])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    spl2_7 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.46  fof(f109,plain,(
% 0.20/0.46    k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) | (~spl2_1 | ~spl2_11 | ~spl2_14)),
% 0.20/0.46    inference(forward_demodulation,[],[f105,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    spl2_1 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | (~spl2_11 | ~spl2_14)),
% 0.20/0.46    inference(superposition,[],[f86,f103])).
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f101])).
% 0.20/0.46  fof(f101,plain,(
% 0.20/0.46    spl2_14 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f85])).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    spl2_11 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    spl2_14 | ~spl2_4 | ~spl2_13),
% 0.20/0.46    inference(avatar_split_clause,[],[f99,f93,f41,f101])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    spl2_4 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    spl2_13 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl2_4 | ~spl2_13)),
% 0.20/0.46    inference(resolution,[],[f94,f43])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    r1_xboole_0(sK0,sK1) | ~spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f41])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_13),
% 0.20/0.46    inference(avatar_component_clause,[],[f93])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    spl2_13),
% 0.20/0.46    inference(avatar_split_clause,[],[f27,f93])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f24,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(nnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    spl2_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f85])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    spl2_7 | ~spl2_3 | ~spl2_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f60,f57,f37,f62])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    spl2_3 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    spl2_6 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) ) | (~spl2_3 | ~spl2_6)),
% 0.20/0.46    inference(resolution,[],[f58,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f37])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl2_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f57])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    spl2_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f57])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ~spl2_2 | spl2_4 | ~spl2_5),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f53])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    $false | (~spl2_2 | spl2_4 | ~spl2_5)),
% 0.20/0.46    inference(subsumption_resolution,[],[f52,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ~r1_xboole_0(sK0,sK1) | spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f41])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    r1_xboole_0(sK0,sK1) | (~spl2_2 | ~spl2_5)),
% 0.20/0.46    inference(superposition,[],[f34,f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    sK0 = k4_xboole_0(sK0,sK1) | ~spl2_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f45])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    spl2_2 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ~spl2_4 | ~spl2_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f49,f45,f41])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ~r1_xboole_0(sK0,sK1) | ~spl2_5),
% 0.20/0.46    inference(subsumption_resolution,[],[f17,f47])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    (sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(nnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.46    inference(negated_conjecture,[],[f8])).
% 0.20/0.46  fof(f8,conjecture,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    spl2_4 | spl2_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f16,f45,f41])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    spl2_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f20,f37])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  % (22513)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    spl2_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f33])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    spl2_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f18,f29])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (22516)------------------------------
% 0.20/0.47  % (22516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22516)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (22516)Memory used [KB]: 6140
% 0.20/0.47  % (22516)Time elapsed: 0.057 s
% 0.20/0.47  % (22516)------------------------------
% 0.20/0.47  % (22516)------------------------------
% 0.20/0.47  % (22508)Success in time 0.111 s
%------------------------------------------------------------------------------
