%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  54 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 126 expanded)
%              Number of equality atoms :   29 (  52 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f28,f32,f35])).

fof(f35,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f34])).

fof(f34,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f33,f22])).

fof(f22,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl2_1
  <=> k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f33,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f25,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f14,f12])).

fof(f12,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f25,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

% (12335)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f32,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f31])).

fof(f31,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f30,f26])).

fof(f26,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f30,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f29])).

fof(f29,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(superposition,[],[f18,f21])).

fof(f21,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f13,f12])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f16,f24,f20])).

fof(f16,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f10,f12])).

fof(f10,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
        & ( r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f27,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f15,f24,f20])).

fof(f15,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f11,f12])).

fof(f11,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:02:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (12343)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (12343)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f27,f28,f32,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    spl2_1 | ~spl2_2),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    $false | (spl2_1 | ~spl2_2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f33,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl2_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    spl2_1 <=> k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl2_2),
% 0.21/0.46    inference(resolution,[],[f25,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f14,f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0))),
% 0.21/0.46    inference(nnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    r2_hidden(sK0,sK1) | ~spl2_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    spl2_2 <=> r2_hidden(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.46  % (12335)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ~spl2_1 | spl2_2),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    $false | (~spl2_1 | spl2_2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f30,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ~r2_hidden(sK0,sK1) | spl2_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f24])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK0,sK1) | ~spl2_1),
% 0.21/0.46    inference(superposition,[],[f18,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl2_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f20])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f13,f12])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    spl2_1 | spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f16,f24,f20])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.46    inference(definition_unfolding,[],[f10,f12])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0,X1] : ((~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0))),
% 0.21/0.46    inference(nnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,plain,(
% 0.21/0.46    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <~> r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 0.21/0.46    inference(negated_conjecture,[],[f3])).
% 0.21/0.46  fof(f3,conjecture,(
% 0.21/0.46    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ~spl2_1 | ~spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f15,f24,f20])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.46    inference(definition_unfolding,[],[f11,f12])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (12343)------------------------------
% 0.21/0.46  % (12343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (12343)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (12343)Memory used [KB]: 6140
% 0.21/0.46  % (12343)Time elapsed: 0.007 s
% 0.21/0.46  % (12343)------------------------------
% 0.21/0.46  % (12343)------------------------------
% 0.21/0.46  % (12325)Success in time 0.096 s
%------------------------------------------------------------------------------
