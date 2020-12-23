%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  54 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :  103 ( 130 expanded)
%              Number of equality atoms :   29 (  39 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f66,f78,f86,f128,f130])).

fof(f130,plain,
    ( spl2_2
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl2_2
    | ~ spl2_11
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f115,f93])).

fof(f93,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl2_13
  <=> r1_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f115,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(sK0))
    | spl2_2
    | ~ spl2_11 ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( sK1 != sK1
    | ~ r1_xboole_0(sK1,k1_tarski(sK0))
    | spl2_2
    | ~ spl2_11 ),
    inference(superposition,[],[f45,f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f45,plain,
    ( sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_2
  <=> sK1 = k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f128,plain,
    ( spl2_1
    | ~ spl2_7
    | ~ spl2_10
    | spl2_13 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl2_1
    | ~ spl2_7
    | ~ spl2_10
    | spl2_13 ),
    inference(subsumption_resolution,[],[f102,f126])).

fof(f126,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_7
    | spl2_13 ),
    inference(unit_resulting_resolution,[],[f94,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != X0
        | r1_xboole_0(X0,X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f94,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(sK0))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f102,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK0))
    | spl2_1
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f40,f77])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f40,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f86,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f27,f84])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f78,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f31,f76])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f66,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f46,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f22,f43])).

fof(f22,plain,(
    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & ~ r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & ~ r2_hidden(X0,X1) )
   => ( sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & ~ r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
       => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

fof(f41,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f38])).

fof(f21,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (29355)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.41  % (29355)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.42  % (29365)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f131,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f41,f46,f66,f78,f86,f128,f130])).
% 0.20/0.42  fof(f130,plain,(
% 0.20/0.42    spl2_2 | ~spl2_11 | ~spl2_13),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f129])).
% 0.20/0.42  fof(f129,plain,(
% 0.20/0.42    $false | (spl2_2 | ~spl2_11 | ~spl2_13)),
% 0.20/0.42    inference(subsumption_resolution,[],[f115,f93])).
% 0.20/0.42  fof(f93,plain,(
% 0.20/0.42    r1_xboole_0(sK1,k1_tarski(sK0)) | ~spl2_13),
% 0.20/0.42    inference(avatar_component_clause,[],[f92])).
% 0.20/0.42  fof(f92,plain,(
% 0.20/0.42    spl2_13 <=> r1_xboole_0(sK1,k1_tarski(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.42  fof(f115,plain,(
% 0.20/0.42    ~r1_xboole_0(sK1,k1_tarski(sK0)) | (spl2_2 | ~spl2_11)),
% 0.20/0.42    inference(trivial_inequality_removal,[],[f110])).
% 0.20/0.42  fof(f110,plain,(
% 0.20/0.42    sK1 != sK1 | ~r1_xboole_0(sK1,k1_tarski(sK0)) | (spl2_2 | ~spl2_11)),
% 0.20/0.42    inference(superposition,[],[f45,f85])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl2_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f84])).
% 0.20/0.42  fof(f84,plain,(
% 0.20/0.42    spl2_11 <=> ! [X1,X0] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f43])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl2_2 <=> sK1 = k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f128,plain,(
% 0.20/0.42    spl2_1 | ~spl2_7 | ~spl2_10 | spl2_13),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f127])).
% 0.20/0.42  fof(f127,plain,(
% 0.20/0.42    $false | (spl2_1 | ~spl2_7 | ~spl2_10 | spl2_13)),
% 0.20/0.42    inference(subsumption_resolution,[],[f102,f126])).
% 0.20/0.42  fof(f126,plain,(
% 0.20/0.42    sK1 != k4_xboole_0(sK1,k1_tarski(sK0)) | (~spl2_7 | spl2_13)),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f94,f65])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) ) | ~spl2_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f64])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    spl2_7 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.42  fof(f94,plain,(
% 0.20/0.42    ~r1_xboole_0(sK1,k1_tarski(sK0)) | spl2_13),
% 0.20/0.42    inference(avatar_component_clause,[],[f92])).
% 0.20/0.42  fof(f102,plain,(
% 0.20/0.42    sK1 = k4_xboole_0(sK1,k1_tarski(sK0)) | (spl2_1 | ~spl2_10)),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f40,f77])).
% 0.20/0.42  fof(f77,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) ) | ~spl2_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f76])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    spl2_10 <=> ! [X1,X0] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    ~r2_hidden(sK0,sK1) | spl2_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f38])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f86,plain,(
% 0.20/0.42    spl2_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f27,f84])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    spl2_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f31,f76])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.20/0.42    inference(nnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,axiom,(
% 0.20/0.42    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    spl2_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f29,f64])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.42    inference(nnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ~spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f43])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & ~r2_hidden(sK0,sK1)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ? [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & ~r2_hidden(X0,X1)) => (sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & ~r2_hidden(sK0,sK1))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ? [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & ~r2_hidden(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.20/0.42    inference(negated_conjecture,[],[f13])).
% 0.20/0.42  fof(f13,conjecture,(
% 0.20/0.42    ! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    ~spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f21,f38])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ~r2_hidden(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (29355)------------------------------
% 0.20/0.42  % (29355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (29355)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (29355)Memory used [KB]: 6140
% 0.20/0.42  % (29355)Time elapsed: 0.037 s
% 0.20/0.42  % (29355)------------------------------
% 0.20/0.42  % (29355)------------------------------
% 0.20/0.42  % (29349)Success in time 0.071 s
%------------------------------------------------------------------------------
