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
% DateTime   : Thu Dec  3 12:40:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 104 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 186 expanded)
%              Number of equality atoms :   27 (  69 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f44,f48,f52,f58,f64,f75,f78])).

fof(f78,plain,
    ( ~ spl2_6
    | spl2_7
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl2_6
    | spl2_7
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f76,f63])).

fof(f63,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_7
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f76,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(resolution,[],[f74,f57])).

fof(f57,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_6
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f75,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f59,f50,f42,f73])).

fof(f42,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f50,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) )
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(resolution,[],[f51,f43])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f64,plain,(
    ~ spl2_7 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f18,f27,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f58,plain,
    ( spl2_6
    | spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f53,f46,f33,f55])).

fof(f33,plain,
    ( spl2_1
  <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f46,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f53,plain,
    ( r2_hidden(sK0,sK1)
    | spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f47,f35])).

fof(f35,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f52,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f31,f50])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f48,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f30,f46])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f44,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f42])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f36,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f29,f33])).

fof(f29,plain,(
    ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f17,f27])).

fof(f17,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (9579)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.45  % (9586)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.45  % (9586)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f36,f44,f48,f52,f58,f64,f75,f78])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    ~spl2_6 | spl2_7 | ~spl2_9),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f77])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    $false | (~spl2_6 | spl2_7 | ~spl2_9)),
% 0.21/0.45    inference(subsumption_resolution,[],[f76,f63])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl2_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f61])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    spl2_7 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | (~spl2_6 | ~spl2_9)),
% 0.21/0.45    inference(resolution,[],[f74,f57])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    r2_hidden(sK0,sK1) | ~spl2_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f55])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    spl2_6 <=> r2_hidden(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) ) | ~spl2_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f73])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    spl2_9 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    spl2_9 | ~spl2_3 | ~spl2_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f59,f50,f42,f73])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    spl2_3 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    spl2_5 <=> ! [X1,X0] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) ) | (~spl2_3 | ~spl2_5)),
% 0.21/0.45    inference(resolution,[],[f51,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl2_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f42])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl2_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f50])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ~spl2_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f28,f61])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.45    inference(definition_unfolding,[],[f18,f27,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f19,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f21,f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.45    inference(negated_conjecture,[],[f8])).
% 0.21/0.45  fof(f8,conjecture,(
% 0.21/0.45    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    spl2_6 | spl2_1 | ~spl2_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f53,f46,f33,f55])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    spl2_1 <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    spl2_4 <=> ! [X1,X0] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    r2_hidden(sK0,sK1) | (spl2_1 | ~spl2_4)),
% 0.21/0.45    inference(resolution,[],[f47,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl2_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f33])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) ) | ~spl2_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f46])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    spl2_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f31,f50])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f24,f27])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 0.21/0.45    inference(unused_predicate_definition_removal,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    spl2_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f30,f46])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f22,f27])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    spl2_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f42])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ~spl2_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f29,f33])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.45    inference(definition_unfolding,[],[f17,f27])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (9586)------------------------------
% 0.21/0.45  % (9586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (9586)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (9586)Memory used [KB]: 6140
% 0.21/0.45  % (9586)Time elapsed: 0.057 s
% 0.21/0.45  % (9586)------------------------------
% 0.21/0.45  % (9586)------------------------------
% 0.21/0.46  % (9578)Success in time 0.1 s
%------------------------------------------------------------------------------
