%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 120 expanded)
%              Number of leaves         :   15 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  178 ( 296 expanded)
%              Number of equality atoms :   39 (  75 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f48,f52,f61,f65,f72,f77,f81,f86,f88])).

fof(f88,plain,
    ( spl2_8
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f87,f84,f58,f69])).

fof(f69,plain,
    ( spl2_8
  <=> r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f58,plain,
    ( spl2_7
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f84,plain,
    ( spl2_9
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(k1_enumset1(sK0,sK0,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f87,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(resolution,[],[f85,f59])).

fof(f59,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(k1_enumset1(sK0,sK0,X0),sK1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f86,plain,
    ( spl2_9
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f82,f58,f50,f84])).

fof(f50,plain,
    ( spl2_5
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k1_enumset1(X0,X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f82,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(k1_enumset1(sK0,sK0,X0),sK1) )
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(resolution,[],[f59,f51])).

fof(f51,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X2)
        | ~ r2_hidden(X1,X2)
        | r1_tarski(k1_enumset1(X0,X0,X1),X2) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f81,plain,
    ( ~ spl2_3
    | spl2_6
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | ~ spl2_3
    | spl2_6
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f56,f75])).

fof(f75,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f71,f43])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f71,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f56,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_6
  <=> k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f77,plain,
    ( ~ spl2_2
    | spl2_7
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | ~ spl2_2
    | spl2_7
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f73,f60])).

fof(f60,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f73,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(resolution,[],[f71,f39])).

fof(f39,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k1_enumset1(X0,X0,X1),X2)
        | r2_hidden(X0,X2) )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_2
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X2)
        | ~ r1_tarski(k1_enumset1(X0,X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f72,plain,
    ( spl2_8
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f67,f54,f46,f69])).

fof(f46,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f67,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f47,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f65,plain,
    ( spl2_6
    | spl2_7 ),
    inference(avatar_split_clause,[],[f64,f58,f54])).

fof(f64,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))
    | spl2_7 ),
    inference(subsumption_resolution,[],[f27,f60])).

fof(f27,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f15,f19,f25])).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f18,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f15,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f61,plain,
    ( ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f26,f58,f54])).

fof(f26,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f16,f19,f25])).

fof(f16,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f30,f50])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f24,f18])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f48,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f29,f46])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f44,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f28,f42])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f32,f38])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k1_enumset1(X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f22,f18])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:46:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (28496)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (28503)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (28503)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f40,f44,f48,f52,f61,f65,f72,f77,f81,f86,f88])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl2_8 | ~spl2_7 | ~spl2_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f87,f84,f58,f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl2_8 <=> r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl2_7 <=> r2_hidden(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl2_9 <=> ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k1_enumset1(sK0,sK0,X0),sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) | (~spl2_7 | ~spl2_9)),
% 0.21/0.47    inference(resolution,[],[f85,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1) | ~spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k1_enumset1(sK0,sK0,X0),sK1)) ) | ~spl2_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f84])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl2_9 | ~spl2_5 | ~spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f82,f58,f50,f84])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl2_5 <=> ! [X1,X0,X2] : (r1_tarski(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k1_enumset1(sK0,sK0,X0),sK1)) ) | (~spl2_5 | ~spl2_7)),
% 0.21/0.47    inference(resolution,[],[f59,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k1_enumset1(X0,X0,X1),X2)) ) | ~spl2_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ~spl2_3 | spl2_6 | ~spl2_8),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    $false | (~spl2_3 | spl2_6 | ~spl2_8)),
% 0.21/0.47    inference(subsumption_resolution,[],[f56,f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) | (~spl2_3 | ~spl2_8)),
% 0.21/0.47    inference(resolution,[],[f71,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl2_3 <=> ! [X1,X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) | ~spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f69])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) | spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl2_6 <=> k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ~spl2_2 | spl2_7 | ~spl2_8),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    $false | (~spl2_2 | spl2_7 | ~spl2_8)),
% 0.21/0.47    inference(subsumption_resolution,[],[f73,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ~r2_hidden(sK0,sK1) | spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1) | (~spl2_2 | ~spl2_8)),
% 0.21/0.47    inference(resolution,[],[f71,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X0,X2)) ) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    spl2_2 <=> ! [X1,X0,X2] : (r2_hidden(X0,X2) | ~r1_tarski(k1_enumset1(X0,X0,X1),X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl2_8 | ~spl2_4 | ~spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f67,f54,f46,f69])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl2_4 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) | (~spl2_4 | ~spl2_6)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) | (~spl2_4 | ~spl2_6)),
% 0.21/0.47    inference(superposition,[],[f47,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) | ~spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f54])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) ) | ~spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f46])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl2_6 | spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f64,f58,f54])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) | spl2_7),
% 0.21/0.47    inference(subsumption_resolution,[],[f27,f60])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1) | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))),
% 0.21/0.47    inference(definition_unfolding,[],[f15,f19,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f17,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ~spl2_6 | ~spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f58,f54])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))),
% 0.21/0.47    inference(definition_unfolding,[],[f16,f19,f25])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f50])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f24,f18])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.47    inference(nnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f46])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f20,f19])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f42])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f21,f19])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f38])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k1_enumset1(X0,X0,X1),X2)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f22,f18])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (28503)------------------------------
% 0.21/0.47  % (28503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (28503)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (28503)Memory used [KB]: 6140
% 0.21/0.47  % (28503)Time elapsed: 0.057 s
% 0.21/0.47  % (28503)------------------------------
% 0.21/0.47  % (28503)------------------------------
% 0.21/0.47  % (28495)Success in time 0.104 s
%------------------------------------------------------------------------------
