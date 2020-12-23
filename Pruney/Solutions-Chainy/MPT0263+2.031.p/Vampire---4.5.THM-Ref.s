%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 101 expanded)
%              Number of leaves         :   15 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :  102 ( 170 expanded)
%              Number of equality atoms :   32 (  75 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f42,f46,f51,f58,f62,f65])).

fof(f65,plain,
    ( ~ spl2_3
    | spl2_6
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | ~ spl2_3
    | spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f63,f57])).

fof(f57,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_6
  <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f63,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f61,f41])).

fof(f41,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_enumset1(X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k1_enumset1(X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_enumset1(X0,X0,X0)))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f62,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_enumset1(X0,X0,X0)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f22,f19,f22])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f18])).

fof(f18,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f58,plain,
    ( ~ spl2_6
    | ~ spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f52,f48,f44,f55])).

fof(f44,plain,
    ( spl2_4
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f48,plain,
    ( spl2_5
  <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f52,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | ~ spl2_4
    | spl2_5 ),
    inference(superposition,[],[f50,f45])).

fof(f45,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f50,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f51,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f23,plain,(
    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f15,f22,f19,f22])).

fof(f15,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f46,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f25,f44])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f17,f19,f19])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f42,plain,
    ( spl2_3
    | spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f37,f34,f29,f39])).

fof(f29,plain,
    ( spl2_1
  <=> r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f34,plain,
    ( spl2_2
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_enumset1(X0,X0,X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f37,plain,
    ( r2_hidden(sK0,sK1)
    | spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f35,f31])).

fof(f31,plain,
    ( ~ r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f35,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_enumset1(X0,X0,X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f36,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f34])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_enumset1(X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f32,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f24,f29])).

fof(f24,plain,(
    ~ r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f14,f22])).

fof(f14,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (31918)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.43  % (31918)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f32,f36,f42,f46,f51,f58,f62,f65])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    ~spl2_3 | spl2_6 | ~spl2_7),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f64])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    $false | (~spl2_3 | spl2_6 | ~spl2_7)),
% 0.20/0.43    inference(subsumption_resolution,[],[f63,f57])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | spl2_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f55])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    spl2_6 <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | (~spl2_3 | ~spl2_7)),
% 0.20/0.43    inference(resolution,[],[f61,f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    r2_hidden(sK0,sK1) | ~spl2_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f39])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    spl2_3 <=> r2_hidden(sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_enumset1(X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_enumset1(X0,X0,X0)))) ) | ~spl2_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f60])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    spl2_7 <=> ! [X1,X0] : (k1_enumset1(X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) | ~r2_hidden(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    spl2_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f27,f60])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_enumset1(X0,X0,X0))) | ~r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f21,f22,f19,f22])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f16,f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ~spl2_6 | ~spl2_4 | spl2_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f52,f48,f44,f55])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    spl2_4 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    spl2_5 <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | (~spl2_4 | spl2_5)),
% 0.20/0.43    inference(superposition,[],[f50,f45])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl2_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f44])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) | spl2_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f48])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ~spl2_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f23,f48])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))),
% 0.20/0.43    inference(definition_unfolding,[],[f15,f22,f19,f22])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.43    inference(negated_conjecture,[],[f7])).
% 0.20/0.43  fof(f7,conjecture,(
% 0.20/0.43    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    spl2_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f44])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f17,f19,f19])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    spl2_3 | spl2_1 | ~spl2_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f37,f34,f29,f39])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    spl2_1 <=> r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    spl2_2 <=> ! [X1,X0] : (r1_xboole_0(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    r2_hidden(sK0,sK1) | (spl2_1 | ~spl2_2)),
% 0.20/0.43    inference(resolution,[],[f35,f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ~r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) | spl2_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f29])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)) ) | ~spl2_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f34])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    spl2_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f26,f34])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f20,f22])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ~spl2_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f29])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ~r1_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 0.20/0.43    inference(definition_unfolding,[],[f14,f22])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (31918)------------------------------
% 0.20/0.43  % (31918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (31918)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (31918)Memory used [KB]: 6140
% 0.20/0.43  % (31918)Time elapsed: 0.005 s
% 0.20/0.43  % (31918)------------------------------
% 0.20/0.43  % (31918)------------------------------
% 0.20/0.43  % (31910)Success in time 0.075 s
%------------------------------------------------------------------------------
