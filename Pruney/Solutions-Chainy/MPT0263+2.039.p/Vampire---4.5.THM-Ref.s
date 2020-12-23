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
% DateTime   : Thu Dec  3 12:40:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 118 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :  130 ( 221 expanded)
%              Number of equality atoms :   37 (  88 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f37,f41,f47,f52,f59,f63,f69,f72])).

fof(f72,plain,
    ( ~ spl2_4
    | spl2_6
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | ~ spl2_4
    | spl2_6
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f70,f58])).

fof(f58,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_6
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f70,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(resolution,[],[f68,f46])).

fof(f46,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k2_enumset1(sK0,sK0,sK0,X0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,X0)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_8
  <=> ! [X0] :
        ( k2_enumset1(sK0,sK0,sK0,X0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,X0))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f69,plain,
    ( spl2_8
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f65,f61,f44,f35,f67])).

fof(f35,plain,
    ( spl2_2
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f61,plain,
    ( spl2_7
  <=> ! [X1,X0,X2] :
        ( k2_enumset1(X0,X0,X0,X2) = k3_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f65,plain,
    ( ! [X0] :
        ( k2_enumset1(sK0,sK0,sK0,X0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,X0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f64,f36])).

fof(f36,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k2_enumset1(sK0,sK0,sK0,X0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,X0),sK1) )
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(resolution,[],[f62,f46])).

fof(f62,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X2,X1)
        | k2_enumset1(X0,X0,X0,X2) = k3_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f63,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X2) = k3_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f59,plain,
    ( ~ spl2_6
    | ~ spl2_2
    | spl2_5 ),
    inference(avatar_split_clause,[],[f53,f49,f35,f56])).

fof(f49,plain,
    ( spl2_5
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f53,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl2_2
    | spl2_5 ),
    inference(superposition,[],[f51,f36])).

fof(f51,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f52,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f16,f24,f24])).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f17,f23])).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f16,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).

fof(f13,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f47,plain,
    ( spl2_4
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f42,f39,f30,f44])).

fof(f30,plain,
    ( spl2_1
  <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f39,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f42,plain,
    ( r2_hidden(sK0,sK1)
    | spl2_1
    | ~ spl2_3 ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f41,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f27,f39])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f24])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f33,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f26,f30])).

fof(f26,plain,(
    ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f15,f24])).

fof(f15,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 11:12:08 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.45  % (19471)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (19478)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (19478)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f33,f37,f41,f47,f52,f59,f63,f69,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ~spl2_4 | spl2_6 | ~spl2_8),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    $false | (~spl2_4 | spl2_6 | ~spl2_8)),
% 0.21/0.47    inference(subsumption_resolution,[],[f70,f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl2_6 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl2_4 | ~spl2_8)),
% 0.21/0.47    inference(resolution,[],[f68,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1) | ~spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl2_4 <=> r2_hidden(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,sK1) | k2_enumset1(sK0,sK0,sK0,X0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,X0))) ) | ~spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f67])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl2_8 <=> ! [X0] : (k2_enumset1(sK0,sK0,sK0,X0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,X0)) | ~r2_hidden(X0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl2_8 | ~spl2_2 | ~spl2_4 | ~spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f65,f61,f44,f35,f67])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    spl2_2 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl2_7 <=> ! [X1,X0,X2] : (k2_enumset1(X0,X0,X0,X2) = k3_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X0] : (k2_enumset1(sK0,sK0,sK0,X0) = k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,X0)) | ~r2_hidden(X0,sK1)) ) | (~spl2_2 | ~spl2_4 | ~spl2_7)),
% 0.21/0.47    inference(forward_demodulation,[],[f64,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f35])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,sK1) | k2_enumset1(sK0,sK0,sK0,X0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,X0),sK1)) ) | (~spl2_4 | ~spl2_7)),
% 0.21/0.47    inference(resolution,[],[f62,f46])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X2) = k3_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)) ) | ~spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f61])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X2) = k3_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f22,f23,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f19,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ~spl2_6 | ~spl2_2 | spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f53,f49,f35,f56])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl2_5 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl2_2 | spl2_5)),
% 0.21/0.47    inference(superposition,[],[f51,f36])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl2_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f49])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ~spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f49])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    k2_enumset1(sK0,sK0,sK0,sK0) != k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.47    inference(definition_unfolding,[],[f16,f24,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f17,f23])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f7])).
% 0.21/0.47  fof(f7,conjecture,(
% 0.21/0.47    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl2_4 | spl2_1 | ~spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f42,f39,f30,f44])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    spl2_1 <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    spl2_3 <=> ! [X1,X0] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1) | (spl2_1 | ~spl2_3)),
% 0.21/0.47    inference(resolution,[],[f40,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f30])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) ) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f39])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f39])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f20,f24])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f18,f35])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ~spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f30])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.47    inference(definition_unfolding,[],[f15,f24])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (19478)------------------------------
% 0.21/0.47  % (19478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19478)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (19478)Memory used [KB]: 6140
% 0.21/0.47  % (19478)Time elapsed: 0.060 s
% 0.21/0.47  % (19478)------------------------------
% 0.21/0.47  % (19478)------------------------------
% 0.21/0.48  % (19486)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (19470)Success in time 0.123 s
%------------------------------------------------------------------------------
