%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  50 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 137 expanded)
%              Number of equality atoms :   27 (  46 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f22,f26,f30,f33,f37])).

fof(f37,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f36])).

fof(f36,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f35,f20])).

fof(f20,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f35,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f34])).

fof(f34,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | ~ r2_hidden(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(superposition,[],[f29,f15])).

fof(f15,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f14,plain,
    ( spl2_1
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f29,plain,
    ( ! [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f33,plain,
    ( spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f32])).

fof(f32,plain,
    ( $false
    | spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f31,f16])).

fof(f16,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f31,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)
    | spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f25,f19])).

fof(f19,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f18])).

fof(f25,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f30,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f11,f28])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f26,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f12,f24])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f22,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f9,f18,f14])).

fof(f9,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( ( r2_hidden(sK0,sK1)
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( ~ r2_hidden(sK0,sK1)
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK0,sK1)
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( ~ r2_hidden(sK0,sK1)
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f21,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f10,f18,f14])).

fof(f10,plain,
    ( r2_hidden(sK0,sK1)
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:35:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (13930)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (13931)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (13934)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.43  % (13934)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f21,f22,f26,f30,f33,f37])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ~spl2_1 | ~spl2_2 | ~spl2_4),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    $false | (~spl2_1 | ~spl2_2 | ~spl2_4)),
% 0.20/0.43    inference(subsumption_resolution,[],[f35,f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    r2_hidden(sK0,sK1) | ~spl2_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    spl2_2 <=> r2_hidden(sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ~r2_hidden(sK0,sK1) | (~spl2_1 | ~spl2_4)),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    k1_tarski(sK0) != k1_tarski(sK0) | ~r2_hidden(sK0,sK1) | (~spl2_1 | ~spl2_4)),
% 0.20/0.43    inference(superposition,[],[f29,f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) | ~spl2_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    spl2_1 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl2_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    spl2_4 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    spl2_1 | spl2_2 | ~spl2_3),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    $false | (spl2_1 | spl2_2 | ~spl2_3)),
% 0.20/0.43    inference(subsumption_resolution,[],[f31,f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | spl2_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f14])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) | (spl2_2 | ~spl2_3)),
% 0.20/0.43    inference(resolution,[],[f25,f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ~r2_hidden(sK0,sK1) | spl2_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f18])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) ) | ~spl2_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    spl2_3 <=> ! [X1,X0] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    spl2_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f11,f28])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.20/0.43    inference(nnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    spl2_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f12,f24])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    spl2_1 | ~spl2_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f9,f18,f14])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    (r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).
% 0.20/0.43  fof(f6,plain,(
% 0.20/0.43    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f5,plain,(
% 0.20/0.43    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 0.20/0.43    inference(nnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,plain,(
% 0.20/0.43    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.20/0.43    inference(negated_conjecture,[],[f2])).
% 0.20/0.43  fof(f2,conjecture,(
% 0.20/0.43    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ~spl2_1 | spl2_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f10,f18,f14])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (13934)------------------------------
% 0.20/0.43  % (13934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (13934)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (13934)Memory used [KB]: 6012
% 0.20/0.43  % (13934)Time elapsed: 0.004 s
% 0.20/0.43  % (13934)------------------------------
% 0.20/0.43  % (13934)------------------------------
% 0.20/0.44  % (13922)Success in time 0.074 s
%------------------------------------------------------------------------------
