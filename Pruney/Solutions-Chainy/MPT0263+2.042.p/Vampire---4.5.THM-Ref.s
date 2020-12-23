%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  58 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   88 ( 125 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f25,f29,f33,f37,f45,f51,f54])).

fof(f54,plain,
    ( ~ spl2_5
    | spl2_6
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | ~ spl2_5
    | spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f52,f43])).

fof(f43,plain,
    ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_6
  <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f52,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(resolution,[],[f36,f50])).

fof(f50,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_7
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f36,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f51,plain,
    ( spl2_7
    | spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f46,f31,f22,f48])).

fof(f22,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f31,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f46,plain,
    ( r2_hidden(sK0,sK1)
    | spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f32,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f45,plain,
    ( ~ spl2_6
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f39,f27,f17,f41])).

fof(f17,plain,
    ( spl2_1
  <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f27,plain,
    ( spl2_3
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f39,plain,
    ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
    | spl2_1
    | ~ spl2_3 ),
    inference(superposition,[],[f19,f28])).

fof(f28,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f19,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f37,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f33,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f14,f31])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(f29,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f25,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f11,f22])).

fof(f11,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f20,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f12,f17])).

fof(f12,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:59:27 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.41  % (15161)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (15161)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f20,f25,f29,f33,f37,f45,f51,f54])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ~spl2_5 | spl2_6 | ~spl2_7),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f53])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    $false | (~spl2_5 | spl2_6 | ~spl2_7)),
% 0.21/0.42    inference(subsumption_resolution,[],[f52,f43])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) | spl2_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f41])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    spl2_6 <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | (~spl2_5 | ~spl2_7)),
% 0.21/0.42    inference(resolution,[],[f36,f50])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    r2_hidden(sK0,sK1) | ~spl2_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f48])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl2_7 <=> r2_hidden(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))) ) | ~spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl2_5 <=> ! [X1,X0] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl2_7 | spl2_2 | ~spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f46,f31,f22,f48])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    spl2_2 <=> r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    spl2_4 <=> ! [X1,X0] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    r2_hidden(sK0,sK1) | (spl2_2 | ~spl2_4)),
% 0.21/0.42    inference(resolution,[],[f32,f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ~r1_xboole_0(k1_tarski(sK0),sK1) | spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f22])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) ) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f31])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    ~spl2_6 | spl2_1 | ~spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f39,f27,f17,f41])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    spl2_1 <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    spl2_3 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) | (spl2_1 | ~spl2_3)),
% 0.21/0.42    inference(superposition,[],[f19,f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f27])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) | spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f17])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f35])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f14,f31])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f13,f27])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ~spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f11,f22])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.42    inference(negated_conjecture,[],[f4])).
% 0.21/0.42  fof(f4,conjecture,(
% 0.21/0.42    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f12,f17])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (15161)------------------------------
% 0.21/0.42  % (15161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (15161)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (15161)Memory used [KB]: 10490
% 0.21/0.42  % (15161)Time elapsed: 0.005 s
% 0.21/0.42  % (15161)------------------------------
% 0.21/0.42  % (15161)------------------------------
% 0.21/0.42  % (15152)Success in time 0.063 s
%------------------------------------------------------------------------------
