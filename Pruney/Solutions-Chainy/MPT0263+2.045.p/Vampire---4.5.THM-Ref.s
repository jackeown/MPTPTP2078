%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  43 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 (  83 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f33,f41,f43])).

fof(f43,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f42,f30,f37])).

fof(f37,plain,
    ( spl2_4
  <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f30,plain,
    ( spl2_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f42,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f32,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(f32,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f41,plain,
    ( ~ spl2_4
    | spl2_1 ),
    inference(avatar_split_clause,[],[f35,f19,f37])).

fof(f19,plain,
    ( spl2_1
  <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f35,plain,
    ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
    | spl2_1 ),
    inference(superposition,[],[f21,f14])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f21,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f33,plain,
    ( spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f28,f24,f30])).

fof(f24,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f28,plain,
    ( r2_hidden(sK0,sK1)
    | spl2_2 ),
    inference(resolution,[],[f26,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(f26,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f27,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f12,f24])).

fof(f12,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f22,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f13,f19])).

fof(f13,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:23:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.41  % (12265)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.41  % (12265)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f22,f27,f33,f41,f43])).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    spl2_4 | ~spl2_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f42,f30,f37])).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    spl2_4 <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    spl2_3 <=> r2_hidden(sK0,sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.41  fof(f42,plain,(
% 0.21/0.41    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | ~spl2_3),
% 0.21/0.41    inference(resolution,[],[f32,f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    r2_hidden(sK0,sK1) | ~spl2_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f30])).
% 0.21/0.41  fof(f41,plain,(
% 0.21/0.41    ~spl2_4 | spl2_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f35,f19,f37])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    spl2_1 <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) | spl2_1),
% 0.21/0.41    inference(superposition,[],[f21,f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) | spl2_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f19])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    spl2_3 | spl2_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f28,f24,f30])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    spl2_2 <=> r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    r2_hidden(sK0,sK1) | spl2_2),
% 0.21/0.41    inference(resolution,[],[f26,f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    ~r1_xboole_0(k1_tarski(sK0),sK1) | spl2_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f24])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    ~spl2_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f12,f24])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.41    inference(negated_conjecture,[],[f5])).
% 0.21/0.41  fof(f5,conjecture,(
% 0.21/0.41    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ~spl2_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f13,f19])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (12265)------------------------------
% 0.21/0.41  % (12265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (12265)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (12265)Memory used [KB]: 10618
% 0.21/0.41  % (12265)Time elapsed: 0.004 s
% 0.21/0.41  % (12265)------------------------------
% 0.21/0.41  % (12265)------------------------------
% 0.21/0.42  % (12253)Success in time 0.058 s
%------------------------------------------------------------------------------
