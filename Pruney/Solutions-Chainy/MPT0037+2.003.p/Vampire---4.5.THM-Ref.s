%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:46 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   36 (  51 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   73 ( 107 expanded)
%              Number of equality atoms :   25 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f22,f26,f30,f36,f46,f73])).

fof(f73,plain,
    ( spl3_1
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl3_1
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k2_xboole_0(sK0,k3_xboole_0(sK2,sK1))
    | spl3_1
    | ~ spl3_7 ),
    inference(superposition,[],[f16,f45])).

fof(f45,plain,
    ( ! [X0] : k2_xboole_0(sK0,k3_xboole_0(X0,sK1)) = k3_xboole_0(k2_xboole_0(sK0,X0),sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_7
  <=> ! [X0] : k2_xboole_0(sK0,k3_xboole_0(X0,sK1)) = k3_xboole_0(k2_xboole_0(sK0,X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f16,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f14])).

fof(f14,plain,
    ( spl3_1
  <=> k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) = k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f46,plain,
    ( spl3_7
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f38,f33,f28,f44])).

fof(f28,plain,
    ( spl3_4
  <=> ! [X1,X0,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f33,plain,
    ( spl3_5
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f38,plain,
    ( ! [X0] : k2_xboole_0(sK0,k3_xboole_0(X0,sK1)) = k3_xboole_0(k2_xboole_0(sK0,X0),sK1)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f29,f35])).

fof(f35,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f33])).

fof(f29,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f28])).

fof(f36,plain,
    ( spl3_5
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f31,f24,f19,f33])).

fof(f19,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f24,plain,
    ( spl3_3
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f31,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f25,f21])).

fof(f21,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f19])).

fof(f25,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f24])).

fof(f30,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f12,f28])).

fof(f12,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f26,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f11,f24])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f22,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f9,f19])).

fof(f9,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_xboole_1)).

fof(f17,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f10,f14])).

fof(f10,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : run_vampire %s %d
% 0.10/0.31  % Computer   : n024.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 14:25:06 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.17/0.37  % (5849)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.17/0.37  % (5849)Refutation found. Thanks to Tanya!
% 0.17/0.37  % SZS status Theorem for theBenchmark
% 0.17/0.37  % SZS output start Proof for theBenchmark
% 0.17/0.38  fof(f74,plain,(
% 0.17/0.38    $false),
% 0.17/0.38    inference(avatar_sat_refutation,[],[f17,f22,f26,f30,f36,f46,f73])).
% 0.17/0.38  fof(f73,plain,(
% 0.17/0.38    spl3_1 | ~spl3_7),
% 0.17/0.38    inference(avatar_contradiction_clause,[],[f72])).
% 0.17/0.38  fof(f72,plain,(
% 0.17/0.38    $false | (spl3_1 | ~spl3_7)),
% 0.17/0.38    inference(trivial_inequality_removal,[],[f71])).
% 0.17/0.38  fof(f71,plain,(
% 0.17/0.38    k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) | (spl3_1 | ~spl3_7)),
% 0.17/0.38    inference(superposition,[],[f16,f45])).
% 0.17/0.38  fof(f45,plain,(
% 0.17/0.38    ( ! [X0] : (k2_xboole_0(sK0,k3_xboole_0(X0,sK1)) = k3_xboole_0(k2_xboole_0(sK0,X0),sK1)) ) | ~spl3_7),
% 0.17/0.38    inference(avatar_component_clause,[],[f44])).
% 0.17/0.38  fof(f44,plain,(
% 0.17/0.38    spl3_7 <=> ! [X0] : k2_xboole_0(sK0,k3_xboole_0(X0,sK1)) = k3_xboole_0(k2_xboole_0(sK0,X0),sK1)),
% 0.17/0.38    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.17/0.38  fof(f16,plain,(
% 0.17/0.38    k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl3_1),
% 0.17/0.38    inference(avatar_component_clause,[],[f14])).
% 0.17/0.38  fof(f14,plain,(
% 0.17/0.38    spl3_1 <=> k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) = k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.17/0.38    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.17/0.38  fof(f46,plain,(
% 0.17/0.38    spl3_7 | ~spl3_4 | ~spl3_5),
% 0.17/0.38    inference(avatar_split_clause,[],[f38,f33,f28,f44])).
% 0.17/0.38  fof(f28,plain,(
% 0.17/0.38    spl3_4 <=> ! [X1,X0,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.17/0.38    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.17/0.38  fof(f33,plain,(
% 0.17/0.38    spl3_5 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.17/0.38    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.17/0.38  fof(f38,plain,(
% 0.17/0.38    ( ! [X0] : (k2_xboole_0(sK0,k3_xboole_0(X0,sK1)) = k3_xboole_0(k2_xboole_0(sK0,X0),sK1)) ) | (~spl3_4 | ~spl3_5)),
% 0.17/0.38    inference(superposition,[],[f29,f35])).
% 0.17/0.38  fof(f35,plain,(
% 0.17/0.38    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_5),
% 0.17/0.38    inference(avatar_component_clause,[],[f33])).
% 0.17/0.38  fof(f29,plain,(
% 0.17/0.38    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) ) | ~spl3_4),
% 0.17/0.38    inference(avatar_component_clause,[],[f28])).
% 0.17/0.38  fof(f36,plain,(
% 0.17/0.38    spl3_5 | ~spl3_2 | ~spl3_3),
% 0.17/0.38    inference(avatar_split_clause,[],[f31,f24,f19,f33])).
% 0.17/0.38  fof(f19,plain,(
% 0.17/0.38    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.17/0.38    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.17/0.38  fof(f24,plain,(
% 0.17/0.38    spl3_3 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.17/0.38    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.17/0.38  fof(f31,plain,(
% 0.17/0.38    sK1 = k2_xboole_0(sK0,sK1) | (~spl3_2 | ~spl3_3)),
% 0.17/0.38    inference(resolution,[],[f25,f21])).
% 0.17/0.38  fof(f21,plain,(
% 0.17/0.38    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.17/0.38    inference(avatar_component_clause,[],[f19])).
% 0.17/0.38  fof(f25,plain,(
% 0.17/0.38    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_3),
% 0.17/0.38    inference(avatar_component_clause,[],[f24])).
% 0.17/0.38  fof(f30,plain,(
% 0.17/0.38    spl3_4),
% 0.17/0.38    inference(avatar_split_clause,[],[f12,f28])).
% 0.17/0.38  fof(f12,plain,(
% 0.17/0.38    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 0.17/0.38    inference(cnf_transformation,[],[f2])).
% 0.17/0.38  fof(f2,axiom,(
% 0.17/0.38    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.17/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
% 0.17/0.38  fof(f26,plain,(
% 0.17/0.38    spl3_3),
% 0.17/0.38    inference(avatar_split_clause,[],[f11,f24])).
% 0.17/0.38  fof(f11,plain,(
% 0.17/0.38    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.17/0.38    inference(cnf_transformation,[],[f6])).
% 0.17/0.38  fof(f6,plain,(
% 0.17/0.38    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.17/0.38    inference(ennf_transformation,[],[f1])).
% 0.17/0.38  fof(f1,axiom,(
% 0.17/0.38    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.17/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.17/0.38  fof(f22,plain,(
% 0.17/0.38    spl3_2),
% 0.17/0.38    inference(avatar_split_clause,[],[f9,f19])).
% 0.17/0.38  fof(f9,plain,(
% 0.17/0.38    r1_tarski(sK0,sK1)),
% 0.17/0.38    inference(cnf_transformation,[],[f8])).
% 0.17/0.38  fof(f8,plain,(
% 0.17/0.38    k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 0.17/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).
% 0.17/0.38  fof(f7,plain,(
% 0.17/0.38    ? [X0,X1,X2] : (k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 0.17/0.38    introduced(choice_axiom,[])).
% 0.17/0.38  fof(f5,plain,(
% 0.17/0.38    ? [X0,X1,X2] : (k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 0.17/0.38    inference(ennf_transformation,[],[f4])).
% 0.17/0.38  fof(f4,negated_conjecture,(
% 0.17/0.38    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.17/0.38    inference(negated_conjecture,[],[f3])).
% 0.17/0.38  fof(f3,conjecture,(
% 0.17/0.38    ! [X0,X1,X2] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.17/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_xboole_1)).
% 0.17/0.38  fof(f17,plain,(
% 0.17/0.38    ~spl3_1),
% 0.17/0.38    inference(avatar_split_clause,[],[f10,f14])).
% 0.17/0.38  fof(f10,plain,(
% 0.17/0.38    k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.17/0.38    inference(cnf_transformation,[],[f8])).
% 0.17/0.38  % SZS output end Proof for theBenchmark
% 0.17/0.38  % (5849)------------------------------
% 0.17/0.38  % (5849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.38  % (5849)Termination reason: Refutation
% 0.17/0.38  
% 0.17/0.38  % (5849)Memory used [KB]: 10490
% 0.17/0.38  % (5849)Time elapsed: 0.005 s
% 0.17/0.38  % (5849)------------------------------
% 0.17/0.38  % (5849)------------------------------
% 0.17/0.38  % (5843)Success in time 0.057 s
%------------------------------------------------------------------------------
