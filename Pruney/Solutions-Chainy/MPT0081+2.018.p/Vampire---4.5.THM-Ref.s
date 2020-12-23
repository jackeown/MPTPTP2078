%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  44 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   73 ( 101 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26,f30,f38,f81,f88])).

fof(f88,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f20,f86])).

fof(f86,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f80,f29])).

fof(f29,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_3
  <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f80,plain,
    ( ! [X0] : ~ r1_xboole_0(sK0,k2_xboole_0(X0,k3_xboole_0(sK1,sK2)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_10
  <=> ! [X0] : ~ r1_xboole_0(sK0,k2_xboole_0(X0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f20,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f81,plain,
    ( spl3_10
    | spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f49,f36,f23,f79])).

fof(f23,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f36,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f49,plain,
    ( ! [X0] : ~ r1_xboole_0(sK0,k2_xboole_0(X0,k3_xboole_0(sK1,sK2)))
    | spl3_2
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f25,f37])).

fof(f37,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X2) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f36])).

fof(f25,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f38,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f30,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f12,f28])).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f26,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f10,f23])).

fof(f10,plain,(
    ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( r1_xboole_0(sK0,sK1)
    & ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) )
   => ( r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f21,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f11,f18])).

fof(f11,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:34:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (13984)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.45  % (13979)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (13979)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f21,f26,f30,f38,f81,f88])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    ~spl3_1 | ~spl3_3 | ~spl3_10),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f87])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    $false | (~spl3_1 | ~spl3_3 | ~spl3_10)),
% 0.21/0.45    inference(subsumption_resolution,[],[f20,f86])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    ~r1_xboole_0(sK0,sK1) | (~spl3_3 | ~spl3_10)),
% 0.21/0.45    inference(superposition,[],[f80,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    spl3_3 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_xboole_0(sK0,k2_xboole_0(X0,k3_xboole_0(sK1,sK2)))) ) | ~spl3_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f79])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    spl3_10 <=> ! [X0] : ~r1_xboole_0(sK0,k2_xboole_0(X0,k3_xboole_0(sK1,sK2)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    spl3_10 | spl3_2 | ~spl3_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f49,f36,f23,f79])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    spl3_2 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    spl3_5 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_xboole_0(sK0,k2_xboole_0(X0,k3_xboole_0(sK1,sK2)))) ) | (spl3_2 | ~spl3_5)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f25,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) ) | ~spl3_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f36])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f23])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    spl3_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f16,f36])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f12,f28])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ~spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f10,f23])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2))) => (r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f6,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.45    inference(negated_conjecture,[],[f4])).
% 0.21/0.45  fof(f4,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f11,f18])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (13979)------------------------------
% 0.21/0.45  % (13979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (13979)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (13979)Memory used [KB]: 6140
% 0.21/0.45  % (13979)Time elapsed: 0.042 s
% 0.21/0.45  % (13979)------------------------------
% 0.21/0.45  % (13979)------------------------------
% 0.21/0.46  % (13970)Success in time 0.104 s
%------------------------------------------------------------------------------
