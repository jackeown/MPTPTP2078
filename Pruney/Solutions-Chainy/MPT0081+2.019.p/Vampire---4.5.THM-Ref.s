%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
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
fof(f82,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26,f30,f42,f48,f81])).

fof(f81,plain,
    ( ~ spl3_1
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f20,f79])).

fof(f79,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f47,f41])).

fof(f41,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_6
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f47,plain,
    ( ! [X0] : ~ r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_7
  <=> ! [X0] : ~ r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f20,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f48,plain,
    ( spl3_7
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f43,f28,f23,f46])).

fof(f23,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f28,plain,
    ( spl3_3
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f43,plain,
    ( ! [X0] : ~ r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X0))
    | spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f25,f29])).

fof(f29,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X1) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f28])).

fof(f25,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f42,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f13,f40])).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f30,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f28])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:40:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (30935)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.42  % (30935)Refutation not found, incomplete strategy% (30935)------------------------------
% 0.21/0.42  % (30935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (30935)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (30935)Memory used [KB]: 10490
% 0.21/0.42  % (30935)Time elapsed: 0.004 s
% 0.21/0.42  % (30935)------------------------------
% 0.21/0.42  % (30935)------------------------------
% 0.21/0.45  % (30929)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (30937)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (30938)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (30929)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f21,f26,f30,f42,f48,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ~spl3_1 | ~spl3_6 | ~spl3_7),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    $false | (~spl3_1 | ~spl3_6 | ~spl3_7)),
% 0.21/0.47    inference(subsumption_resolution,[],[f20,f79])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ~r1_xboole_0(sK0,sK1) | (~spl3_6 | ~spl3_7)),
% 0.21/0.47    inference(superposition,[],[f47,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    spl3_6 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X0))) ) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl3_7 <=> ! [X0] : ~r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl3_7 | spl3_2 | ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f43,f28,f23,f46])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    spl3_2 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    spl3_3 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_xboole_0(sK0,k2_xboole_0(k3_xboole_0(sK1,sK2),X0))) ) | (spl3_2 | ~spl3_3)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f25,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) ) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f28])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f23])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f13,f40])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f15,f28])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f10,f23])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2))) => (r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f11,f18])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    r1_xboole_0(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (30929)------------------------------
% 0.21/0.47  % (30929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (30929)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (30929)Memory used [KB]: 6140
% 0.21/0.47  % (30929)Time elapsed: 0.035 s
% 0.21/0.47  % (30929)------------------------------
% 0.21/0.47  % (30929)------------------------------
% 0.21/0.47  % (30923)Success in time 0.106 s
%------------------------------------------------------------------------------
