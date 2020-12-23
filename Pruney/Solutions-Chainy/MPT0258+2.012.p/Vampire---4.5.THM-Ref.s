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
% DateTime   : Thu Dec  3 12:40:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  66 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 184 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f33,f37,f41,f59,f94,f104])).

fof(f104,plain,
    ( spl3_1
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl3_1
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f102,f22])).

fof(f22,plain,
    ( k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl3_1
  <=> k2_tarski(sK0,sK2) = k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f102,plain,
    ( k2_tarski(sK0,sK2) = k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(resolution,[],[f93,f36])).

fof(f36,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f93,plain,
    ( r1_tarski(k2_tarski(sK0,sK2),sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_14
  <=> r1_tarski(k2_tarski(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f94,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f88,f57,f25,f91])).

fof(f25,plain,
    ( spl3_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f57,plain,
    ( spl3_9
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r1_tarski(k2_tarski(sK0,X1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f88,plain,
    ( r1_tarski(k2_tarski(sK0,sK2),sK1)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f58,f27])).

fof(f27,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f58,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r1_tarski(k2_tarski(sK0,X1),sK1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f51,f39,f30,f57])).

fof(f30,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f39,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f51,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | r1_tarski(k2_tarski(sK0,X1),sK1) )
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f40,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X2)
        | ~ r2_hidden(X1,X2)
        | r1_tarski(k2_tarski(X0,X1),X2) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f41,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f37,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f33,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f12,f30])).

fof(f12,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f28,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f14,f20])).

fof(f14,plain,(
    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:05:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.40  % (19322)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.41  % (19318)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (19319)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.41  % (19318)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f105,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f23,f28,f33,f37,f41,f59,f94,f104])).
% 0.21/0.41  fof(f104,plain,(
% 0.21/0.41    spl3_1 | ~spl3_4 | ~spl3_14),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f103])).
% 0.21/0.41  fof(f103,plain,(
% 0.21/0.41    $false | (spl3_1 | ~spl3_4 | ~spl3_14)),
% 0.21/0.41    inference(subsumption_resolution,[],[f102,f22])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) | spl3_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f20])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    spl3_1 <=> k2_tarski(sK0,sK2) = k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.41  fof(f102,plain,(
% 0.21/0.41    k2_tarski(sK0,sK2) = k3_xboole_0(k2_tarski(sK0,sK2),sK1) | (~spl3_4 | ~spl3_14)),
% 0.21/0.41    inference(resolution,[],[f93,f36])).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl3_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f35])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    spl3_4 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    r1_tarski(k2_tarski(sK0,sK2),sK1) | ~spl3_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f91])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    spl3_14 <=> r1_tarski(k2_tarski(sK0,sK2),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    spl3_14 | ~spl3_2 | ~spl3_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f88,f57,f25,f91])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    spl3_2 <=> r2_hidden(sK2,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    spl3_9 <=> ! [X1] : (~r2_hidden(X1,sK1) | r1_tarski(k2_tarski(sK0,X1),sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    r1_tarski(k2_tarski(sK0,sK2),sK1) | (~spl3_2 | ~spl3_9)),
% 0.21/0.42    inference(resolution,[],[f58,f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    r2_hidden(sK2,sK1) | ~spl3_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f25])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X1] : (~r2_hidden(X1,sK1) | r1_tarski(k2_tarski(sK0,X1),sK1)) ) | ~spl3_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f57])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    spl3_9 | ~spl3_3 | ~spl3_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f51,f39,f30,f57])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    spl3_3 <=> r2_hidden(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    spl3_5 <=> ! [X1,X0,X2] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    ( ! [X1] : (~r2_hidden(X1,sK1) | r1_tarski(k2_tarski(sK0,X1),sK1)) ) | (~spl3_3 | ~spl3_5)),
% 0.21/0.42    inference(resolution,[],[f40,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    r2_hidden(sK0,sK1) | ~spl3_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f30])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) ) | ~spl3_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f39])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    spl3_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f39])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.42    inference(flattening,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.42    inference(nnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl3_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f35])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl3_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f12,f30])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    r2_hidden(sK0,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f5])).
% 0.21/0.42  fof(f5,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 0.21/0.42    inference(negated_conjecture,[],[f3])).
% 0.21/0.42  fof(f3,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    spl3_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f13,f25])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    r2_hidden(sK2,sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ~spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f14,f20])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (19318)------------------------------
% 0.21/0.42  % (19318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (19318)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (19318)Memory used [KB]: 10618
% 0.21/0.42  % (19318)Time elapsed: 0.006 s
% 0.21/0.42  % (19318)------------------------------
% 0.21/0.42  % (19318)------------------------------
% 0.21/0.42  % (19310)Success in time 0.063 s
%------------------------------------------------------------------------------
