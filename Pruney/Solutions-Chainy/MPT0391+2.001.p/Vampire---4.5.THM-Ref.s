%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:49 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   67 (  99 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :  169 ( 266 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f42,f46,f50,f58,f62,f84,f108,f113,f126,f138])).

fof(f138,plain,
    ( spl3_1
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl3_1
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f136,f27])).

fof(f27,plain,
    ( ~ r1_xboole_0(k1_setfam_1(sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_1
  <=> r1_xboole_0(k1_setfam_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f136,plain,
    ( r1_xboole_0(k1_setfam_1(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f128,f41])).

fof(f41,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_4
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f128,plain,
    ( ~ r1_xboole_0(k1_setfam_1(sK1),k1_xboole_0)
    | r1_xboole_0(k1_setfam_1(sK1),sK2)
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(superposition,[],[f124,f83])).

fof(f83,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_12
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_setfam_1(sK1),k3_xboole_0(sK0,X0))
        | r1_xboole_0(k1_setfam_1(sK1),X0) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_18
  <=> ! [X0] :
        ( ~ r1_xboole_0(k1_setfam_1(sK1),k3_xboole_0(sK0,X0))
        | r1_xboole_0(k1_setfam_1(sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f126,plain,
    ( spl3_18
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f116,f111,f44,f123])).

fof(f44,plain,
    ( spl3_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f111,plain,
    ( spl3_16
  <=> ! [X0] :
        ( r1_xboole_0(k1_setfam_1(sK1),X0)
        | ~ r1_xboole_0(k1_setfam_1(sK1),k3_xboole_0(X0,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f116,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(k1_setfam_1(sK1),k3_xboole_0(sK0,X1))
        | r1_xboole_0(k1_setfam_1(sK1),X1) )
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(superposition,[],[f112,f45])).

fof(f45,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_setfam_1(sK1),k3_xboole_0(X0,sK0))
        | r1_xboole_0(k1_setfam_1(sK1),X0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f111])).

fof(f113,plain,
    ( spl3_16
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f109,f106,f35,f111])).

fof(f35,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f106,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_setfam_1(X0),k3_xboole_0(X1,X2))
        | r1_xboole_0(k1_setfam_1(X0),X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f109,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_setfam_1(sK1),X0)
        | ~ r1_xboole_0(k1_setfam_1(sK1),k3_xboole_0(X0,sK0)) )
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(resolution,[],[f107,f37])).

fof(f37,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X0)
        | r1_xboole_0(k1_setfam_1(X0),X1)
        | ~ r1_xboole_0(k1_setfam_1(X0),k3_xboole_0(X1,X2)) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,
    ( spl3_15
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f104,f60,f48,f106])).

fof(f48,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_tarski(k1_setfam_1(X1),X0)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f60,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f104,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(k1_setfam_1(X0),k3_xboole_0(X1,X2))
        | r1_xboole_0(k1_setfam_1(X0),X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(resolution,[],[f61,f49])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_setfam_1(X1),X0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f61,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X2)
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | r1_xboole_0(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f60])).

fof(f84,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f77,f56,f30,f81])).

fof(f30,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f56,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f77,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f57,f32])).

fof(f32,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f62,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f23,f60])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f58,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f21,f56])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f50,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f46,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f42,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_xboole_0(k1_setfam_1(sK1),sK2)
    & r1_xboole_0(sK0,sK2)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
        & r1_xboole_0(X0,X2)
        & r2_hidden(X0,X1) )
   => ( ~ r1_xboole_0(k1_setfam_1(sK1),sK2)
      & r1_xboole_0(sK0,sK2)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
      & r1_xboole_0(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
      & r1_xboole_0(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r2_hidden(X0,X1) )
       => r1_xboole_0(k1_setfam_1(X1),X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_xboole_0(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f25])).

fof(f17,plain,(
    ~ r1_xboole_0(k1_setfam_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:29:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.41  % (30903)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.18/0.41  % (30909)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.18/0.41  % (30903)Refutation found. Thanks to Tanya!
% 0.18/0.41  % SZS status Theorem for theBenchmark
% 0.18/0.41  % SZS output start Proof for theBenchmark
% 0.18/0.41  fof(f139,plain,(
% 0.18/0.41    $false),
% 0.18/0.41    inference(avatar_sat_refutation,[],[f28,f33,f38,f42,f46,f50,f58,f62,f84,f108,f113,f126,f138])).
% 0.18/0.41  fof(f138,plain,(
% 0.18/0.41    spl3_1 | ~spl3_4 | ~spl3_12 | ~spl3_18),
% 0.18/0.41    inference(avatar_contradiction_clause,[],[f137])).
% 0.18/0.41  fof(f137,plain,(
% 0.18/0.41    $false | (spl3_1 | ~spl3_4 | ~spl3_12 | ~spl3_18)),
% 0.18/0.41    inference(subsumption_resolution,[],[f136,f27])).
% 0.18/0.41  fof(f27,plain,(
% 0.18/0.41    ~r1_xboole_0(k1_setfam_1(sK1),sK2) | spl3_1),
% 0.18/0.41    inference(avatar_component_clause,[],[f25])).
% 0.18/0.41  fof(f25,plain,(
% 0.18/0.41    spl3_1 <=> r1_xboole_0(k1_setfam_1(sK1),sK2)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.18/0.41  fof(f136,plain,(
% 0.18/0.41    r1_xboole_0(k1_setfam_1(sK1),sK2) | (~spl3_4 | ~spl3_12 | ~spl3_18)),
% 0.18/0.41    inference(subsumption_resolution,[],[f128,f41])).
% 0.18/0.41  fof(f41,plain,(
% 0.18/0.41    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_4),
% 0.18/0.41    inference(avatar_component_clause,[],[f40])).
% 0.18/0.41  fof(f40,plain,(
% 0.18/0.41    spl3_4 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.18/0.41  fof(f128,plain,(
% 0.18/0.41    ~r1_xboole_0(k1_setfam_1(sK1),k1_xboole_0) | r1_xboole_0(k1_setfam_1(sK1),sK2) | (~spl3_12 | ~spl3_18)),
% 0.18/0.41    inference(superposition,[],[f124,f83])).
% 0.18/0.41  fof(f83,plain,(
% 0.18/0.41    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_12),
% 0.18/0.41    inference(avatar_component_clause,[],[f81])).
% 0.18/0.41  fof(f81,plain,(
% 0.18/0.41    spl3_12 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.18/0.41  fof(f124,plain,(
% 0.18/0.41    ( ! [X0] : (~r1_xboole_0(k1_setfam_1(sK1),k3_xboole_0(sK0,X0)) | r1_xboole_0(k1_setfam_1(sK1),X0)) ) | ~spl3_18),
% 0.18/0.41    inference(avatar_component_clause,[],[f123])).
% 0.18/0.41  fof(f123,plain,(
% 0.18/0.41    spl3_18 <=> ! [X0] : (~r1_xboole_0(k1_setfam_1(sK1),k3_xboole_0(sK0,X0)) | r1_xboole_0(k1_setfam_1(sK1),X0))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.18/0.41  fof(f126,plain,(
% 0.18/0.41    spl3_18 | ~spl3_5 | ~spl3_16),
% 0.18/0.41    inference(avatar_split_clause,[],[f116,f111,f44,f123])).
% 0.18/0.41  fof(f44,plain,(
% 0.18/0.41    spl3_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.18/0.41  fof(f111,plain,(
% 0.18/0.41    spl3_16 <=> ! [X0] : (r1_xboole_0(k1_setfam_1(sK1),X0) | ~r1_xboole_0(k1_setfam_1(sK1),k3_xboole_0(X0,sK0)))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.18/0.41  fof(f116,plain,(
% 0.18/0.41    ( ! [X1] : (~r1_xboole_0(k1_setfam_1(sK1),k3_xboole_0(sK0,X1)) | r1_xboole_0(k1_setfam_1(sK1),X1)) ) | (~spl3_5 | ~spl3_16)),
% 0.18/0.41    inference(superposition,[],[f112,f45])).
% 0.18/0.41  fof(f45,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.18/0.41    inference(avatar_component_clause,[],[f44])).
% 0.18/0.41  fof(f112,plain,(
% 0.18/0.41    ( ! [X0] : (~r1_xboole_0(k1_setfam_1(sK1),k3_xboole_0(X0,sK0)) | r1_xboole_0(k1_setfam_1(sK1),X0)) ) | ~spl3_16),
% 0.18/0.41    inference(avatar_component_clause,[],[f111])).
% 0.18/0.41  fof(f113,plain,(
% 0.18/0.41    spl3_16 | ~spl3_3 | ~spl3_15),
% 0.18/0.41    inference(avatar_split_clause,[],[f109,f106,f35,f111])).
% 0.18/0.41  fof(f35,plain,(
% 0.18/0.41    spl3_3 <=> r2_hidden(sK0,sK1)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.18/0.41  fof(f106,plain,(
% 0.18/0.41    spl3_15 <=> ! [X1,X0,X2] : (~r1_xboole_0(k1_setfam_1(X0),k3_xboole_0(X1,X2)) | r1_xboole_0(k1_setfam_1(X0),X1) | ~r2_hidden(X2,X0))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.18/0.41  fof(f109,plain,(
% 0.18/0.41    ( ! [X0] : (r1_xboole_0(k1_setfam_1(sK1),X0) | ~r1_xboole_0(k1_setfam_1(sK1),k3_xboole_0(X0,sK0))) ) | (~spl3_3 | ~spl3_15)),
% 0.18/0.41    inference(resolution,[],[f107,f37])).
% 0.18/0.41  fof(f37,plain,(
% 0.18/0.41    r2_hidden(sK0,sK1) | ~spl3_3),
% 0.18/0.41    inference(avatar_component_clause,[],[f35])).
% 0.18/0.41  fof(f107,plain,(
% 0.18/0.41    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r1_xboole_0(k1_setfam_1(X0),X1) | ~r1_xboole_0(k1_setfam_1(X0),k3_xboole_0(X1,X2))) ) | ~spl3_15),
% 0.18/0.41    inference(avatar_component_clause,[],[f106])).
% 0.18/0.41  fof(f108,plain,(
% 0.18/0.41    spl3_15 | ~spl3_6 | ~spl3_9),
% 0.18/0.41    inference(avatar_split_clause,[],[f104,f60,f48,f106])).
% 0.18/0.41  fof(f48,plain,(
% 0.18/0.41    spl3_6 <=> ! [X1,X0] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.18/0.41  fof(f60,plain,(
% 0.18/0.41    spl3_9 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.18/0.41  fof(f104,plain,(
% 0.18/0.41    ( ! [X2,X0,X1] : (~r1_xboole_0(k1_setfam_1(X0),k3_xboole_0(X1,X2)) | r1_xboole_0(k1_setfam_1(X0),X1) | ~r2_hidden(X2,X0)) ) | (~spl3_6 | ~spl3_9)),
% 0.18/0.41    inference(resolution,[],[f61,f49])).
% 0.18/0.41  fof(f49,plain,(
% 0.18/0.41    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) ) | ~spl3_6),
% 0.18/0.41    inference(avatar_component_clause,[],[f48])).
% 0.18/0.41  fof(f61,plain,(
% 0.18/0.41    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) ) | ~spl3_9),
% 0.18/0.41    inference(avatar_component_clause,[],[f60])).
% 0.18/0.41  fof(f84,plain,(
% 0.18/0.41    spl3_12 | ~spl3_2 | ~spl3_8),
% 0.18/0.41    inference(avatar_split_clause,[],[f77,f56,f30,f81])).
% 0.18/0.41  fof(f30,plain,(
% 0.18/0.41    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.18/0.41  fof(f56,plain,(
% 0.18/0.41    spl3_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.18/0.41  fof(f77,plain,(
% 0.18/0.41    k1_xboole_0 = k3_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_8)),
% 0.18/0.41    inference(resolution,[],[f57,f32])).
% 0.18/0.41  fof(f32,plain,(
% 0.18/0.41    r1_xboole_0(sK0,sK2) | ~spl3_2),
% 0.18/0.41    inference(avatar_component_clause,[],[f30])).
% 0.18/0.41  fof(f57,plain,(
% 0.18/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_8),
% 0.18/0.41    inference(avatar_component_clause,[],[f56])).
% 0.18/0.41  fof(f62,plain,(
% 0.18/0.41    spl3_9),
% 0.18/0.41    inference(avatar_split_clause,[],[f23,f60])).
% 0.18/0.41  fof(f23,plain,(
% 0.18/0.41    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f11])).
% 0.18/0.41  fof(f11,plain,(
% 0.18/0.41    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 0.18/0.41    inference(ennf_transformation,[],[f4])).
% 0.18/0.41  fof(f4,axiom,(
% 0.18/0.41    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.18/0.41  fof(f58,plain,(
% 0.18/0.41    spl3_8),
% 0.18/0.41    inference(avatar_split_clause,[],[f21,f56])).
% 0.18/0.41  fof(f21,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f14])).
% 0.18/0.41  fof(f14,plain,(
% 0.18/0.41    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.18/0.41    inference(nnf_transformation,[],[f2])).
% 0.18/0.41  fof(f2,axiom,(
% 0.18/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.18/0.41  fof(f50,plain,(
% 0.18/0.41    spl3_6),
% 0.18/0.41    inference(avatar_split_clause,[],[f20,f48])).
% 0.18/0.41  fof(f20,plain,(
% 0.18/0.41    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f10])).
% 0.18/0.41  fof(f10,plain,(
% 0.18/0.41    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.18/0.41    inference(ennf_transformation,[],[f5])).
% 0.18/0.41  fof(f5,axiom,(
% 0.18/0.41    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.18/0.41  fof(f46,plain,(
% 0.18/0.41    spl3_5),
% 0.18/0.41    inference(avatar_split_clause,[],[f19,f44])).
% 0.18/0.41  fof(f19,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f1])).
% 0.18/0.41  fof(f1,axiom,(
% 0.18/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.18/0.41  fof(f42,plain,(
% 0.18/0.41    spl3_4),
% 0.18/0.41    inference(avatar_split_clause,[],[f18,f40])).
% 0.18/0.41  fof(f18,plain,(
% 0.18/0.41    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f3])).
% 0.18/0.41  fof(f3,axiom,(
% 0.18/0.41    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.18/0.41  fof(f38,plain,(
% 0.18/0.41    spl3_3),
% 0.18/0.41    inference(avatar_split_clause,[],[f15,f35])).
% 0.18/0.41  fof(f15,plain,(
% 0.18/0.41    r2_hidden(sK0,sK1)),
% 0.18/0.41    inference(cnf_transformation,[],[f13])).
% 0.18/0.41  fof(f13,plain,(
% 0.18/0.41    ~r1_xboole_0(k1_setfam_1(sK1),sK2) & r1_xboole_0(sK0,sK2) & r2_hidden(sK0,sK1)),
% 0.18/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).
% 0.18/0.41  fof(f12,plain,(
% 0.18/0.41    ? [X0,X1,X2] : (~r1_xboole_0(k1_setfam_1(X1),X2) & r1_xboole_0(X0,X2) & r2_hidden(X0,X1)) => (~r1_xboole_0(k1_setfam_1(sK1),sK2) & r1_xboole_0(sK0,sK2) & r2_hidden(sK0,sK1))),
% 0.18/0.41    introduced(choice_axiom,[])).
% 0.18/0.41  fof(f9,plain,(
% 0.18/0.41    ? [X0,X1,X2] : (~r1_xboole_0(k1_setfam_1(X1),X2) & r1_xboole_0(X0,X2) & r2_hidden(X0,X1))),
% 0.18/0.41    inference(flattening,[],[f8])).
% 0.18/0.41  fof(f8,plain,(
% 0.18/0.41    ? [X0,X1,X2] : (~r1_xboole_0(k1_setfam_1(X1),X2) & (r1_xboole_0(X0,X2) & r2_hidden(X0,X1)))),
% 0.18/0.41    inference(ennf_transformation,[],[f7])).
% 0.18/0.41  fof(f7,negated_conjecture,(
% 0.18/0.41    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r2_hidden(X0,X1)) => r1_xboole_0(k1_setfam_1(X1),X2))),
% 0.18/0.41    inference(negated_conjecture,[],[f6])).
% 0.18/0.41  fof(f6,conjecture,(
% 0.18/0.41    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r2_hidden(X0,X1)) => r1_xboole_0(k1_setfam_1(X1),X2))),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_setfam_1)).
% 0.18/0.41  fof(f33,plain,(
% 0.18/0.41    spl3_2),
% 0.18/0.41    inference(avatar_split_clause,[],[f16,f30])).
% 0.18/0.41  fof(f16,plain,(
% 0.18/0.41    r1_xboole_0(sK0,sK2)),
% 0.18/0.41    inference(cnf_transformation,[],[f13])).
% 0.18/0.41  fof(f28,plain,(
% 0.18/0.41    ~spl3_1),
% 0.18/0.41    inference(avatar_split_clause,[],[f17,f25])).
% 0.18/0.41  fof(f17,plain,(
% 0.18/0.41    ~r1_xboole_0(k1_setfam_1(sK1),sK2)),
% 0.18/0.41    inference(cnf_transformation,[],[f13])).
% 0.18/0.41  % SZS output end Proof for theBenchmark
% 0.18/0.41  % (30903)------------------------------
% 0.18/0.41  % (30903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.41  % (30903)Termination reason: Refutation
% 0.18/0.41  
% 0.18/0.41  % (30903)Memory used [KB]: 10618
% 0.18/0.41  % (30903)Time elapsed: 0.006 s
% 0.18/0.41  % (30903)------------------------------
% 0.18/0.41  % (30903)------------------------------
% 0.18/0.41  % (30897)Success in time 0.072 s
%------------------------------------------------------------------------------
