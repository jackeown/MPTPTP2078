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
% DateTime   : Thu Dec  3 12:30:22 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 (  95 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  140 ( 254 expanded)
%              Number of equality atoms :   32 (  51 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f269,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f40,f46,f51,f61,f121,f133,f266,f268])).

fof(f268,plain,
    ( sK1 != k2_xboole_0(sK0,sK1)
    | sK0 != k2_xboole_0(sK0,sK1)
    | sK0 = sK1 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f266,plain,
    ( spl3_14
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f259,f126,f261])).

fof(f261,plain,
    ( spl3_14
  <=> sK0 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f126,plain,
    ( spl3_11
  <=> sK0 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f259,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f22,f127])).

fof(f127,plain,
    ( sK0 = k2_xboole_0(sK1,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f133,plain,
    ( spl3_11
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f129,f118,f49,f126])).

fof(f49,plain,
    ( spl3_5
  <=> sK2 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f118,plain,
    ( spl3_9
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f129,plain,
    ( sK0 = k2_xboole_0(sK1,sK0)
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(superposition,[],[f50,f119])).

fof(f119,plain,
    ( sK0 = sK2
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f50,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f121,plain,
    ( spl3_9
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f114,f38,f34,f30,f118])).

fof(f30,plain,
    ( spl3_1
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f34,plain,
    ( spl3_2
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f38,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f114,plain,
    ( r2_xboole_0(sK0,sK2)
    | sK0 = sK2
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f112,f39])).

fof(f39,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r2_xboole_0(X0,sK2)
        | sK2 = X0 )
    | ~ spl3_2 ),
    inference(resolution,[],[f80,f35])).

fof(f35,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f80,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_xboole_0(X6,X7)
      | X5 = X7
      | r2_xboole_0(X5,X7)
      | ~ r1_tarski(X5,X6) ) ),
    inference(resolution,[],[f63,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X0)
      | X1 = X2
      | r2_xboole_0(X2,X1) ) ),
    inference(resolution,[],[f27,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f61,plain,
    ( sK0 != sK1
    | r2_xboole_0(sK0,sK2)
    | ~ r2_xboole_0(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f51,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f47,f34,f49])).

fof(f47,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f42,f35])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(resolution,[],[f23,f24])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f46,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f41,f38,f44])).

fof(f44,plain,
    ( spl3_4
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f41,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f23,f39])).

fof(f40,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r2_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r2_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

fof(f36,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f30])).

fof(f20,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (6387)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.47  % (6397)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.47  % (6387)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % (6395)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.48  % (6390)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f269,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f32,f36,f40,f46,f51,f61,f121,f133,f266,f268])).
% 0.19/0.48  fof(f268,plain,(
% 0.19/0.48    sK1 != k2_xboole_0(sK0,sK1) | sK0 != k2_xboole_0(sK0,sK1) | sK0 = sK1),
% 0.19/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.48  fof(f266,plain,(
% 0.19/0.48    spl3_14 | ~spl3_11),
% 0.19/0.48    inference(avatar_split_clause,[],[f259,f126,f261])).
% 0.19/0.48  fof(f261,plain,(
% 0.19/0.48    spl3_14 <=> sK0 = k2_xboole_0(sK0,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.19/0.48  fof(f126,plain,(
% 0.19/0.48    spl3_11 <=> sK0 = k2_xboole_0(sK1,sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.48  fof(f259,plain,(
% 0.19/0.48    sK0 = k2_xboole_0(sK0,sK1) | ~spl3_11),
% 0.19/0.48    inference(superposition,[],[f22,f127])).
% 0.19/0.48  fof(f127,plain,(
% 0.19/0.48    sK0 = k2_xboole_0(sK1,sK0) | ~spl3_11),
% 0.19/0.48    inference(avatar_component_clause,[],[f126])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.48  fof(f133,plain,(
% 0.19/0.48    spl3_11 | ~spl3_5 | ~spl3_9),
% 0.19/0.48    inference(avatar_split_clause,[],[f129,f118,f49,f126])).
% 0.19/0.48  fof(f49,plain,(
% 0.19/0.48    spl3_5 <=> sK2 = k2_xboole_0(sK1,sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.48  fof(f118,plain,(
% 0.19/0.48    spl3_9 <=> sK0 = sK2),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.48  fof(f129,plain,(
% 0.19/0.48    sK0 = k2_xboole_0(sK1,sK0) | (~spl3_5 | ~spl3_9)),
% 0.19/0.48    inference(superposition,[],[f50,f119])).
% 0.19/0.48  fof(f119,plain,(
% 0.19/0.48    sK0 = sK2 | ~spl3_9),
% 0.19/0.48    inference(avatar_component_clause,[],[f118])).
% 0.19/0.48  fof(f50,plain,(
% 0.19/0.48    sK2 = k2_xboole_0(sK1,sK2) | ~spl3_5),
% 0.19/0.48    inference(avatar_component_clause,[],[f49])).
% 0.19/0.48  fof(f121,plain,(
% 0.19/0.48    spl3_9 | spl3_1 | ~spl3_2 | ~spl3_3),
% 0.19/0.48    inference(avatar_split_clause,[],[f114,f38,f34,f30,f118])).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    spl3_1 <=> r2_xboole_0(sK0,sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    spl3_2 <=> r2_xboole_0(sK1,sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.48  fof(f114,plain,(
% 0.19/0.48    r2_xboole_0(sK0,sK2) | sK0 = sK2 | (~spl3_2 | ~spl3_3)),
% 0.19/0.48    inference(resolution,[],[f112,f39])).
% 0.19/0.48  fof(f39,plain,(
% 0.19/0.48    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.19/0.48    inference(avatar_component_clause,[],[f38])).
% 0.19/0.48  fof(f112,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(X0,sK1) | r2_xboole_0(X0,sK2) | sK2 = X0) ) | ~spl3_2),
% 0.19/0.48    inference(resolution,[],[f80,f35])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    r2_xboole_0(sK1,sK2) | ~spl3_2),
% 0.19/0.48    inference(avatar_component_clause,[],[f34])).
% 0.19/0.48  fof(f80,plain,(
% 0.19/0.48    ( ! [X6,X7,X5] : (~r2_xboole_0(X6,X7) | X5 = X7 | r2_xboole_0(X5,X7) | ~r1_tarski(X5,X6)) )),
% 0.19/0.48    inference(resolution,[],[f63,f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.19/0.48    inference(flattening,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.19/0.48    inference(nnf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.19/0.48  fof(f63,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X0) | X1 = X2 | r2_xboole_0(X2,X1)) )),
% 0.19/0.48    inference(resolution,[],[f27,f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.48    inference(flattening,[],[f12])).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.48  fof(f61,plain,(
% 0.19/0.48    sK0 != sK1 | r2_xboole_0(sK0,sK2) | ~r2_xboole_0(sK1,sK2)),
% 0.19/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.48  fof(f51,plain,(
% 0.19/0.48    spl3_5 | ~spl3_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f47,f34,f49])).
% 0.19/0.48  fof(f47,plain,(
% 0.19/0.48    sK2 = k2_xboole_0(sK1,sK2) | ~spl3_2),
% 0.19/0.48    inference(resolution,[],[f42,f35])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.19/0.48    inference(resolution,[],[f23,f24])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f11])).
% 0.19/0.48  fof(f11,plain,(
% 0.19/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.48  fof(f46,plain,(
% 0.19/0.48    spl3_4 | ~spl3_3),
% 0.19/0.48    inference(avatar_split_clause,[],[f41,f38,f44])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    spl3_4 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_3),
% 0.19/0.48    inference(resolution,[],[f23,f39])).
% 0.19/0.48  fof(f40,plain,(
% 0.19/0.48    spl3_3),
% 0.19/0.48    inference(avatar_split_clause,[],[f18,f38])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    r1_tarski(sK0,sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f10,plain,(
% 0.19/0.48    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.19/0.48    inference(flattening,[],[f9])).
% 0.19/0.48  fof(f9,plain,(
% 0.19/0.48    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r2_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,negated_conjecture,(
% 0.19/0.48    ~! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.19/0.48    inference(negated_conjecture,[],[f6])).
% 0.19/0.48  fof(f6,conjecture,(
% 0.19/0.48    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    spl3_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f19,f34])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    r2_xboole_0(sK1,sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f15])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ~spl3_1),
% 0.19/0.48    inference(avatar_split_clause,[],[f20,f30])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ~r2_xboole_0(sK0,sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f15])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (6387)------------------------------
% 0.19/0.48  % (6387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (6387)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (6387)Memory used [KB]: 10746
% 0.19/0.48  % (6387)Time elapsed: 0.063 s
% 0.19/0.48  % (6387)------------------------------
% 0.19/0.48  % (6387)------------------------------
% 0.19/0.48  % (6396)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.48  % (6380)Success in time 0.129 s
%------------------------------------------------------------------------------
