%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 111 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :  198 ( 321 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f30,f34,f42,f46,f55,f59,f69,f73,f79,f83,f90,f96,f115])).

fof(f115,plain,
    ( ~ spl3_1
    | spl3_3
    | spl3_13
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | spl3_13
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f108,f25])).

fof(f25,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_1
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f108,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | ~ spl3_1
    | spl3_3
    | spl3_13
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f82,f104])).

fof(f104,plain,
    ( sK0 = sK2
    | ~ spl3_1
    | spl3_3
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f103,f33])).

fof(f33,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_3
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f103,plain,
    ( r2_xboole_0(sK0,sK2)
    | sK0 = sK2
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(resolution,[],[f95,f25])).

fof(f95,plain,
    ( ! [X2] :
        ( ~ r2_xboole_0(X2,sK1)
        | r2_xboole_0(X2,sK2)
        | sK2 = X2 )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_15
  <=> ! [X2] :
        ( sK2 = X2
        | r2_xboole_0(X2,sK2)
        | ~ r2_xboole_0(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f82,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_13
  <=> r2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f96,plain,
    ( spl3_15
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f92,f88,f44,f94])).

fof(f44,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f88,plain,
    ( spl3_14
  <=> ! [X7] :
        ( ~ r1_tarski(X7,sK1)
        | sK2 = X7
        | r2_xboole_0(X7,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f92,plain,
    ( ! [X2] :
        ( sK2 = X2
        | r2_xboole_0(X2,sK2)
        | ~ r2_xboole_0(X2,sK1) )
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(resolution,[],[f89,f45])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ r2_xboole_0(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f44])).

fof(f89,plain,
    ( ! [X7] :
        ( ~ r1_tarski(X7,sK1)
        | sK2 = X7
        | r2_xboole_0(X7,sK2) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f88])).

fof(f90,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f86,f77,f28,f88])).

fof(f28,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f77,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X2,X0)
        | X1 = X2
        | r2_xboole_0(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f86,plain,
    ( ! [X7] :
        ( ~ r1_tarski(X7,sK1)
        | sK2 = X7
        | r2_xboole_0(X7,sK2) )
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(resolution,[],[f78,f29])).

fof(f29,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X2,X0)
        | X1 = X2
        | r2_xboole_0(X2,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f77])).

fof(f83,plain,
    ( ~ spl3_13
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f75,f64,f40,f81])).

fof(f40,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( ~ r2_xboole_0(X0,X1)
        | ~ r2_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f64,plain,
    ( spl3_10
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

% (3446)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f75,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(resolution,[],[f65,f41])).

fof(f41,plain,
    ( ! [X0,X1] :
        ( ~ r2_xboole_0(X0,X1)
        | ~ r2_xboole_0(X1,X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f65,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f64])).

fof(f79,plain,
    ( spl3_12
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f62,f57,f53,f77])).

fof(f53,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f57,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f62,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X2,X0)
        | X1 = X2
        | r2_xboole_0(X2,X1) )
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(resolution,[],[f58,f54])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f53])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f57])).

fof(f73,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f70,f25])).

fof(f70,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | spl3_3
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f33,f68])).

fof(f68,plain,
    ( sK1 = sK2
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_11
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f69,plain,
    ( spl3_10
    | spl3_11
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f60,f53,f28,f67,f64])).

fof(f60,plain,
    ( sK1 = sK2
    | r2_xboole_0(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f54,f29])).

fof(f59,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f21,f57])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f55,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f20,f53])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f46,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f18,f44])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f42,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f34,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f30,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f28])).

fof(f14,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f26,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f13,f24])).

fof(f13,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n009.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 17:09:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (3448)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (3449)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (3447)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (3456)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (3447)Refutation not found, incomplete strategy% (3447)------------------------------
% 0.21/0.48  % (3447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3447)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3447)Memory used [KB]: 10618
% 0.21/0.48  % (3447)Time elapsed: 0.062 s
% 0.21/0.48  % (3447)------------------------------
% 0.21/0.48  % (3447)------------------------------
% 0.21/0.48  % (3456)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f26,f30,f34,f42,f46,f55,f59,f69,f73,f79,f83,f90,f96,f115])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ~spl3_1 | spl3_3 | spl3_13 | ~spl3_15),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    $false | (~spl3_1 | spl3_3 | spl3_13 | ~spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f108,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    r2_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    spl3_1 <=> r2_xboole_0(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ~r2_xboole_0(sK0,sK1) | (~spl3_1 | spl3_3 | spl3_13 | ~spl3_15)),
% 0.21/0.48    inference(backward_demodulation,[],[f82,f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    sK0 = sK2 | (~spl3_1 | spl3_3 | ~spl3_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f103,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ~r2_xboole_0(sK0,sK2) | spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    spl3_3 <=> r2_xboole_0(sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    r2_xboole_0(sK0,sK2) | sK0 = sK2 | (~spl3_1 | ~spl3_15)),
% 0.21/0.48    inference(resolution,[],[f95,f25])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X2] : (~r2_xboole_0(X2,sK1) | r2_xboole_0(X2,sK2) | sK2 = X2) ) | ~spl3_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl3_15 <=> ! [X2] : (sK2 = X2 | r2_xboole_0(X2,sK2) | ~r2_xboole_0(X2,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ~r2_xboole_0(sK2,sK1) | spl3_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl3_13 <=> r2_xboole_0(sK2,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl3_15 | ~spl3_6 | ~spl3_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f92,f88,f44,f94])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl3_6 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl3_14 <=> ! [X7] : (~r1_tarski(X7,sK1) | sK2 = X7 | r2_xboole_0(X7,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X2] : (sK2 = X2 | r2_xboole_0(X2,sK2) | ~r2_xboole_0(X2,sK1)) ) | (~spl3_6 | ~spl3_14)),
% 0.21/0.48    inference(resolution,[],[f89,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) ) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f44])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X7] : (~r1_tarski(X7,sK1) | sK2 = X7 | r2_xboole_0(X7,sK2)) ) | ~spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f88])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl3_14 | ~spl3_2 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f86,f77,f28,f88])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl3_12 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X0) | X1 = X2 | r2_xboole_0(X2,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X7] : (~r1_tarski(X7,sK1) | sK2 = X7 | r2_xboole_0(X7,sK2)) ) | (~spl3_2 | ~spl3_12)),
% 0.21/0.48    inference(resolution,[],[f78,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f28])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X0) | X1 = X2 | r2_xboole_0(X2,X1)) ) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f77])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ~spl3_13 | ~spl3_5 | ~spl3_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f75,f64,f40,f81])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl3_5 <=> ! [X1,X0] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl3_10 <=> r2_xboole_0(sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  % (3446)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ~r2_xboole_0(sK2,sK1) | (~spl3_5 | ~spl3_10)),
% 0.21/0.48    inference(resolution,[],[f65,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f40])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    r2_xboole_0(sK1,sK2) | ~spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl3_12 | ~spl3_8 | ~spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f62,f57,f53,f77])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl3_8 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl3_9 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X0) | X1 = X2 | r2_xboole_0(X2,X1)) ) | (~spl3_8 | ~spl3_9)),
% 0.21/0.48    inference(resolution,[],[f58,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) ) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f53])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ~spl3_1 | spl3_3 | ~spl3_11),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    $false | (~spl3_1 | spl3_3 | ~spl3_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f70,f25])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ~r2_xboole_0(sK0,sK1) | (spl3_3 | ~spl3_11)),
% 0.21/0.48    inference(backward_demodulation,[],[f33,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    sK1 = sK2 | ~spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl3_11 <=> sK1 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl3_10 | spl3_11 | ~spl3_2 | ~spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f60,f53,f28,f67,f64])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    sK1 = sK2 | r2_xboole_0(sK1,sK2) | (~spl3_2 | ~spl3_8)),
% 0.21/0.48    inference(resolution,[],[f54,f29])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f57])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f20,f53])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f44])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f40])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f15,f32])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ~r2_xboole_0(sK0,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r1_tarski(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f14,f28])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f13,f24])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    r2_xboole_0(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (3456)------------------------------
% 0.21/0.48  % (3456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3456)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (3456)Memory used [KB]: 10618
% 0.21/0.48  % (3456)Time elapsed: 0.064 s
% 0.21/0.48  % (3456)------------------------------
% 0.21/0.48  % (3456)------------------------------
% 0.21/0.48  % (3444)Success in time 0.124 s
%------------------------------------------------------------------------------
