%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
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
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f36,f48,f52,f65,f69,f80,f84,f91,f101,f113,f120,f137])).

fof(f137,plain,
    ( ~ spl3_1
    | spl3_3
    | spl3_14
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | spl3_14
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f130,f27])).

fof(f27,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl3_1
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f130,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | ~ spl3_1
    | spl3_3
    | spl3_14
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f90,f126])).

fof(f126,plain,
    ( sK0 = sK2
    | ~ spl3_1
    | spl3_3
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f125,f35])).

fof(f35,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_3
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f125,plain,
    ( r2_xboole_0(sK0,sK2)
    | sK0 = sK2
    | ~ spl3_1
    | ~ spl3_19 ),
    inference(resolution,[],[f119,f27])).

fof(f119,plain,
    ( ! [X2] :
        ( ~ r2_xboole_0(X2,sK1)
        | r2_xboole_0(X2,sK2)
        | sK2 = X2 )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl3_19
  <=> ! [X2] :
        ( sK2 = X2
        | r2_xboole_0(X2,sK2)
        | ~ r2_xboole_0(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f90,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_14
  <=> r2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f120,plain,
    ( spl3_19
    | ~ spl3_7
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f115,f111,f50,f118])).

fof(f50,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f111,plain,
    ( spl3_18
  <=> ! [X10] :
        ( ~ r1_tarski(X10,sK1)
        | sK2 = X10
        | r2_xboole_0(X10,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f115,plain,
    ( ! [X2] :
        ( sK2 = X2
        | r2_xboole_0(X2,sK2)
        | ~ r2_xboole_0(X2,sK1) )
    | ~ spl3_7
    | ~ spl3_18 ),
    inference(resolution,[],[f112,f51])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ r2_xboole_0(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f112,plain,
    ( ! [X10] :
        ( ~ r1_tarski(X10,sK1)
        | sK2 = X10
        | r2_xboole_0(X10,sK2) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f111])).

fof(f113,plain,
    ( spl3_18
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f109,f99,f30,f111])).

fof(f30,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f99,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X2,X0)
        | X1 = X2
        | r2_xboole_0(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f109,plain,
    ( ! [X10] :
        ( ~ r1_tarski(X10,sK1)
        | sK2 = X10
        | r2_xboole_0(X10,sK2) )
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(resolution,[],[f100,f31])).

fof(f31,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X2,X0)
        | X1 = X2
        | r2_xboole_0(X2,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,
    ( spl3_16
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f86,f67,f63,f99])).

fof(f63,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f67,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f86,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X2,X0)
        | X1 = X2
        | r2_xboole_0(X2,X1) )
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(resolution,[],[f68,f64])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f63])).

fof(f68,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f67])).

fof(f91,plain,
    ( ~ spl3_14
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f87,f75,f46,f89])).

fof(f46,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( ~ r2_xboole_0(X0,X1)
        | ~ r2_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f75,plain,
    ( spl3_12
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f87,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(resolution,[],[f76,f47])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( ~ r2_xboole_0(X0,X1)
        | ~ r2_xboole_0(X1,X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f46])).

fof(f76,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f75])).

fof(f84,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f81,f27])).

fof(f81,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | spl3_3
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f35,f79])).

fof(f79,plain,
    ( sK1 = sK2
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_13
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f80,plain,
    ( spl3_12
    | spl3_13
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f71,f63,f30,f78,f75])).

fof(f71,plain,
    ( sK1 = sK2
    | r2_xboole_0(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(resolution,[],[f64,f31])).

fof(f69,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f23,f67])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f65,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f22,f63])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f52,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f48,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f18,f46])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f36,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f32,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f15,f30])).

fof(f15,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

% (6977)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f28,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:17:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (6981)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (6973)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (6981)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (6973)Refutation not found, incomplete strategy% (6973)------------------------------
% 0.22/0.50  % (6973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f28,f32,f36,f48,f52,f65,f69,f80,f84,f91,f101,f113,f120,f137])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ~spl3_1 | spl3_3 | spl3_14 | ~spl3_19),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f136])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    $false | (~spl3_1 | spl3_3 | spl3_14 | ~spl3_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f130,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    r2_xboole_0(sK0,sK1) | ~spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    spl3_1 <=> r2_xboole_0(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ~r2_xboole_0(sK0,sK1) | (~spl3_1 | spl3_3 | spl3_14 | ~spl3_19)),
% 0.22/0.50    inference(backward_demodulation,[],[f90,f126])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    sK0 = sK2 | (~spl3_1 | spl3_3 | ~spl3_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f125,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ~r2_xboole_0(sK0,sK2) | spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    spl3_3 <=> r2_xboole_0(sK0,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    r2_xboole_0(sK0,sK2) | sK0 = sK2 | (~spl3_1 | ~spl3_19)),
% 0.22/0.50    inference(resolution,[],[f119,f27])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ( ! [X2] : (~r2_xboole_0(X2,sK1) | r2_xboole_0(X2,sK2) | sK2 = X2) ) | ~spl3_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f118])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    spl3_19 <=> ! [X2] : (sK2 = X2 | r2_xboole_0(X2,sK2) | ~r2_xboole_0(X2,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ~r2_xboole_0(sK2,sK1) | spl3_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f89])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl3_14 <=> r2_xboole_0(sK2,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    spl3_19 | ~spl3_7 | ~spl3_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f115,f111,f50,f118])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    spl3_7 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    spl3_18 <=> ! [X10] : (~r1_tarski(X10,sK1) | sK2 = X10 | r2_xboole_0(X10,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    ( ! [X2] : (sK2 = X2 | r2_xboole_0(X2,sK2) | ~r2_xboole_0(X2,sK1)) ) | (~spl3_7 | ~spl3_18)),
% 0.22/0.50    inference(resolution,[],[f112,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) ) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f50])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ( ! [X10] : (~r1_tarski(X10,sK1) | sK2 = X10 | r2_xboole_0(X10,sK2)) ) | ~spl3_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f111])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl3_18 | ~spl3_2 | ~spl3_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f109,f99,f30,f111])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl3_16 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X0) | X1 = X2 | r2_xboole_0(X2,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    ( ! [X10] : (~r1_tarski(X10,sK1) | sK2 = X10 | r2_xboole_0(X10,sK2)) ) | (~spl3_2 | ~spl3_16)),
% 0.22/0.50    inference(resolution,[],[f100,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f30])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X0) | X1 = X2 | r2_xboole_0(X2,X1)) ) | ~spl3_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f99])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl3_16 | ~spl3_10 | ~spl3_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f86,f67,f63,f99])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl3_10 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl3_11 <=> ! [X1,X0,X2] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X0) | X1 = X2 | r2_xboole_0(X2,X1)) ) | (~spl3_10 | ~spl3_11)),
% 0.22/0.50    inference(resolution,[],[f68,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) ) | ~spl3_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f63])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f67])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ~spl3_14 | ~spl3_6 | ~spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f87,f75,f46,f89])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    spl3_6 <=> ! [X1,X0] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl3_12 <=> r2_xboole_0(sK1,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ~r2_xboole_0(sK2,sK1) | (~spl3_6 | ~spl3_12)),
% 0.22/0.50    inference(resolution,[],[f76,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) ) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f46])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    r2_xboole_0(sK1,sK2) | ~spl3_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f75])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ~spl3_1 | spl3_3 | ~spl3_13),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f83])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    $false | (~spl3_1 | spl3_3 | ~spl3_13)),
% 0.22/0.50    inference(subsumption_resolution,[],[f81,f27])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ~r2_xboole_0(sK0,sK1) | (spl3_3 | ~spl3_13)),
% 0.22/0.50    inference(backward_demodulation,[],[f35,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    sK1 = sK2 | ~spl3_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl3_13 <=> sK1 = sK2),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl3_12 | spl3_13 | ~spl3_2 | ~spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f71,f63,f30,f78,f75])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    sK1 = sK2 | r2_xboole_0(sK1,sK2) | (~spl3_2 | ~spl3_10)),
% 0.22/0.50    inference(resolution,[],[f64,f31])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl3_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f23,f67])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f22,f63])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f20,f50])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f18,f46])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f16,f34])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ~r2_xboole_0(sK0,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r1_tarski(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.50    inference(negated_conjecture,[],[f6])).
% 0.22/0.50  fof(f6,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f15,f30])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    r1_tarski(sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  % (6977)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f14,f26])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    r2_xboole_0(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (6981)------------------------------
% 0.22/0.50  % (6981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (6981)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (6981)Memory used [KB]: 10618
% 0.22/0.50  % (6981)Time elapsed: 0.064 s
% 0.22/0.50  % (6981)------------------------------
% 0.22/0.50  % (6981)------------------------------
% 0.22/0.50  % (6971)Success in time 0.139 s
%------------------------------------------------------------------------------
