%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 117 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :  201 ( 318 expanded)
%              Number of equality atoms :   33 (  57 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f548,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f47,f51,f55,f67,f71,f81,f89,f115,f130,f206,f486,f546])).

fof(f546,plain,
    ( spl3_1
    | ~ spl3_21
    | ~ spl3_86 ),
    inference(avatar_contradiction_clause,[],[f545])).

fof(f545,plain,
    ( $false
    | spl3_1
    | ~ spl3_21
    | ~ spl3_86 ),
    inference(subsumption_resolution,[],[f525,f32])).

fof(f32,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl3_1
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f525,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | ~ spl3_21
    | ~ spl3_86 ),
    inference(resolution,[],[f485,f129])).

fof(f129,plain,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_21
  <=> r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f485,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X1)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1) )
    | ~ spl3_86 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl3_86
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1)
        | ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).

fof(f486,plain,
    ( spl3_86
    | ~ spl3_3
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f481,f204,f40,f484])).

fof(f40,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f204,plain,
    ( spl3_35
  <=> ! [X1,X3,X2] :
        ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)),X3)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(X1,X2),X3)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f481,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1)
        | ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X1) )
    | ~ spl3_3
    | ~ spl3_35 ),
    inference(resolution,[],[f205,f42])).

fof(f42,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f205,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(X1,X2),X3)
        | ~ r1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)),X3) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f204])).

fof(f206,plain,
    ( spl3_35
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f198,f53,f45,f204])).

fof(f45,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f53,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k1_xboole_0
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f198,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)),X3)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(X1,X2),X3)
        | ~ v1_relat_1(X1) )
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(resolution,[],[f54,f46])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = k1_xboole_0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f130,plain,
    ( spl3_21
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f121,f113,f78,f127])).

fof(f78,plain,
    ( spl3_12
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f113,plain,
    ( spl3_18
  <=> ! [X1,X0] : r1_xboole_0(k1_relat_1(k7_relat_1(sK2,k4_xboole_0(X0,X1))),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f121,plain,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(superposition,[],[f114,f80])).

fof(f80,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f114,plain,
    ( ! [X0,X1] : r1_xboole_0(k1_relat_1(k7_relat_1(sK2,k4_xboole_0(X0,X1))),X1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f110,f87,f40,f113])).

fof(f87,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(k1_relat_1(k7_relat_1(X0,k4_xboole_0(X1,X2))),X2)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f110,plain,
    ( ! [X0,X1] : r1_xboole_0(k1_relat_1(k7_relat_1(sK2,k4_xboole_0(X0,X1))),X1)
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(resolution,[],[f88,f42])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | r1_xboole_0(k1_relat_1(k7_relat_1(X0,k4_xboole_0(X1,X2))),X2) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f84,f69,f49,f87])).

fof(f49,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f69,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f84,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(k1_relat_1(k7_relat_1(X0,k4_xboole_0(X1,X2))),X2)
        | ~ v1_relat_1(X0) )
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(resolution,[],[f70,f50])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        | r1_xboole_0(X0,X2) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f81,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f76,f65,f35,f78])).

fof(f35,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f65,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f76,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f66,f37])).

fof(f37,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f71,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f28,f69])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f67,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f25,f65])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f55,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k7_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k7_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f51,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f47,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f43,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    & r1_xboole_0(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
        & r1_xboole_0(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
      & r1_xboole_0(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f38,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f35])).

fof(f19,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f30])).

fof(f20,plain,(
    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:25:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (6482)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.41  % (6481)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (6481)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f548,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f33,f38,f43,f47,f51,f55,f67,f71,f81,f89,f115,f130,f206,f486,f546])).
% 0.20/0.42  fof(f546,plain,(
% 0.20/0.42    spl3_1 | ~spl3_21 | ~spl3_86),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f545])).
% 0.20/0.42  fof(f545,plain,(
% 0.20/0.42    $false | (spl3_1 | ~spl3_21 | ~spl3_86)),
% 0.20/0.42    inference(subsumption_resolution,[],[f525,f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) | spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f30])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    spl3_1 <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.42  fof(f525,plain,(
% 0.20/0.42    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1) | (~spl3_21 | ~spl3_86)),
% 0.20/0.42    inference(resolution,[],[f485,f129])).
% 0.20/0.42  fof(f129,plain,(
% 0.20/0.42    r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) | ~spl3_21),
% 0.20/0.42    inference(avatar_component_clause,[],[f127])).
% 0.20/0.42  fof(f127,plain,(
% 0.20/0.42    spl3_21 <=> r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.42  fof(f485,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1)) ) | ~spl3_86),
% 0.20/0.42    inference(avatar_component_clause,[],[f484])).
% 0.20/0.42  fof(f484,plain,(
% 0.20/0.42    spl3_86 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1) | ~r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).
% 0.20/0.42  fof(f486,plain,(
% 0.20/0.42    spl3_86 | ~spl3_3 | ~spl3_35),
% 0.20/0.42    inference(avatar_split_clause,[],[f481,f204,f40,f484])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    spl3_3 <=> v1_relat_1(sK2)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.42  fof(f204,plain,(
% 0.20/0.42    spl3_35 <=> ! [X1,X3,X2] : (~r1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)),X3) | k1_xboole_0 = k7_relat_1(k7_relat_1(X1,X2),X3) | ~v1_relat_1(X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.42  fof(f481,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1) | ~r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X1)) ) | (~spl3_3 | ~spl3_35)),
% 0.20/0.42    inference(resolution,[],[f205,f42])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    v1_relat_1(sK2) | ~spl3_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f40])).
% 0.20/0.42  fof(f205,plain,(
% 0.20/0.42    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(X1,X2),X3) | ~r1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)),X3)) ) | ~spl3_35),
% 0.20/0.42    inference(avatar_component_clause,[],[f204])).
% 0.20/0.42  fof(f206,plain,(
% 0.20/0.42    spl3_35 | ~spl3_4 | ~spl3_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f198,f53,f45,f204])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    spl3_4 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl3_6 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.42  fof(f198,plain,(
% 0.20/0.42    ( ! [X2,X3,X1] : (~r1_xboole_0(k1_relat_1(k7_relat_1(X1,X2)),X3) | k1_xboole_0 = k7_relat_1(k7_relat_1(X1,X2),X3) | ~v1_relat_1(X1)) ) | (~spl3_4 | ~spl3_6)),
% 0.20/0.42    inference(resolution,[],[f54,f46])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f45])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = k1_xboole_0) ) | ~spl3_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f53])).
% 0.20/0.42  fof(f130,plain,(
% 0.20/0.42    spl3_21 | ~spl3_12 | ~spl3_18),
% 0.20/0.42    inference(avatar_split_clause,[],[f121,f113,f78,f127])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    spl3_12 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.42  fof(f113,plain,(
% 0.20/0.42    spl3_18 <=> ! [X1,X0] : r1_xboole_0(k1_relat_1(k7_relat_1(sK2,k4_xboole_0(X0,X1))),X1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.42  fof(f121,plain,(
% 0.20/0.42    r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) | (~spl3_12 | ~spl3_18)),
% 0.20/0.42    inference(superposition,[],[f114,f80])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_12),
% 0.20/0.42    inference(avatar_component_clause,[],[f78])).
% 0.20/0.42  fof(f114,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(k7_relat_1(sK2,k4_xboole_0(X0,X1))),X1)) ) | ~spl3_18),
% 0.20/0.42    inference(avatar_component_clause,[],[f113])).
% 0.20/0.42  fof(f115,plain,(
% 0.20/0.42    spl3_18 | ~spl3_3 | ~spl3_13),
% 0.20/0.42    inference(avatar_split_clause,[],[f110,f87,f40,f113])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    spl3_13 <=> ! [X1,X0,X2] : (r1_xboole_0(k1_relat_1(k7_relat_1(X0,k4_xboole_0(X1,X2))),X2) | ~v1_relat_1(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.42  fof(f110,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(k7_relat_1(sK2,k4_xboole_0(X0,X1))),X1)) ) | (~spl3_3 | ~spl3_13)),
% 0.20/0.42    inference(resolution,[],[f88,f42])).
% 0.20/0.42  fof(f88,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r1_xboole_0(k1_relat_1(k7_relat_1(X0,k4_xboole_0(X1,X2))),X2)) ) | ~spl3_13),
% 0.20/0.42    inference(avatar_component_clause,[],[f87])).
% 0.20/0.42  fof(f89,plain,(
% 0.20/0.42    spl3_13 | ~spl3_5 | ~spl3_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f84,f69,f49,f87])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    spl3_5 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    spl3_10 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.42  fof(f84,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(k1_relat_1(k7_relat_1(X0,k4_xboole_0(X1,X2))),X2) | ~v1_relat_1(X0)) ) | (~spl3_5 | ~spl3_10)),
% 0.20/0.42    inference(resolution,[],[f70,f50])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl3_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f49])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) ) | ~spl3_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f69])).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    spl3_12 | ~spl3_2 | ~spl3_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f76,f65,f35,f78])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    spl3_2 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    spl3_9 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    sK0 = k4_xboole_0(sK0,sK1) | (~spl3_2 | ~spl3_9)),
% 0.20/0.42    inference(resolution,[],[f66,f37])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    r1_xboole_0(sK0,sK1) | ~spl3_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f35])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl3_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f65])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    spl3_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f28,f69])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    spl3_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f65])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.42    inference(nnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    spl3_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f53])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1] : (((k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(nnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0,X1] : ((k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    spl3_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f49])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    spl3_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f21,f45])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    spl3_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f18,f40])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    v1_relat_1(sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2))),
% 0.20/0.42    inference(flattening,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.42    inference(negated_conjecture,[],[f6])).
% 0.20/0.42  fof(f6,conjecture,(
% 0.20/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f19,f35])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    r1_xboole_0(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ~spl3_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f20,f30])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (6481)------------------------------
% 0.20/0.42  % (6481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (6481)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (6481)Memory used [KB]: 10874
% 0.20/0.42  % (6481)Time elapsed: 0.013 s
% 0.20/0.42  % (6481)------------------------------
% 0.20/0.42  % (6481)------------------------------
% 0.20/0.43  % (6473)Success in time 0.071 s
%------------------------------------------------------------------------------
