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
% DateTime   : Thu Dec  3 12:31:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 141 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :    7
%              Number of atoms          :  201 ( 326 expanded)
%              Number of equality atoms :   56 (  90 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f40,f44,f48,f52,f60,f64,f68,f72,f83,f93,f101,f110,f123,f177,f208,f256,f284])).

fof(f284,plain,
    ( spl3_1
    | ~ spl3_10
    | ~ spl3_34 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | spl3_1
    | ~ spl3_10
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f273,f29])).

fof(f29,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f273,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_10
    | ~ spl3_34 ),
    inference(trivial_inequality_removal,[],[f272])).

fof(f272,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1)
    | ~ spl3_10
    | ~ spl3_34 ),
    inference(superposition,[],[f67,f254])).

fof(f254,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl3_34
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k4_xboole_0(X0,X1)
        | r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f256,plain,
    ( spl3_34
    | ~ spl3_14
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f246,f205,f98,f252])).

fof(f98,plain,
    ( spl3_14
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f205,plain,
    ( spl3_28
  <=> ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f246,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_14
    | ~ spl3_28 ),
    inference(superposition,[],[f100,f206])).

fof(f206,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f205])).

fof(f100,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f208,plain,
    ( spl3_28
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f194,f175,f46,f205])).

fof(f46,plain,
    ( spl3_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f175,plain,
    ( spl3_23
  <=> ! [X1] : k4_xboole_0(sK0,k2_xboole_0(sK2,X1)) = k4_xboole_0(sK0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f194,plain,
    ( ! [X1] : k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k2_xboole_0(X1,sK2))
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(superposition,[],[f176,f47])).

fof(f47,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f176,plain,
    ( ! [X1] : k4_xboole_0(sK0,k2_xboole_0(sK2,X1)) = k4_xboole_0(sK0,X1)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f175])).

fof(f177,plain,
    ( spl3_23
    | ~ spl3_11
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f166,f119,f70,f175])).

fof(f70,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f119,plain,
    ( spl3_17
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f166,plain,
    ( ! [X1] : k4_xboole_0(sK0,k2_xboole_0(sK2,X1)) = k4_xboole_0(sK0,X1)
    | ~ spl3_11
    | ~ spl3_17 ),
    inference(superposition,[],[f71,f121])).

fof(f121,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f119])).

fof(f71,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f70])).

fof(f123,plain,
    ( spl3_17
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f117,f107,f78,f119])).

fof(f78,plain,
    ( spl3_12
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f107,plain,
    ( spl3_15
  <=> sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f117,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(superposition,[],[f79,f109])).

fof(f109,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f107])).

fof(f79,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f110,plain,
    ( spl3_15
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f104,f90,f50,f107])).

fof(f50,plain,
    ( spl3_6
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f90,plain,
    ( spl3_13
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f104,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(superposition,[],[f51,f92])).

fof(f92,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f51,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f101,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f96,f62,f37,f98])).

fof(f37,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f62,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f96,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f93,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f88,f58,f32,f90])).

fof(f32,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f58,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f88,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f59,f34])).

fof(f34,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f83,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f76,f46,f42,f78])).

fof(f42,plain,
    ( spl3_4
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f76,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f43,f47])).

fof(f43,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f72,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f25,f70])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f68,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f23,f66])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f64,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f24,f62])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f21,f58])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f52,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f48,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f46])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f44,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f40,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f37])).

fof(f15,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f35,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f27])).

fof(f17,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:36:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (12658)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (12660)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.42  % (12658)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f285,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f30,f35,f40,f44,f48,f52,f60,f64,f68,f72,f83,f93,f101,f110,f123,f177,f208,f256,f284])).
% 0.20/0.43  fof(f284,plain,(
% 0.20/0.43    spl3_1 | ~spl3_10 | ~spl3_34),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f283])).
% 0.20/0.43  fof(f283,plain,(
% 0.20/0.43    $false | (spl3_1 | ~spl3_10 | ~spl3_34)),
% 0.20/0.43    inference(subsumption_resolution,[],[f273,f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.43  fof(f273,plain,(
% 0.20/0.43    r1_tarski(sK0,sK1) | (~spl3_10 | ~spl3_34)),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f272])).
% 0.20/0.43  fof(f272,plain,(
% 0.20/0.43    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) | (~spl3_10 | ~spl3_34)),
% 0.20/0.43    inference(superposition,[],[f67,f254])).
% 0.20/0.43  fof(f254,plain,(
% 0.20/0.43    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_34),
% 0.20/0.43    inference(avatar_component_clause,[],[f252])).
% 0.20/0.43  fof(f252,plain,(
% 0.20/0.43    spl3_34 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f66])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    spl3_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.43  fof(f256,plain,(
% 0.20/0.43    spl3_34 | ~spl3_14 | ~spl3_28),
% 0.20/0.43    inference(avatar_split_clause,[],[f246,f205,f98,f252])).
% 0.20/0.43  fof(f98,plain,(
% 0.20/0.43    spl3_14 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.43  fof(f205,plain,(
% 0.20/0.43    spl3_28 <=> ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.43  fof(f246,plain,(
% 0.20/0.43    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_14 | ~spl3_28)),
% 0.20/0.43    inference(superposition,[],[f100,f206])).
% 0.20/0.43  fof(f206,plain,(
% 0.20/0.43    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK2))) ) | ~spl3_28),
% 0.20/0.43    inference(avatar_component_clause,[],[f205])).
% 0.20/0.43  fof(f100,plain,(
% 0.20/0.43    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f98])).
% 0.20/0.43  fof(f208,plain,(
% 0.20/0.43    spl3_28 | ~spl3_5 | ~spl3_23),
% 0.20/0.43    inference(avatar_split_clause,[],[f194,f175,f46,f205])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    spl3_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.43  fof(f175,plain,(
% 0.20/0.43    spl3_23 <=> ! [X1] : k4_xboole_0(sK0,k2_xboole_0(sK2,X1)) = k4_xboole_0(sK0,X1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.43  fof(f194,plain,(
% 0.20/0.43    ( ! [X1] : (k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k2_xboole_0(X1,sK2))) ) | (~spl3_5 | ~spl3_23)),
% 0.20/0.43    inference(superposition,[],[f176,f47])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f46])).
% 0.20/0.43  fof(f176,plain,(
% 0.20/0.43    ( ! [X1] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X1)) = k4_xboole_0(sK0,X1)) ) | ~spl3_23),
% 0.20/0.43    inference(avatar_component_clause,[],[f175])).
% 0.20/0.43  fof(f177,plain,(
% 0.20/0.43    spl3_23 | ~spl3_11 | ~spl3_17),
% 0.20/0.43    inference(avatar_split_clause,[],[f166,f119,f70,f175])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    spl3_11 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    spl3_17 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.43  fof(f166,plain,(
% 0.20/0.43    ( ! [X1] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X1)) = k4_xboole_0(sK0,X1)) ) | (~spl3_11 | ~spl3_17)),
% 0.20/0.43    inference(superposition,[],[f71,f121])).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f119])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f70])).
% 0.20/0.43  fof(f123,plain,(
% 0.20/0.43    spl3_17 | ~spl3_12 | ~spl3_15),
% 0.20/0.43    inference(avatar_split_clause,[],[f117,f107,f78,f119])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    spl3_12 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    spl3_15 <=> sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    sK0 = k4_xboole_0(sK0,sK2) | (~spl3_12 | ~spl3_15)),
% 0.20/0.43    inference(superposition,[],[f79,f109])).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) | ~spl3_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f107])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl3_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f78])).
% 0.20/0.43  fof(f110,plain,(
% 0.20/0.43    spl3_15 | ~spl3_6 | ~spl3_13),
% 0.20/0.43    inference(avatar_split_clause,[],[f104,f90,f50,f107])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    spl3_6 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    spl3_13 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.43  fof(f104,plain,(
% 0.20/0.43    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) | (~spl3_6 | ~spl3_13)),
% 0.20/0.43    inference(superposition,[],[f51,f92])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f90])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl3_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f50])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    spl3_14 | ~spl3_3 | ~spl3_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f96,f62,f37,f98])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    spl3_3 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    spl3_9 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.43  fof(f96,plain,(
% 0.20/0.43    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_9)),
% 0.20/0.43    inference(resolution,[],[f63,f39])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f37])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) ) | ~spl3_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f62])).
% 0.20/0.43  fof(f93,plain,(
% 0.20/0.43    spl3_13 | ~spl3_2 | ~spl3_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f88,f58,f32,f90])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    spl3_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    k1_xboole_0 = k3_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_8)),
% 0.20/0.43    inference(resolution,[],[f59,f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    r1_xboole_0(sK0,sK2) | ~spl3_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f32])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f58])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    spl3_12 | ~spl3_4 | ~spl3_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f76,f46,f42,f78])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    spl3_4 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl3_4 | ~spl3_5)),
% 0.20/0.43    inference(superposition,[],[f43,f47])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f42])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    spl3_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f70])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    spl3_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f23,f66])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.43    inference(nnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    spl3_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f62])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    spl3_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f21,f58])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.43    inference(nnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    spl3_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f20,f50])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    spl3_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f19,f46])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    spl3_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f18,f42])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    spl3_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f15,f37])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.43    inference(flattening,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.20/0.43    inference(negated_conjecture,[],[f7])).
% 0.20/0.43  fof(f7,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    spl3_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f16,f32])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    r1_xboole_0(sK0,sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ~spl3_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f17,f27])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ~r1_tarski(sK0,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (12658)------------------------------
% 0.20/0.43  % (12658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (12658)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (12658)Memory used [KB]: 10746
% 0.20/0.43  % (12658)Time elapsed: 0.008 s
% 0.20/0.43  % (12658)------------------------------
% 0.20/0.43  % (12658)------------------------------
% 0.20/0.43  % (12652)Success in time 0.065 s
%------------------------------------------------------------------------------
