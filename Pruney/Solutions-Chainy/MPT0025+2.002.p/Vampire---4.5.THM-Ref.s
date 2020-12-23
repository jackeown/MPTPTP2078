%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:38 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 110 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :    6
%              Number of atoms          :  146 ( 231 expanded)
%              Number of equality atoms :   22 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f328,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f32,f36,f40,f44,f48,f55,f66,f78,f95,f206,f242,f280,f327])).

fof(f327,plain,
    ( spl3_1
    | ~ spl3_13
    | ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | spl3_1
    | ~ spl3_13
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f315,f22])).

fof(f22,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f315,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_13
    | ~ spl3_33 ),
    inference(superposition,[],[f279,f87])).

fof(f87,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_13
  <=> ! [X3,X2] : k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f279,plain,
    ( ! [X24] : r1_tarski(sK0,k2_xboole_0(X24,k3_xboole_0(sK1,sK2)))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl3_33
  <=> ! [X24] : r1_tarski(sK0,k2_xboole_0(X24,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f280,plain,
    ( spl3_33
    | ~ spl3_9
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f265,f239,f63,f278])).

fof(f63,plain,
    ( spl3_9
  <=> k3_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f239,plain,
    ( spl3_29
  <=> ! [X3,X2,X4] : r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f265,plain,
    ( ! [X24] : r1_tarski(sK0,k2_xboole_0(X24,k3_xboole_0(sK1,sK2)))
    | ~ spl3_9
    | ~ spl3_29 ),
    inference(superposition,[],[f240,f65])).

fof(f65,plain,
    ( k3_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f240,plain,
    ( ! [X4,X2,X3] : r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X2)))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f239])).

fof(f242,plain,
    ( spl3_29
    | ~ spl3_5
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f224,f204,f38,f239])).

fof(f38,plain,
    ( spl3_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f204,plain,
    ( spl3_26
  <=> ! [X11,X13,X12] : r1_tarski(X13,k2_xboole_0(X11,k2_xboole_0(X12,X13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f224,plain,
    ( ! [X6,X7,X5] : r1_tarski(X6,k2_xboole_0(X7,k2_xboole_0(X6,X5)))
    | ~ spl3_5
    | ~ spl3_26 ),
    inference(superposition,[],[f205,f39])).

fof(f39,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f205,plain,
    ( ! [X12,X13,X11] : r1_tarski(X13,k2_xboole_0(X11,k2_xboole_0(X12,X13)))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f204])).

fof(f206,plain,
    ( spl3_26
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f146,f52,f46,f204])).

fof(f46,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f52,plain,
    ( spl3_8
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f146,plain,
    ( ! [X12,X13,X11] : r1_tarski(X13,k2_xboole_0(X11,k2_xboole_0(X12,X13)))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(superposition,[],[f53,f47])).

fof(f47,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f46])).

fof(f53,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f52])).

fof(f95,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f83,f76,f38,f86])).

fof(f76,plain,
    ( spl3_12
  <=> ! [X5,X4] : k2_xboole_0(k3_xboole_0(X4,X5),X4) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f83,plain,
    ( ! [X4,X5] : k2_xboole_0(X4,k3_xboole_0(X4,X5)) = X4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(superposition,[],[f39,f77])).

fof(f77,plain,
    ( ! [X4,X5] : k2_xboole_0(k3_xboole_0(X4,X5),X4) = X4
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f76])).

fof(f78,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f61,f42,f34,f76])).

fof(f34,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f42,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f61,plain,
    ( ! [X4,X5] : k2_xboole_0(k3_xboole_0(X4,X5),X4) = X4
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f42])).

fof(f66,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f58,f42,f25,f63])).

fof(f25,plain,
    ( spl3_2
  <=> r1_tarski(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f58,plain,
    ( k3_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f43,f27])).

fof(f27,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f55,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f50,f38,f30,f52])).

fof(f30,plain,
    ( spl3_3
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f50,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(superposition,[],[f31,f39])).

fof(f31,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f48,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f18,f46])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f44,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f40,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f36,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f34])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f32,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f28,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f12,f25])).

fof(f12,plain,(
    r1_tarski(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k3_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k3_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f23,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f13,f20])).

fof(f13,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:34:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.42  % (27039)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.14/0.42  % (27039)Refutation found. Thanks to Tanya!
% 0.14/0.42  % SZS status Theorem for theBenchmark
% 0.14/0.42  % SZS output start Proof for theBenchmark
% 0.14/0.42  fof(f328,plain,(
% 0.14/0.42    $false),
% 0.14/0.42    inference(avatar_sat_refutation,[],[f23,f28,f32,f36,f40,f44,f48,f55,f66,f78,f95,f206,f242,f280,f327])).
% 0.14/0.42  fof(f327,plain,(
% 0.14/0.42    spl3_1 | ~spl3_13 | ~spl3_33),
% 0.14/0.42    inference(avatar_contradiction_clause,[],[f326])).
% 0.14/0.42  fof(f326,plain,(
% 0.14/0.42    $false | (spl3_1 | ~spl3_13 | ~spl3_33)),
% 0.14/0.42    inference(subsumption_resolution,[],[f315,f22])).
% 0.14/0.42  fof(f22,plain,(
% 0.14/0.42    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.14/0.42    inference(avatar_component_clause,[],[f20])).
% 0.14/0.42  fof(f20,plain,(
% 0.14/0.42    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.14/0.42  fof(f315,plain,(
% 0.14/0.42    r1_tarski(sK0,sK1) | (~spl3_13 | ~spl3_33)),
% 0.14/0.42    inference(superposition,[],[f279,f87])).
% 0.14/0.42  fof(f87,plain,(
% 0.14/0.42    ( ! [X2,X3] : (k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2) ) | ~spl3_13),
% 0.14/0.42    inference(avatar_component_clause,[],[f86])).
% 0.14/0.42  fof(f86,plain,(
% 0.14/0.42    spl3_13 <=> ! [X3,X2] : k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.14/0.42  fof(f279,plain,(
% 0.14/0.42    ( ! [X24] : (r1_tarski(sK0,k2_xboole_0(X24,k3_xboole_0(sK1,sK2)))) ) | ~spl3_33),
% 0.14/0.42    inference(avatar_component_clause,[],[f278])).
% 0.14/0.42  fof(f278,plain,(
% 0.14/0.42    spl3_33 <=> ! [X24] : r1_tarski(sK0,k2_xboole_0(X24,k3_xboole_0(sK1,sK2)))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.14/0.42  fof(f280,plain,(
% 0.14/0.42    spl3_33 | ~spl3_9 | ~spl3_29),
% 0.14/0.42    inference(avatar_split_clause,[],[f265,f239,f63,f278])).
% 0.14/0.42  fof(f63,plain,(
% 0.14/0.42    spl3_9 <=> k3_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.14/0.42  fof(f239,plain,(
% 0.14/0.42    spl3_29 <=> ! [X3,X2,X4] : r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X2)))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.14/0.42  fof(f265,plain,(
% 0.14/0.42    ( ! [X24] : (r1_tarski(sK0,k2_xboole_0(X24,k3_xboole_0(sK1,sK2)))) ) | (~spl3_9 | ~spl3_29)),
% 0.14/0.42    inference(superposition,[],[f240,f65])).
% 0.14/0.42  fof(f65,plain,(
% 0.14/0.42    k3_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_9),
% 0.14/0.42    inference(avatar_component_clause,[],[f63])).
% 0.14/0.42  fof(f240,plain,(
% 0.14/0.42    ( ! [X4,X2,X3] : (r1_tarski(X3,k2_xboole_0(X4,k2_xboole_0(X3,X2)))) ) | ~spl3_29),
% 0.14/0.42    inference(avatar_component_clause,[],[f239])).
% 0.14/0.42  fof(f242,plain,(
% 0.14/0.42    spl3_29 | ~spl3_5 | ~spl3_26),
% 0.14/0.42    inference(avatar_split_clause,[],[f224,f204,f38,f239])).
% 0.14/0.42  fof(f38,plain,(
% 0.14/0.42    spl3_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.14/0.42  fof(f204,plain,(
% 0.14/0.42    spl3_26 <=> ! [X11,X13,X12] : r1_tarski(X13,k2_xboole_0(X11,k2_xboole_0(X12,X13)))),
% 0.14/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.14/0.42  fof(f224,plain,(
% 0.14/0.42    ( ! [X6,X7,X5] : (r1_tarski(X6,k2_xboole_0(X7,k2_xboole_0(X6,X5)))) ) | (~spl3_5 | ~spl3_26)),
% 0.14/0.42    inference(superposition,[],[f205,f39])).
% 0.14/0.42  fof(f39,plain,(
% 0.14/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.14/0.42    inference(avatar_component_clause,[],[f38])).
% 0.14/0.43  fof(f205,plain,(
% 0.14/0.43    ( ! [X12,X13,X11] : (r1_tarski(X13,k2_xboole_0(X11,k2_xboole_0(X12,X13)))) ) | ~spl3_26),
% 0.14/0.43    inference(avatar_component_clause,[],[f204])).
% 0.14/0.43  fof(f206,plain,(
% 0.14/0.43    spl3_26 | ~spl3_7 | ~spl3_8),
% 0.14/0.43    inference(avatar_split_clause,[],[f146,f52,f46,f204])).
% 0.14/0.43  fof(f46,plain,(
% 0.14/0.43    spl3_7 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.14/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.14/0.43  fof(f52,plain,(
% 0.14/0.43    spl3_8 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0))),
% 0.14/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.14/0.43  fof(f146,plain,(
% 0.14/0.43    ( ! [X12,X13,X11] : (r1_tarski(X13,k2_xboole_0(X11,k2_xboole_0(X12,X13)))) ) | (~spl3_7 | ~spl3_8)),
% 0.14/0.43    inference(superposition,[],[f53,f47])).
% 0.14/0.43  fof(f47,plain,(
% 0.14/0.43    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_7),
% 0.14/0.43    inference(avatar_component_clause,[],[f46])).
% 0.14/0.43  fof(f53,plain,(
% 0.14/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) ) | ~spl3_8),
% 0.14/0.43    inference(avatar_component_clause,[],[f52])).
% 0.14/0.43  fof(f95,plain,(
% 0.14/0.43    spl3_13 | ~spl3_5 | ~spl3_12),
% 0.14/0.43    inference(avatar_split_clause,[],[f83,f76,f38,f86])).
% 0.14/0.43  fof(f76,plain,(
% 0.14/0.43    spl3_12 <=> ! [X5,X4] : k2_xboole_0(k3_xboole_0(X4,X5),X4) = X4),
% 0.14/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.14/0.43  fof(f83,plain,(
% 0.14/0.43    ( ! [X4,X5] : (k2_xboole_0(X4,k3_xboole_0(X4,X5)) = X4) ) | (~spl3_5 | ~spl3_12)),
% 0.14/0.43    inference(superposition,[],[f39,f77])).
% 0.14/0.43  fof(f77,plain,(
% 0.14/0.43    ( ! [X4,X5] : (k2_xboole_0(k3_xboole_0(X4,X5),X4) = X4) ) | ~spl3_12),
% 0.14/0.43    inference(avatar_component_clause,[],[f76])).
% 0.14/0.43  fof(f78,plain,(
% 0.14/0.43    spl3_12 | ~spl3_4 | ~spl3_6),
% 0.14/0.43    inference(avatar_split_clause,[],[f61,f42,f34,f76])).
% 0.14/0.43  fof(f34,plain,(
% 0.14/0.43    spl3_4 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.14/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.14/0.43  fof(f42,plain,(
% 0.14/0.43    spl3_6 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.14/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.14/0.43  fof(f61,plain,(
% 0.14/0.43    ( ! [X4,X5] : (k2_xboole_0(k3_xboole_0(X4,X5),X4) = X4) ) | (~spl3_4 | ~spl3_6)),
% 0.14/0.43    inference(resolution,[],[f43,f35])).
% 0.14/0.43  fof(f35,plain,(
% 0.14/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_4),
% 0.14/0.43    inference(avatar_component_clause,[],[f34])).
% 0.14/0.43  fof(f43,plain,(
% 0.14/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_6),
% 0.14/0.43    inference(avatar_component_clause,[],[f42])).
% 0.14/0.43  fof(f66,plain,(
% 0.14/0.43    spl3_9 | ~spl3_2 | ~spl3_6),
% 0.14/0.43    inference(avatar_split_clause,[],[f58,f42,f25,f63])).
% 0.14/0.43  fof(f25,plain,(
% 0.14/0.43    spl3_2 <=> r1_tarski(sK0,k3_xboole_0(sK1,sK2))),
% 0.14/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.14/0.43  fof(f58,plain,(
% 0.14/0.43    k3_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_6)),
% 0.14/0.43    inference(resolution,[],[f43,f27])).
% 0.14/0.43  fof(f27,plain,(
% 0.14/0.43    r1_tarski(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.14/0.43    inference(avatar_component_clause,[],[f25])).
% 0.14/0.43  fof(f55,plain,(
% 0.14/0.43    spl3_8 | ~spl3_3 | ~spl3_5),
% 0.14/0.43    inference(avatar_split_clause,[],[f50,f38,f30,f52])).
% 0.14/0.43  fof(f30,plain,(
% 0.14/0.43    spl3_3 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.14/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.14/0.43  fof(f50,plain,(
% 0.14/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) ) | (~spl3_3 | ~spl3_5)),
% 0.14/0.43    inference(superposition,[],[f31,f39])).
% 0.14/0.43  fof(f31,plain,(
% 0.14/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_3),
% 0.14/0.43    inference(avatar_component_clause,[],[f30])).
% 0.14/0.43  fof(f48,plain,(
% 0.14/0.43    spl3_7),
% 0.14/0.43    inference(avatar_split_clause,[],[f18,f46])).
% 0.14/0.43  fof(f18,plain,(
% 0.14/0.43    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.14/0.43    inference(cnf_transformation,[],[f4])).
% 0.14/0.43  fof(f4,axiom,(
% 0.14/0.43    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.14/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.14/0.43  fof(f44,plain,(
% 0.14/0.43    spl3_6),
% 0.14/0.43    inference(avatar_split_clause,[],[f17,f42])).
% 0.14/0.43  fof(f17,plain,(
% 0.14/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.14/0.43    inference(cnf_transformation,[],[f9])).
% 0.14/0.43  fof(f9,plain,(
% 0.14/0.43    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.14/0.43    inference(ennf_transformation,[],[f2])).
% 0.14/0.43  fof(f2,axiom,(
% 0.14/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.14/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.14/0.43  fof(f40,plain,(
% 0.14/0.43    spl3_5),
% 0.14/0.43    inference(avatar_split_clause,[],[f16,f38])).
% 0.14/0.43  fof(f16,plain,(
% 0.14/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.14/0.43    inference(cnf_transformation,[],[f1])).
% 0.14/0.43  fof(f1,axiom,(
% 0.14/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.14/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.14/0.43  fof(f36,plain,(
% 0.14/0.43    spl3_4),
% 0.14/0.43    inference(avatar_split_clause,[],[f15,f34])).
% 0.14/0.43  fof(f15,plain,(
% 0.14/0.43    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.14/0.43    inference(cnf_transformation,[],[f3])).
% 0.14/0.43  fof(f3,axiom,(
% 0.14/0.43    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.14/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.14/0.43  fof(f32,plain,(
% 0.14/0.43    spl3_3),
% 0.14/0.43    inference(avatar_split_clause,[],[f14,f30])).
% 0.14/0.43  fof(f14,plain,(
% 0.14/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.14/0.43    inference(cnf_transformation,[],[f5])).
% 0.14/0.43  fof(f5,axiom,(
% 0.14/0.43    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.14/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.14/0.43  fof(f28,plain,(
% 0.14/0.43    spl3_2),
% 0.14/0.43    inference(avatar_split_clause,[],[f12,f25])).
% 0.14/0.43  fof(f12,plain,(
% 0.14/0.43    r1_tarski(sK0,k3_xboole_0(sK1,sK2))),
% 0.14/0.43    inference(cnf_transformation,[],[f11])).
% 0.14/0.43  fof(f11,plain,(
% 0.14/0.43    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k3_xboole_0(sK1,sK2))),
% 0.14/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10])).
% 0.14/0.43  fof(f10,plain,(
% 0.14/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k3_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k3_xboole_0(sK1,sK2)))),
% 0.14/0.43    introduced(choice_axiom,[])).
% 0.14/0.43  fof(f8,plain,(
% 0.14/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.14/0.43    inference(ennf_transformation,[],[f7])).
% 0.14/0.43  fof(f7,negated_conjecture,(
% 0.14/0.43    ~! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.14/0.43    inference(negated_conjecture,[],[f6])).
% 0.14/0.43  fof(f6,conjecture,(
% 0.14/0.43    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.14/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.14/0.43  fof(f23,plain,(
% 0.14/0.43    ~spl3_1),
% 0.14/0.43    inference(avatar_split_clause,[],[f13,f20])).
% 0.14/0.43  fof(f13,plain,(
% 0.14/0.43    ~r1_tarski(sK0,sK1)),
% 0.14/0.43    inference(cnf_transformation,[],[f11])).
% 0.14/0.43  % SZS output end Proof for theBenchmark
% 0.14/0.43  % (27039)------------------------------
% 0.14/0.43  % (27039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.43  % (27039)Termination reason: Refutation
% 0.14/0.43  
% 0.14/0.43  % (27039)Memory used [KB]: 10746
% 0.14/0.43  % (27039)Time elapsed: 0.009 s
% 0.14/0.43  % (27039)------------------------------
% 0.14/0.43  % (27039)------------------------------
% 0.22/0.43  % (27028)Success in time 0.068 s
%------------------------------------------------------------------------------
