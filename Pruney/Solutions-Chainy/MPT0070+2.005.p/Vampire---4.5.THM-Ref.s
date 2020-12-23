%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 199 expanded)
%              Number of leaves         :   37 (  97 expanded)
%              Depth                    :    7
%              Number of atoms          :  283 ( 467 expanded)
%              Number of equality atoms :   81 ( 135 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f54,f58,f62,f70,f74,f78,f82,f86,f98,f102,f144,f162,f213,f228,f262,f314,f561,f566,f720,f761,f830,f1058,f1225])).

fof(f1225,plain,
    ( spl3_43
    | ~ spl3_47
    | ~ spl3_57 ),
    inference(avatar_contradiction_clause,[],[f1224])).

fof(f1224,plain,
    ( $false
    | spl3_43
    | ~ spl3_47
    | ~ spl3_57 ),
    inference(subsumption_resolution,[],[f760,f1209])).

fof(f1209,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK0)
    | ~ spl3_47
    | ~ spl3_57 ),
    inference(superposition,[],[f1057,f829])).

fof(f829,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f827])).

fof(f827,plain,
    ( spl3_47
  <=> sK2 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f1057,plain,
    ( ! [X3] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,sK1),sK0)
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f1056])).

fof(f1056,plain,
    ( spl3_57
  <=> ! [X3] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f760,plain,
    ( k1_xboole_0 != k3_xboole_0(sK2,sK0)
    | spl3_43 ),
    inference(avatar_component_clause,[],[f758])).

fof(f758,plain,
    ( spl3_43
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f1058,plain,
    ( spl3_57
    | ~ spl3_24
    | ~ spl3_38
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f732,f717,f559,f211,f1056])).

fof(f211,plain,
    ( spl3_24
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f559,plain,
    ( spl3_38
  <=> ! [X5,X7,X6] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k2_xboole_0(X6,X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f717,plain,
    ( spl3_41
  <=> sK1 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f732,plain,
    ( ! [X3] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,sK1),sK0)
    | ~ spl3_24
    | ~ spl3_38
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f729,f212])).

fof(f212,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f211])).

fof(f729,plain,
    ( ! [X3] : k3_xboole_0(k4_xboole_0(X3,sK1),sK0) = k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK1))
    | ~ spl3_38
    | ~ spl3_41 ),
    inference(superposition,[],[f560,f719])).

fof(f719,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f717])).

fof(f560,plain,
    ( ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k2_xboole_0(X6,X7)))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f559])).

fof(f830,plain,
    ( spl3_47
    | ~ spl3_32
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f711,f563,f312,f827])).

fof(f312,plain,
    ( spl3_32
  <=> ! [X1,X2] :
        ( k4_xboole_0(X1,X2) = X1
        | ~ r1_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f563,plain,
    ( spl3_39
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f711,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl3_32
    | ~ spl3_39 ),
    inference(unit_resulting_resolution,[],[f565,f313])).

fof(f313,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | ~ r1_xboole_0(X1,X2) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f312])).

fof(f565,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f563])).

fof(f761,plain,
    ( ~ spl3_43
    | spl3_3
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f263,f260,f47,f758])).

fof(f47,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f260,plain,
    ( spl3_28
  <=> ! [X3,X4] :
        ( k1_xboole_0 != k3_xboole_0(X4,X3)
        | r1_xboole_0(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f263,plain,
    ( k1_xboole_0 != k3_xboole_0(sK2,sK0)
    | spl3_3
    | ~ spl3_28 ),
    inference(unit_resulting_resolution,[],[f49,f261])).

fof(f261,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 != k3_xboole_0(X4,X3)
        | r1_xboole_0(X3,X4) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f260])).

fof(f49,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f720,plain,
    ( spl3_41
    | ~ spl3_1
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f229,f226,f37,f717])).

fof(f37,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f226,plain,
    ( spl3_26
  <=> ! [X5,X4] :
        ( k2_xboole_0(X5,X4) = X5
        | ~ r1_tarski(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f229,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_26 ),
    inference(unit_resulting_resolution,[],[f39,f227])).

fof(f227,plain,
    ( ! [X4,X5] :
        ( k2_xboole_0(X5,X4) = X5
        | ~ r1_tarski(X4,X5) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f226])).

fof(f39,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f566,plain,
    ( spl3_39
    | ~ spl3_17
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f265,f260,f159,f563])).

fof(f159,plain,
    ( spl3_17
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f265,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl3_17
    | ~ spl3_28 ),
    inference(unit_resulting_resolution,[],[f161,f261])).

fof(f161,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f159])).

fof(f561,plain,
    ( spl3_38
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f152,f142,f96,f559])).

fof(f96,plain,
    ( spl3_13
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f142,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f152,plain,
    ( ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k2_xboole_0(X6,X7)))
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(superposition,[],[f97,f143])).

fof(f143,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f142])).

fof(f97,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f96])).

fof(f314,plain,
    ( spl3_32
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f134,f100,f80,f72,f60,f312])).

fof(f60,plain,
    ( spl3_6
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f72,plain,
    ( spl3_9
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f80,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f100,plain,
    ( spl3_14
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f134,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | ~ r1_xboole_0(X1,X2) )
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f126,f91])).

fof(f91,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f73,f61])).

fof(f61,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f73,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f72])).

fof(f126,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = X1
        | ~ r1_xboole_0(X1,X2) )
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(superposition,[],[f101,f81])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f80])).

fof(f101,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f100])).

fof(f262,plain,
    ( spl3_28
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f119,f84,f68,f260])).

fof(f68,plain,
    ( spl3_8
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f84,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f119,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 != k3_xboole_0(X4,X3)
        | r1_xboole_0(X3,X4) )
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(superposition,[],[f85,f69])).

fof(f69,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f228,plain,
    ( spl3_26
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f105,f76,f72,f226])).

fof(f76,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f105,plain,
    ( ! [X4,X5] :
        ( k2_xboole_0(X5,X4) = X5
        | ~ r1_tarski(X4,X5) )
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(superposition,[],[f77,f73])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f76])).

fof(f213,plain,
    ( spl3_24
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f124,f96,f56,f52,f211])).

fof(f52,plain,
    ( spl3_4
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f56,plain,
    ( spl3_5
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f124,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f122,f53])).

fof(f53,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f122,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(superposition,[],[f97,f57])).

fof(f57,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f162,plain,
    ( spl3_17
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f110,f80,f42,f159])).

fof(f42,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f110,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f44,f81])).

fof(f44,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f144,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f35,f142])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f102,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f31,f100])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f98,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f30,f96])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f86,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f34,f84])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f82,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f33,f80])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f32,f76])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f74,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f70,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f62,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f58,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f54,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f50,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f45,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f42])).

fof(f22,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f21,f37])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:38:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (8537)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (8535)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (8538)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (8536)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (8547)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (8545)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (8543)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (8544)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (8548)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (8540)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (8544)Refutation not found, incomplete strategy% (8544)------------------------------
% 0.21/0.48  % (8544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8544)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (8544)Memory used [KB]: 10618
% 0.21/0.48  % (8544)Time elapsed: 0.064 s
% 0.21/0.48  % (8544)------------------------------
% 0.21/0.48  % (8544)------------------------------
% 0.21/0.49  % (8542)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (8541)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (8538)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (8533)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (8539)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (8550)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (8534)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (8546)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f1244,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f40,f45,f50,f54,f58,f62,f70,f74,f78,f82,f86,f98,f102,f144,f162,f213,f228,f262,f314,f561,f566,f720,f761,f830,f1058,f1225])).
% 0.21/0.51  fof(f1225,plain,(
% 0.21/0.51    spl3_43 | ~spl3_47 | ~spl3_57),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f1224])).
% 0.21/0.51  fof(f1224,plain,(
% 0.21/0.51    $false | (spl3_43 | ~spl3_47 | ~spl3_57)),
% 0.21/0.51    inference(subsumption_resolution,[],[f760,f1209])).
% 0.21/0.51  fof(f1209,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(sK2,sK0) | (~spl3_47 | ~spl3_57)),
% 0.21/0.51    inference(superposition,[],[f1057,f829])).
% 0.21/0.51  fof(f829,plain,(
% 0.21/0.51    sK2 = k4_xboole_0(sK2,sK1) | ~spl3_47),
% 0.21/0.51    inference(avatar_component_clause,[],[f827])).
% 0.21/0.51  fof(f827,plain,(
% 0.21/0.51    spl3_47 <=> sK2 = k4_xboole_0(sK2,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.51  fof(f1057,plain,(
% 0.21/0.51    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,sK1),sK0)) ) | ~spl3_57),
% 0.21/0.51    inference(avatar_component_clause,[],[f1056])).
% 0.21/0.51  fof(f1056,plain,(
% 0.21/0.51    spl3_57 <=> ! [X3] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.21/0.51  fof(f760,plain,(
% 0.21/0.51    k1_xboole_0 != k3_xboole_0(sK2,sK0) | spl3_43),
% 0.21/0.51    inference(avatar_component_clause,[],[f758])).
% 0.21/0.51  fof(f758,plain,(
% 0.21/0.51    spl3_43 <=> k1_xboole_0 = k3_xboole_0(sK2,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.51  fof(f1058,plain,(
% 0.21/0.51    spl3_57 | ~spl3_24 | ~spl3_38 | ~spl3_41),
% 0.21/0.51    inference(avatar_split_clause,[],[f732,f717,f559,f211,f1056])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    spl3_24 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.51  fof(f559,plain,(
% 0.21/0.51    spl3_38 <=> ! [X5,X7,X6] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k2_xboole_0(X6,X7)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.51  fof(f717,plain,(
% 0.21/0.51    spl3_41 <=> sK1 = k2_xboole_0(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.51  fof(f732,plain,(
% 0.21/0.51    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,sK1),sK0)) ) | (~spl3_24 | ~spl3_38 | ~spl3_41)),
% 0.21/0.51    inference(forward_demodulation,[],[f729,f212])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl3_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f211])).
% 0.21/0.51  fof(f729,plain,(
% 0.21/0.51    ( ! [X3] : (k3_xboole_0(k4_xboole_0(X3,sK1),sK0) = k4_xboole_0(k4_xboole_0(X3,sK1),k4_xboole_0(X3,sK1))) ) | (~spl3_38 | ~spl3_41)),
% 0.21/0.51    inference(superposition,[],[f560,f719])).
% 0.21/0.51  fof(f719,plain,(
% 0.21/0.51    sK1 = k2_xboole_0(sK1,sK0) | ~spl3_41),
% 0.21/0.51    inference(avatar_component_clause,[],[f717])).
% 0.21/0.51  fof(f560,plain,(
% 0.21/0.51    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k2_xboole_0(X6,X7)))) ) | ~spl3_38),
% 0.21/0.51    inference(avatar_component_clause,[],[f559])).
% 0.21/0.51  fof(f830,plain,(
% 0.21/0.51    spl3_47 | ~spl3_32 | ~spl3_39),
% 0.21/0.51    inference(avatar_split_clause,[],[f711,f563,f312,f827])).
% 0.21/0.51  fof(f312,plain,(
% 0.21/0.51    spl3_32 <=> ! [X1,X2] : (k4_xboole_0(X1,X2) = X1 | ~r1_xboole_0(X1,X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.51  fof(f563,plain,(
% 0.21/0.51    spl3_39 <=> r1_xboole_0(sK2,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.51  fof(f711,plain,(
% 0.21/0.51    sK2 = k4_xboole_0(sK2,sK1) | (~spl3_32 | ~spl3_39)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f565,f313])).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | ~r1_xboole_0(X1,X2)) ) | ~spl3_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f312])).
% 0.21/0.51  fof(f565,plain,(
% 0.21/0.51    r1_xboole_0(sK2,sK1) | ~spl3_39),
% 0.21/0.51    inference(avatar_component_clause,[],[f563])).
% 0.21/0.51  fof(f761,plain,(
% 0.21/0.51    ~spl3_43 | spl3_3 | ~spl3_28),
% 0.21/0.51    inference(avatar_split_clause,[],[f263,f260,f47,f758])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    spl3_3 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    spl3_28 <=> ! [X3,X4] : (k1_xboole_0 != k3_xboole_0(X4,X3) | r1_xboole_0(X3,X4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.51  fof(f263,plain,(
% 0.21/0.51    k1_xboole_0 != k3_xboole_0(sK2,sK0) | (spl3_3 | ~spl3_28)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f49,f261])).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k1_xboole_0 != k3_xboole_0(X4,X3) | r1_xboole_0(X3,X4)) ) | ~spl3_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f260])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ~r1_xboole_0(sK0,sK2) | spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f47])).
% 0.21/0.51  fof(f720,plain,(
% 0.21/0.51    spl3_41 | ~spl3_1 | ~spl3_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f229,f226,f37,f717])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    spl3_26 <=> ! [X5,X4] : (k2_xboole_0(X5,X4) = X5 | ~r1_tarski(X4,X5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.51  fof(f229,plain,(
% 0.21/0.51    sK1 = k2_xboole_0(sK1,sK0) | (~spl3_1 | ~spl3_26)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f39,f227])).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    ( ! [X4,X5] : (k2_xboole_0(X5,X4) = X5 | ~r1_tarski(X4,X5)) ) | ~spl3_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f226])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f37])).
% 0.21/0.51  fof(f566,plain,(
% 0.21/0.51    spl3_39 | ~spl3_17 | ~spl3_28),
% 0.21/0.51    inference(avatar_split_clause,[],[f265,f260,f159,f563])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    spl3_17 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    r1_xboole_0(sK2,sK1) | (~spl3_17 | ~spl3_28)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f161,f261])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl3_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f159])).
% 0.21/0.51  fof(f561,plain,(
% 0.21/0.51    spl3_38 | ~spl3_13 | ~spl3_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f152,f142,f96,f559])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl3_13 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl3_16 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k2_xboole_0(X6,X7)))) ) | (~spl3_13 | ~spl3_16)),
% 0.21/0.51    inference(superposition,[],[f97,f143])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f142])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f314,plain,(
% 0.21/0.51    spl3_32 | ~spl3_6 | ~spl3_9 | ~spl3_11 | ~spl3_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f134,f100,f80,f72,f60,f312])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    spl3_6 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl3_9 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl3_11 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl3_14 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | ~r1_xboole_0(X1,X2)) ) | (~spl3_6 | ~spl3_9 | ~spl3_11 | ~spl3_14)),
% 0.21/0.51    inference(forward_demodulation,[],[f126,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl3_6 | ~spl3_9)),
% 0.21/0.51    inference(superposition,[],[f73,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f60])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f72])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = X1 | ~r1_xboole_0(X1,X2)) ) | (~spl3_11 | ~spl3_14)),
% 0.21/0.51    inference(superposition,[],[f101,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl3_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f100])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    spl3_28 | ~spl3_8 | ~spl3_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f119,f84,f68,f260])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl3_8 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl3_12 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k1_xboole_0 != k3_xboole_0(X4,X3) | r1_xboole_0(X3,X4)) ) | (~spl3_8 | ~spl3_12)),
% 0.21/0.51    inference(superposition,[],[f85,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f68])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl3_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f84])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    spl3_26 | ~spl3_9 | ~spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f105,f76,f72,f226])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl3_10 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X4,X5] : (k2_xboole_0(X5,X4) = X5 | ~r1_tarski(X4,X5)) ) | (~spl3_9 | ~spl3_10)),
% 0.21/0.51    inference(superposition,[],[f77,f73])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f76])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    spl3_24 | ~spl3_4 | ~spl3_5 | ~spl3_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f124,f96,f56,f52,f211])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    spl3_4 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    spl3_5 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl3_4 | ~spl3_5 | ~spl3_13)),
% 0.21/0.51    inference(forward_demodulation,[],[f122,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f52])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) ) | (~spl3_5 | ~spl3_13)),
% 0.21/0.51    inference(superposition,[],[f97,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f56])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    spl3_17 | ~spl3_2 | ~spl3_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f110,f80,f42,f159])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    spl3_2 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(sK1,sK2) | (~spl3_2 | ~spl3_11)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f44,f81])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    r1_xboole_0(sK1,sK2) | ~spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f42])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    spl3_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f142])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl3_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f31,f100])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    spl3_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f96])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl3_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f84])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl3_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f80])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f76])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f72])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f28,f68])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f60])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f25,f56])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f24,f52])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ~spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f23,f47])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ~r1_xboole_0(sK0,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.51    inference(negated_conjecture,[],[f12])).
% 0.21/0.51  fof(f12,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f22,f42])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    r1_xboole_0(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f21,f37])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    r1_tarski(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (8538)------------------------------
% 0.21/0.51  % (8538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8538)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (8538)Memory used [KB]: 7291
% 0.21/0.51  % (8538)Time elapsed: 0.075 s
% 0.21/0.51  % (8538)------------------------------
% 0.21/0.51  % (8538)------------------------------
% 0.21/0.52  % (8532)Success in time 0.153 s
%------------------------------------------------------------------------------
