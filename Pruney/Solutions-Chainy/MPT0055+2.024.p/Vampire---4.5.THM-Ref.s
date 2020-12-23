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
% DateTime   : Thu Dec  3 12:30:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 167 expanded)
%              Number of leaves         :   30 (  83 expanded)
%              Depth                    :    6
%              Number of atoms          :  254 ( 405 expanded)
%              Number of equality atoms :   67 ( 118 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1330,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f47,f51,f55,f59,f67,f71,f79,f83,f87,f164,f212,f270,f297,f812,f1045,f1049,f1125,f1233,f1286])).

fof(f1286,plain,
    ( spl4_1
    | ~ spl4_69 ),
    inference(avatar_contradiction_clause,[],[f1248])).

fof(f1248,plain,
    ( $false
    | spl4_1
    | ~ spl4_69 ),
    inference(unit_resulting_resolution,[],[f38,f1232])).

fof(f1232,plain,
    ( ! [X26,X27] : k3_xboole_0(X26,X27) = k4_xboole_0(X26,k4_xboole_0(X26,X27))
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f1231])).

fof(f1231,plain,
    ( spl4_69
  <=> ! [X27,X26] : k3_xboole_0(X26,X27) = k4_xboole_0(X26,k4_xboole_0(X26,X27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f38,plain,
    ( k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl4_1
  <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1233,plain,
    ( spl4_69
    | ~ spl4_32
    | ~ spl4_66
    | ~ spl4_67 ),
    inference(avatar_split_clause,[],[f1185,f1123,f1047,f268,f1231])).

fof(f268,plain,
    ( spl4_32
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f1047,plain,
    ( spl4_66
  <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f1123,plain,
    ( spl4_67
  <=> ! [X7,X6] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f1185,plain,
    ( ! [X26,X27] : k3_xboole_0(X26,X27) = k4_xboole_0(X26,k4_xboole_0(X26,X27))
    | ~ spl4_32
    | ~ spl4_66
    | ~ spl4_67 ),
    inference(forward_demodulation,[],[f1144,f1048])).

fof(f1048,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f1047])).

fof(f1144,plain,
    ( ! [X26,X27] : k3_xboole_0(X26,X27) = k4_xboole_0(X26,k4_xboole_0(k4_xboole_0(X26,X27),k3_xboole_0(X26,X27)))
    | ~ spl4_32
    | ~ spl4_67 ),
    inference(superposition,[],[f1124,f269])).

fof(f269,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f268])).

fof(f1124,plain,
    ( ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6
    | ~ spl4_67 ),
    inference(avatar_component_clause,[],[f1123])).

fof(f1125,plain,
    ( spl4_67
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_34
    | ~ spl4_65 ),
    inference(avatar_split_clause,[],[f1106,f1043,f295,f81,f41,f1123])).

fof(f41,plain,
    ( spl4_2
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f81,plain,
    ( spl4_12
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f295,plain,
    ( spl4_34
  <=> ! [X7,X6] : k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f1043,plain,
    ( spl4_65
  <=> ! [X1,X0] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f1106,plain,
    ( ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_34
    | ~ spl4_65 ),
    inference(backward_demodulation,[],[f296,f1105])).

fof(f1105,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_65 ),
    inference(forward_demodulation,[],[f1097,f42])).

fof(f42,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f1097,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k1_xboole_0) = k4_xboole_0(X4,k4_xboole_0(X5,X4))
    | ~ spl4_12
    | ~ spl4_65 ),
    inference(superposition,[],[f82,f1044])).

fof(f1044,plain,
    ( ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f82,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f296,plain,
    ( ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f295])).

fof(f1049,plain,
    ( spl4_66
    | ~ spl4_12
    | ~ spl4_22
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f293,f268,f162,f81,f1047])).

fof(f162,plain,
    ( spl4_22
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f293,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))
    | ~ spl4_12
    | ~ spl4_22
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f284,f82])).

fof(f284,plain,
    ( ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ spl4_22
    | ~ spl4_32 ),
    inference(superposition,[],[f163,f269])).

fof(f163,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f162])).

fof(f1045,plain,
    ( spl4_65
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f832,f810,f65,f57,f1043])).

fof(f57,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK2(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f65,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f810,plain,
    ( spl4_57
  <=> ! [X5,X4,X6] :
        ( ~ r2_hidden(sK2(X4,X5),k4_xboole_0(X6,X4))
        | k1_xboole_0 = k3_xboole_0(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f832,plain,
    ( ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f817,f66])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f817,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))
        | r1_xboole_0(X0,k4_xboole_0(X1,X0)) )
    | ~ spl4_6
    | ~ spl4_57 ),
    inference(resolution,[],[f811,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f811,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_hidden(sK2(X4,X5),k4_xboole_0(X6,X4))
        | k1_xboole_0 = k3_xboole_0(X4,X5) )
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f810])).

fof(f812,plain,
    ( spl4_57
    | ~ spl4_8
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f214,f210,f65,f810])).

fof(f210,plain,
    ( spl4_26
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK2(X0,X1),k4_xboole_0(X2,X0))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f214,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_hidden(sK2(X4,X5),k4_xboole_0(X6,X4))
        | k1_xboole_0 = k3_xboole_0(X4,X5) )
    | ~ spl4_8
    | ~ spl4_26 ),
    inference(resolution,[],[f211,f66])).

fof(f211,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,X1)
        | ~ r2_hidden(sK2(X0,X1),k4_xboole_0(X2,X0)) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f210])).

fof(f297,plain,
    ( spl4_34
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f100,f85,f77,f295])).

fof(f77,plain,
    ( spl4_11
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f85,plain,
    ( spl4_13
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f100,plain,
    ( ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(superposition,[],[f86,f78])).

fof(f78,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f86,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f270,plain,
    ( spl4_32
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f97,f81,f77,f49,f45,f268])).

fof(f45,plain,
    ( spl4_3
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f49,plain,
    ( spl4_4
  <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f97,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f96,f50])).

fof(f50,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f96,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f95,f46])).

fof(f46,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f95,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(superposition,[],[f78,f82])).

fof(f212,plain,
    ( spl4_26
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f92,f69,f53,f210])).

fof(f53,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | r2_hidden(sK2(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f69,plain,
    ( spl4_9
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f92,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK2(X0,X1),k4_xboole_0(X2,X0))
        | r1_xboole_0(X0,X1) )
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(resolution,[],[f70,f54])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f70,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f164,plain,
    ( spl4_22
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f98,f85,f45,f162])).

fof(f98,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(superposition,[],[f86,f46])).

fof(f87,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f21,f85])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f83,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f20,f81])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f79,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f19,f77])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f71,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f34,f69])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f67,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f59,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f55,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f18,f49])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f47,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f17,f45])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f43,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f16,f41])).

fof(f16,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f39,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f15,f37])).

fof(f15,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:30:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (12697)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.46  % (12707)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (12710)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.46  % (12707)Refutation not found, incomplete strategy% (12707)------------------------------
% 0.20/0.46  % (12707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (12707)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (12707)Memory used [KB]: 1535
% 0.20/0.46  % (12707)Time elapsed: 0.061 s
% 0.20/0.46  % (12707)------------------------------
% 0.20/0.46  % (12707)------------------------------
% 0.20/0.46  % (12698)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (12694)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (12696)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (12693)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (12693)Refutation not found, incomplete strategy% (12693)------------------------------
% 0.20/0.47  % (12693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (12693)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (12693)Memory used [KB]: 6140
% 0.20/0.47  % (12693)Time elapsed: 0.077 s
% 0.20/0.47  % (12693)------------------------------
% 0.20/0.47  % (12693)------------------------------
% 0.20/0.47  % (12708)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (12695)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (12699)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (12709)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (12709)Refutation not found, incomplete strategy% (12709)------------------------------
% 0.20/0.47  % (12709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (12709)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (12709)Memory used [KB]: 6140
% 0.20/0.47  % (12709)Time elapsed: 0.039 s
% 0.20/0.47  % (12709)------------------------------
% 0.20/0.47  % (12709)------------------------------
% 0.20/0.48  % (12712)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % (12700)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (12704)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (12713)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.48  % (12701)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (12704)Refutation not found, incomplete strategy% (12704)------------------------------
% 0.20/0.48  % (12704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (12704)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (12704)Memory used [KB]: 10618
% 0.20/0.48  % (12704)Time elapsed: 0.087 s
% 0.20/0.48  % (12704)------------------------------
% 0.20/0.48  % (12704)------------------------------
% 0.20/0.48  % (12696)Refutation not found, incomplete strategy% (12696)------------------------------
% 0.20/0.48  % (12696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (12696)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (12696)Memory used [KB]: 10618
% 0.20/0.48  % (12696)Time elapsed: 0.081 s
% 0.20/0.48  % (12696)------------------------------
% 0.20/0.48  % (12696)------------------------------
% 0.20/0.48  % (12694)Refutation not found, incomplete strategy% (12694)------------------------------
% 0.20/0.48  % (12694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (12694)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (12694)Memory used [KB]: 10490
% 0.20/0.48  % (12694)Time elapsed: 0.079 s
% 0.20/0.48  % (12694)------------------------------
% 0.20/0.48  % (12694)------------------------------
% 0.20/0.49  % (12714)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % (12706)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (12706)Refutation not found, incomplete strategy% (12706)------------------------------
% 0.20/0.49  % (12706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (12706)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (12706)Memory used [KB]: 6012
% 0.20/0.49  % (12706)Time elapsed: 0.001 s
% 0.20/0.49  % (12706)------------------------------
% 0.20/0.49  % (12706)------------------------------
% 0.20/0.49  % (12703)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (12703)Refutation not found, incomplete strategy% (12703)------------------------------
% 0.20/0.49  % (12703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (12703)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (12703)Memory used [KB]: 6012
% 0.20/0.49  % (12703)Time elapsed: 0.097 s
% 0.20/0.49  % (12703)------------------------------
% 0.20/0.49  % (12703)------------------------------
% 0.20/0.49  % (12715)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (12702)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (12715)Refutation not found, incomplete strategy% (12715)------------------------------
% 0.20/0.49  % (12715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (12715)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (12715)Memory used [KB]: 10490
% 0.20/0.49  % (12715)Time elapsed: 0.098 s
% 0.20/0.49  % (12715)------------------------------
% 0.20/0.49  % (12715)------------------------------
% 0.20/0.52  % (12702)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f1330,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f39,f43,f47,f51,f55,f59,f67,f71,f79,f83,f87,f164,f212,f270,f297,f812,f1045,f1049,f1125,f1233,f1286])).
% 0.20/0.53  fof(f1286,plain,(
% 0.20/0.53    spl4_1 | ~spl4_69),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f1248])).
% 0.20/0.53  fof(f1248,plain,(
% 0.20/0.53    $false | (spl4_1 | ~spl4_69)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f38,f1232])).
% 0.20/0.53  fof(f1232,plain,(
% 0.20/0.53    ( ! [X26,X27] : (k3_xboole_0(X26,X27) = k4_xboole_0(X26,k4_xboole_0(X26,X27))) ) | ~spl4_69),
% 0.20/0.53    inference(avatar_component_clause,[],[f1231])).
% 0.20/0.53  fof(f1231,plain,(
% 0.20/0.53    spl4_69 <=> ! [X27,X26] : k3_xboole_0(X26,X27) = k4_xboole_0(X26,k4_xboole_0(X26,X27))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl4_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    spl4_1 <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.53  fof(f1233,plain,(
% 0.20/0.53    spl4_69 | ~spl4_32 | ~spl4_66 | ~spl4_67),
% 0.20/0.53    inference(avatar_split_clause,[],[f1185,f1123,f1047,f268,f1231])).
% 0.20/0.53  fof(f268,plain,(
% 0.20/0.53    spl4_32 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.20/0.53  fof(f1047,plain,(
% 0.20/0.53    spl4_66 <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 0.20/0.53  fof(f1123,plain,(
% 0.20/0.53    spl4_67 <=> ! [X7,X6] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 0.20/0.53  fof(f1185,plain,(
% 0.20/0.53    ( ! [X26,X27] : (k3_xboole_0(X26,X27) = k4_xboole_0(X26,k4_xboole_0(X26,X27))) ) | (~spl4_32 | ~spl4_66 | ~spl4_67)),
% 0.20/0.53    inference(forward_demodulation,[],[f1144,f1048])).
% 0.20/0.53  fof(f1048,plain,(
% 0.20/0.53    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))) ) | ~spl4_66),
% 0.20/0.53    inference(avatar_component_clause,[],[f1047])).
% 0.20/0.53  fof(f1144,plain,(
% 0.20/0.53    ( ! [X26,X27] : (k3_xboole_0(X26,X27) = k4_xboole_0(X26,k4_xboole_0(k4_xboole_0(X26,X27),k3_xboole_0(X26,X27)))) ) | (~spl4_32 | ~spl4_67)),
% 0.20/0.53    inference(superposition,[],[f1124,f269])).
% 0.20/0.53  fof(f269,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl4_32),
% 0.20/0.53    inference(avatar_component_clause,[],[f268])).
% 0.20/0.55  fof(f1124,plain,(
% 0.20/0.55    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6) ) | ~spl4_67),
% 0.20/0.55    inference(avatar_component_clause,[],[f1123])).
% 0.20/0.55  fof(f1125,plain,(
% 0.20/0.55    spl4_67 | ~spl4_2 | ~spl4_12 | ~spl4_34 | ~spl4_65),
% 0.20/0.55    inference(avatar_split_clause,[],[f1106,f1043,f295,f81,f41,f1123])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    spl4_2 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    spl4_12 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.55  fof(f295,plain,(
% 0.20/0.55    spl4_34 <=> ! [X7,X6] : k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.20/0.55  fof(f1043,plain,(
% 0.20/0.55    spl4_65 <=> ! [X1,X0] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 0.20/0.55  fof(f1106,plain,(
% 0.20/0.55    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6)) = X6) ) | (~spl4_2 | ~spl4_12 | ~spl4_34 | ~spl4_65)),
% 0.20/0.55    inference(backward_demodulation,[],[f296,f1105])).
% 0.20/0.55  fof(f1105,plain,(
% 0.20/0.55    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4) ) | (~spl4_2 | ~spl4_12 | ~spl4_65)),
% 0.20/0.55    inference(forward_demodulation,[],[f1097,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f41])).
% 0.20/0.55  fof(f1097,plain,(
% 0.20/0.55    ( ! [X4,X5] : (k4_xboole_0(X4,k1_xboole_0) = k4_xboole_0(X4,k4_xboole_0(X5,X4))) ) | (~spl4_12 | ~spl4_65)),
% 0.20/0.55    inference(superposition,[],[f82,f1044])).
% 0.20/0.55  fof(f1044,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl4_65),
% 0.20/0.55    inference(avatar_component_clause,[],[f1043])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl4_12),
% 0.20/0.55    inference(avatar_component_clause,[],[f81])).
% 0.20/0.55  fof(f296,plain,(
% 0.20/0.55    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))) ) | ~spl4_34),
% 0.20/0.55    inference(avatar_component_clause,[],[f295])).
% 0.20/0.55  fof(f1049,plain,(
% 0.20/0.55    spl4_66 | ~spl4_12 | ~spl4_22 | ~spl4_32),
% 0.20/0.55    inference(avatar_split_clause,[],[f293,f268,f162,f81,f1047])).
% 0.20/0.55  fof(f162,plain,(
% 0.20/0.55    spl4_22 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.55  fof(f293,plain,(
% 0.20/0.55    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))) ) | (~spl4_12 | ~spl4_22 | ~spl4_32)),
% 0.20/0.55    inference(forward_demodulation,[],[f284,f82])).
% 0.20/0.55  fof(f284,plain,(
% 0.20/0.55    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3))) ) | (~spl4_22 | ~spl4_32)),
% 0.20/0.55    inference(superposition,[],[f163,f269])).
% 0.20/0.55  fof(f163,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) ) | ~spl4_22),
% 0.20/0.55    inference(avatar_component_clause,[],[f162])).
% 0.20/0.55  fof(f1045,plain,(
% 0.20/0.55    spl4_65 | ~spl4_6 | ~spl4_8 | ~spl4_57),
% 0.20/0.55    inference(avatar_split_clause,[],[f832,f810,f65,f57,f1043])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    spl4_6 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    spl4_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.55  fof(f810,plain,(
% 0.20/0.55    spl4_57 <=> ! [X5,X4,X6] : (~r2_hidden(sK2(X4,X5),k4_xboole_0(X6,X4)) | k1_xboole_0 = k3_xboole_0(X4,X5))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.20/0.55  fof(f832,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) ) | (~spl4_6 | ~spl4_8 | ~spl4_57)),
% 0.20/0.55    inference(subsumption_resolution,[],[f817,f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl4_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f65])).
% 0.20/0.55  fof(f817,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) | r1_xboole_0(X0,k4_xboole_0(X1,X0))) ) | (~spl4_6 | ~spl4_57)),
% 0.20/0.55    inference(resolution,[],[f811,f58])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) ) | ~spl4_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f57])).
% 0.20/0.55  fof(f811,plain,(
% 0.20/0.55    ( ! [X6,X4,X5] : (~r2_hidden(sK2(X4,X5),k4_xboole_0(X6,X4)) | k1_xboole_0 = k3_xboole_0(X4,X5)) ) | ~spl4_57),
% 0.20/0.55    inference(avatar_component_clause,[],[f810])).
% 0.20/0.55  fof(f812,plain,(
% 0.20/0.55    spl4_57 | ~spl4_8 | ~spl4_26),
% 0.20/0.55    inference(avatar_split_clause,[],[f214,f210,f65,f810])).
% 0.20/0.55  fof(f210,plain,(
% 0.20/0.55    spl4_26 <=> ! [X1,X0,X2] : (~r2_hidden(sK2(X0,X1),k4_xboole_0(X2,X0)) | r1_xboole_0(X0,X1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.55  fof(f214,plain,(
% 0.20/0.55    ( ! [X6,X4,X5] : (~r2_hidden(sK2(X4,X5),k4_xboole_0(X6,X4)) | k1_xboole_0 = k3_xboole_0(X4,X5)) ) | (~spl4_8 | ~spl4_26)),
% 0.20/0.55    inference(resolution,[],[f211,f66])).
% 0.20/0.55  fof(f211,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X1) | ~r2_hidden(sK2(X0,X1),k4_xboole_0(X2,X0))) ) | ~spl4_26),
% 0.20/0.55    inference(avatar_component_clause,[],[f210])).
% 0.20/0.55  fof(f297,plain,(
% 0.20/0.55    spl4_34 | ~spl4_11 | ~spl4_13),
% 0.20/0.55    inference(avatar_split_clause,[],[f100,f85,f77,f295])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    spl4_11 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    spl4_13 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X7,X6)) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X7,X6))) ) | (~spl4_11 | ~spl4_13)),
% 0.20/0.55    inference(superposition,[],[f86,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl4_11),
% 0.20/0.55    inference(avatar_component_clause,[],[f77])).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) ) | ~spl4_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f85])).
% 0.20/0.55  fof(f270,plain,(
% 0.20/0.55    spl4_32 | ~spl4_3 | ~spl4_4 | ~spl4_11 | ~spl4_12),
% 0.20/0.55    inference(avatar_split_clause,[],[f97,f81,f77,f49,f45,f268])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    spl4_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    spl4_4 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | (~spl4_3 | ~spl4_4 | ~spl4_11 | ~spl4_12)),
% 0.20/0.55    inference(forward_demodulation,[],[f96,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl4_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f49])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | (~spl4_3 | ~spl4_11 | ~spl4_12)),
% 0.20/0.55    inference(forward_demodulation,[],[f95,f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl4_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f45])).
% 0.20/0.55  fof(f95,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | (~spl4_11 | ~spl4_12)),
% 0.20/0.55    inference(superposition,[],[f78,f82])).
% 0.20/0.55  fof(f212,plain,(
% 0.20/0.55    spl4_26 | ~spl4_5 | ~spl4_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f92,f69,f53,f210])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    spl4_5 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    spl4_9 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1),k4_xboole_0(X2,X0)) | r1_xboole_0(X0,X1)) ) | (~spl4_5 | ~spl4_9)),
% 0.20/0.55    inference(resolution,[],[f70,f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) ) | ~spl4_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f53])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) ) | ~spl4_9),
% 0.20/0.55    inference(avatar_component_clause,[],[f69])).
% 0.20/0.55  fof(f164,plain,(
% 0.20/0.55    spl4_22 | ~spl4_3 | ~spl4_13),
% 0.20/0.55    inference(avatar_split_clause,[],[f98,f85,f45,f162])).
% 0.20/0.55  fof(f98,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) ) | (~spl4_3 | ~spl4_13)),
% 0.20/0.55    inference(superposition,[],[f86,f46])).
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    spl4_13),
% 0.20/0.55    inference(avatar_split_clause,[],[f21,f85])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    spl4_12),
% 0.20/0.55    inference(avatar_split_clause,[],[f20,f81])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    spl4_11),
% 0.20/0.55    inference(avatar_split_clause,[],[f19,f77])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    spl4_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f34,f69])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(equality_resolution,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    spl4_8),
% 0.20/0.55    inference(avatar_split_clause,[],[f26,f65])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    spl4_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f24,f57])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.55    inference(rectify,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    spl4_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f23,f53])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f14])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    spl4_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f18,f49])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    spl4_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f17,f45])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    spl4_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f16,f41])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ~spl4_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f15,f37])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.55    inference(negated_conjecture,[],[f10])).
% 0.20/0.55  fof(f10,conjecture,(
% 0.20/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (12702)------------------------------
% 0.20/0.55  % (12702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12702)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (12702)Memory used [KB]: 11513
% 0.20/0.55  % (12702)Time elapsed: 0.101 s
% 0.20/0.55  % (12702)------------------------------
% 0.20/0.55  % (12702)------------------------------
% 0.20/0.55  % (12689)Success in time 0.2 s
%------------------------------------------------------------------------------
