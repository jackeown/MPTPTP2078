%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 286 expanded)
%              Number of leaves         :   45 ( 141 expanded)
%              Depth                    :    7
%              Number of atoms          :  408 ( 697 expanded)
%              Number of equality atoms :  102 ( 204 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3008,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f53,f57,f61,f65,f69,f73,f77,f81,f87,f95,f125,f130,f134,f138,f198,f224,f269,f276,f407,f492,f788,f862,f937,f1042,f1216,f1332,f1338,f2160,f2968,f3004])).

fof(f3004,plain,
    ( ~ spl3_15
    | spl3_34
    | ~ spl3_53
    | ~ spl3_83
    | ~ spl3_103 ),
    inference(avatar_contradiction_clause,[],[f3003])).

fof(f3003,plain,
    ( $false
    | ~ spl3_15
    | spl3_34
    | ~ spl3_53
    | ~ spl3_83
    | ~ spl3_103 ),
    inference(subsumption_resolution,[],[f406,f3002])).

fof(f3002,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl3_15
    | ~ spl3_53
    | ~ spl3_83
    | ~ spl3_103 ),
    inference(forward_demodulation,[],[f3001,f2159])).

fof(f2159,plain,
    ( ! [X51] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X51,sK2))
    | ~ spl3_83 ),
    inference(avatar_component_clause,[],[f2158])).

fof(f2158,plain,
    ( spl3_83
  <=> ! [X51] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X51,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f3001,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_15
    | ~ spl3_53
    | ~ spl3_103 ),
    inference(forward_demodulation,[],[f2971,f124])).

fof(f124,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f2971,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | ~ spl3_53
    | ~ spl3_103 ),
    inference(unit_resulting_resolution,[],[f936,f2967])).

fof(f2967,plain,
    ( ! [X4,X3] :
        ( r1_tarski(X3,k4_xboole_0(X3,X4))
        | ~ r1_xboole_0(X3,X4) )
    | ~ spl3_103 ),
    inference(avatar_component_clause,[],[f2966])).

fof(f2966,plain,
    ( spl3_103
  <=> ! [X3,X4] :
        ( r1_tarski(X3,k4_xboole_0(X3,X4))
        | ~ r1_xboole_0(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).

fof(f936,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f934])).

fof(f934,plain,
    ( spl3_53
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f406,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | spl3_34 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl3_34
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f2968,plain,
    ( spl3_103
    | ~ spl3_8
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f506,f490,f67,f2966])).

fof(f67,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f490,plain,
    ( spl3_39
  <=> ! [X5,X4] :
        ( k1_xboole_0 != k3_xboole_0(X4,X5)
        | r1_tarski(X4,k4_xboole_0(X4,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f506,plain,
    ( ! [X4,X3] :
        ( r1_tarski(X3,k4_xboole_0(X3,X4))
        | ~ r1_xboole_0(X3,X4) )
    | ~ spl3_8
    | ~ spl3_39 ),
    inference(trivial_inequality_removal,[],[f501])).

fof(f501,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(X3,k4_xboole_0(X3,X4))
        | ~ r1_xboole_0(X3,X4) )
    | ~ spl3_8
    | ~ spl3_39 ),
    inference(superposition,[],[f491,f68])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f491,plain,
    ( ! [X4,X5] :
        ( k1_xboole_0 != k3_xboole_0(X4,X5)
        | r1_tarski(X4,k4_xboole_0(X4,X5)) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f490])).

fof(f2160,plain,
    ( spl3_83
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_17
    | ~ spl3_19
    | ~ spl3_28
    | ~ spl3_58
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f1403,f1336,f1214,f274,f195,f132,f79,f59,f2158])).

fof(f59,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f79,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f132,plain,
    ( spl3_17
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f195,plain,
    ( spl3_19
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f274,plain,
    ( spl3_28
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f1214,plain,
    ( spl3_58
  <=> ! [X3,X2,X4] : k3_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f1336,plain,
    ( spl3_60
  <=> ! [X9,X8,X10] : k3_xboole_0(k4_xboole_0(X8,X9),X10) = k3_xboole_0(X8,k4_xboole_0(X10,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f1403,plain,
    ( ! [X51] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X51,sK2))
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_17
    | ~ spl3_19
    | ~ spl3_28
    | ~ spl3_58
    | ~ spl3_60 ),
    inference(forward_demodulation,[],[f1354,f1267])).

fof(f1267,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_17
    | ~ spl3_28
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f1217,f290])).

fof(f290,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_17
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f281,f106])).

fof(f106,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f60,f80])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f60,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f281,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1)
    | ~ spl3_17
    | ~ spl3_28 ),
    inference(superposition,[],[f133,f275])).

fof(f275,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f274])).

fof(f133,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f132])).

fof(f1217,plain,
    ( ! [X0,X1] : k3_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))
    | ~ spl3_28
    | ~ spl3_58 ),
    inference(superposition,[],[f1215,f275])).

fof(f1215,plain,
    ( ! [X4,X2,X3] : k3_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4)))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f1214])).

fof(f1354,plain,
    ( ! [X51] : k3_xboole_0(k1_xboole_0,X51) = k3_xboole_0(sK0,k4_xboole_0(X51,sK2))
    | ~ spl3_19
    | ~ spl3_60 ),
    inference(superposition,[],[f1337,f197])).

fof(f197,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f195])).

fof(f1337,plain,
    ( ! [X10,X8,X9] : k3_xboole_0(k4_xboole_0(X8,X9),X10) = k3_xboole_0(X8,k4_xboole_0(X10,X9))
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f1336])).

fof(f1338,plain,
    ( spl3_60
    | ~ spl3_7
    | ~ spl3_51
    | ~ spl3_56
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f1334,f1330,f1040,f860,f63,f1336])).

fof(f63,plain,
    ( spl3_7
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f860,plain,
    ( spl3_51
  <=> ! [X5,X7,X6] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f1040,plain,
    ( spl3_56
  <=> ! [X5,X7,X6] : k3_xboole_0(X5,k4_xboole_0(X6,X7)) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f1330,plain,
    ( spl3_59
  <=> ! [X9,X8,X10] : k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,k2_xboole_0(X9,X10)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f1334,plain,
    ( ! [X10,X8,X9] : k3_xboole_0(k4_xboole_0(X8,X9),X10) = k3_xboole_0(X8,k4_xboole_0(X10,X9))
    | ~ spl3_7
    | ~ spl3_51
    | ~ spl3_56
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f1333,f1059])).

fof(f1059,plain,
    ( ! [X6,X7,X5] : k3_xboole_0(X5,k4_xboole_0(X6,X7)) = k4_xboole_0(X5,k2_xboole_0(X7,k4_xboole_0(X5,X6)))
    | ~ spl3_7
    | ~ spl3_56 ),
    inference(superposition,[],[f1041,f64])).

fof(f64,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f1041,plain,
    ( ! [X6,X7,X5] : k3_xboole_0(X5,k4_xboole_0(X6,X7)) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7))
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f1040])).

fof(f1333,plain,
    ( ! [X10,X8,X9] : k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X10)))
    | ~ spl3_7
    | ~ spl3_51
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f1331,f864])).

fof(f864,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(X4,k4_xboole_0(X5,X3)) = k2_xboole_0(X4,k4_xboole_0(X5,k2_xboole_0(X4,X3)))
    | ~ spl3_7
    | ~ spl3_51 ),
    inference(superposition,[],[f861,f64])).

fof(f861,plain,
    ( ! [X6,X7,X5] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f860])).

fof(f1331,plain,
    ( ! [X10,X8,X9] : k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,k2_xboole_0(X9,X10))))
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f1330])).

fof(f1332,plain,
    ( spl3_59
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f174,f132,f93,f1330])).

fof(f93,plain,
    ( spl3_14
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f174,plain,
    ( ! [X10,X8,X9] : k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,k2_xboole_0(X9,X10))))
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f162,f133])).

fof(f162,plain,
    ( ! [X10,X8,X9] : k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(k4_xboole_0(X8,X9),X10)))
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(superposition,[],[f133,f94])).

fof(f94,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f93])).

fof(f1216,plain,
    ( spl3_58
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f164,f132,f93,f1214])).

fof(f164,plain,
    ( ! [X4,X2,X3] : k3_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4)))
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(superposition,[],[f94,f133])).

fof(f1042,plain,
    ( spl3_56
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f169,f132,f123,f93,f1040])).

fof(f169,plain,
    ( ! [X6,X7,X5] : k3_xboole_0(X5,k4_xboole_0(X6,X7)) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7))
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f157,f124])).

fof(f157,plain,
    ( ! [X6,X7,X5] : k4_xboole_0(k3_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7))
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(superposition,[],[f133,f94])).

fof(f937,plain,
    ( spl3_53
    | ~ spl3_22
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f789,f786,f221,f934])).

fof(f221,plain,
    ( spl3_22
  <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f786,plain,
    ( spl3_49
  <=> ! [X7,X8,X6] :
        ( k1_xboole_0 != k3_xboole_0(X6,k3_xboole_0(X7,X8))
        | r1_xboole_0(k3_xboole_0(X6,X7),X8) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f789,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl3_22
    | ~ spl3_49 ),
    inference(unit_resulting_resolution,[],[f223,f787])).

fof(f787,plain,
    ( ! [X6,X8,X7] :
        ( k1_xboole_0 != k3_xboole_0(X6,k3_xboole_0(X7,X8))
        | r1_xboole_0(k3_xboole_0(X6,X7),X8) )
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f786])).

fof(f223,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f221])).

fof(f862,plain,
    ( spl3_51
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f165,f132,f85,f860])).

fof(f85,plain,
    ( spl3_12
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f165,plain,
    ( ! [X6,X7,X5] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(superposition,[],[f86,f133])).

fof(f86,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f788,plain,
    ( spl3_49
    | ~ spl3_9
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f183,f136,f71,f786])).

fof(f71,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f136,plain,
    ( spl3_18
  <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f183,plain,
    ( ! [X6,X8,X7] :
        ( k1_xboole_0 != k3_xboole_0(X6,k3_xboole_0(X7,X8))
        | r1_xboole_0(k3_xboole_0(X6,X7),X8) )
    | ~ spl3_9
    | ~ spl3_18 ),
    inference(superposition,[],[f72,f137])).

fof(f137,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f136])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f492,plain,
    ( spl3_39
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f118,f93,f75,f490])).

fof(f75,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f118,plain,
    ( ! [X4,X5] :
        ( k1_xboole_0 != k3_xboole_0(X4,X5)
        | r1_tarski(X4,k4_xboole_0(X4,X5)) )
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(superposition,[],[f76,f94])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k4_xboole_0(X0,X1)
        | r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f407,plain,
    ( ~ spl3_34
    | spl3_16
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f270,f267,f127,f404])).

fof(f127,plain,
    ( spl3_16
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f267,plain,
    ( spl3_27
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f270,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | spl3_16
    | ~ spl3_27 ),
    inference(unit_resulting_resolution,[],[f129,f268])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f267])).

fof(f129,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f127])).

fof(f276,plain,
    ( spl3_28
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f119,f93,f55,f51,f274])).

fof(f51,plain,
    ( spl3_4
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f55,plain,
    ( spl3_5
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f119,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f112,f52])).

fof(f52,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f112,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(superposition,[],[f94,f56])).

fof(f56,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f269,plain,
    ( spl3_27
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f107,f79,f55,f267])).

fof(f107,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(superposition,[],[f80,f56])).

fof(f224,plain,
    ( spl3_22
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f96,f67,f46,f221])).

fof(f46,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f96,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f48,f68])).

fof(f48,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f198,plain,
    ( spl3_19
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f105,f79,f41,f195])).

fof(f41,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f105,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f43,f80])).

fof(f43,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f138,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f34,f136])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f134,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f33,f132])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f130,plain,
    ( ~ spl3_16
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f98,f71,f36,f127])).

fof(f36,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f98,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl3_1
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f38,f72])).

fof(f38,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f125,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f32,f123])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f95,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f27,f93])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f87,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f26,f85])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f81,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f31,f79])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f77,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f30,f75])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f69,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f25,f63])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f61,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f24,f59])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f57,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f53,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f46])).

fof(f21,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f44,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f36])).

fof(f19,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:50:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.42  % (9186)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.42  % (9185)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.44  % (9188)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.44  % (9192)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.45  % (9182)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.45  % (9191)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.45  % (9196)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (9184)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (9197)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (9183)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (9187)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (9190)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (9189)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (9199)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (9195)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (9194)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (9193)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (9198)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.56  % (9187)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f3008,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f39,f44,f49,f53,f57,f61,f65,f69,f73,f77,f81,f87,f95,f125,f130,f134,f138,f198,f224,f269,f276,f407,f492,f788,f862,f937,f1042,f1216,f1332,f1338,f2160,f2968,f3004])).
% 0.20/0.57  fof(f3004,plain,(
% 0.20/0.57    ~spl3_15 | spl3_34 | ~spl3_53 | ~spl3_83 | ~spl3_103),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f3003])).
% 0.20/0.57  fof(f3003,plain,(
% 0.20/0.57    $false | (~spl3_15 | spl3_34 | ~spl3_53 | ~spl3_83 | ~spl3_103)),
% 0.20/0.57    inference(subsumption_resolution,[],[f406,f3002])).
% 0.20/0.57  fof(f3002,plain,(
% 0.20/0.57    r1_tarski(k3_xboole_0(sK0,sK1),k1_xboole_0) | (~spl3_15 | ~spl3_53 | ~spl3_83 | ~spl3_103)),
% 0.20/0.57    inference(forward_demodulation,[],[f3001,f2159])).
% 0.20/0.57  fof(f2159,plain,(
% 0.20/0.57    ( ! [X51] : (k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X51,sK2))) ) | ~spl3_83),
% 0.20/0.57    inference(avatar_component_clause,[],[f2158])).
% 0.20/0.57  fof(f2158,plain,(
% 0.20/0.57    spl3_83 <=> ! [X51] : k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X51,sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 0.20/0.57  fof(f3001,plain,(
% 0.20/0.57    r1_tarski(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | (~spl3_15 | ~spl3_53 | ~spl3_103)),
% 0.20/0.57    inference(forward_demodulation,[],[f2971,f124])).
% 0.20/0.57  fof(f124,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl3_15),
% 0.20/0.57    inference(avatar_component_clause,[],[f123])).
% 0.20/0.57  fof(f123,plain,(
% 0.20/0.57    spl3_15 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.57  fof(f2971,plain,(
% 0.20/0.57    r1_tarski(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)) | (~spl3_53 | ~spl3_103)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f936,f2967])).
% 0.20/0.57  fof(f2967,plain,(
% 0.20/0.57    ( ! [X4,X3] : (r1_tarski(X3,k4_xboole_0(X3,X4)) | ~r1_xboole_0(X3,X4)) ) | ~spl3_103),
% 0.20/0.57    inference(avatar_component_clause,[],[f2966])).
% 0.20/0.57  fof(f2966,plain,(
% 0.20/0.57    spl3_103 <=> ! [X3,X4] : (r1_tarski(X3,k4_xboole_0(X3,X4)) | ~r1_xboole_0(X3,X4))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).
% 0.20/0.57  fof(f936,plain,(
% 0.20/0.57    r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | ~spl3_53),
% 0.20/0.57    inference(avatar_component_clause,[],[f934])).
% 0.20/0.57  fof(f934,plain,(
% 0.20/0.57    spl3_53 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.20/0.57  fof(f406,plain,(
% 0.20/0.57    ~r1_tarski(k3_xboole_0(sK0,sK1),k1_xboole_0) | spl3_34),
% 0.20/0.57    inference(avatar_component_clause,[],[f404])).
% 0.20/0.57  fof(f404,plain,(
% 0.20/0.57    spl3_34 <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.57  fof(f2968,plain,(
% 0.20/0.57    spl3_103 | ~spl3_8 | ~spl3_39),
% 0.20/0.57    inference(avatar_split_clause,[],[f506,f490,f67,f2966])).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    spl3_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.57  fof(f490,plain,(
% 0.20/0.57    spl3_39 <=> ! [X5,X4] : (k1_xboole_0 != k3_xboole_0(X4,X5) | r1_tarski(X4,k4_xboole_0(X4,X5)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.20/0.57  fof(f506,plain,(
% 0.20/0.57    ( ! [X4,X3] : (r1_tarski(X3,k4_xboole_0(X3,X4)) | ~r1_xboole_0(X3,X4)) ) | (~spl3_8 | ~spl3_39)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f501])).
% 0.20/0.57  fof(f501,plain,(
% 0.20/0.57    ( ! [X4,X3] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X3,k4_xboole_0(X3,X4)) | ~r1_xboole_0(X3,X4)) ) | (~spl3_8 | ~spl3_39)),
% 0.20/0.57    inference(superposition,[],[f491,f68])).
% 0.20/0.57  fof(f68,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_8),
% 0.20/0.57    inference(avatar_component_clause,[],[f67])).
% 0.20/0.57  fof(f491,plain,(
% 0.20/0.57    ( ! [X4,X5] : (k1_xboole_0 != k3_xboole_0(X4,X5) | r1_tarski(X4,k4_xboole_0(X4,X5))) ) | ~spl3_39),
% 0.20/0.57    inference(avatar_component_clause,[],[f490])).
% 0.20/0.57  fof(f2160,plain,(
% 0.20/0.57    spl3_83 | ~spl3_6 | ~spl3_11 | ~spl3_17 | ~spl3_19 | ~spl3_28 | ~spl3_58 | ~spl3_60),
% 0.20/0.57    inference(avatar_split_clause,[],[f1403,f1336,f1214,f274,f195,f132,f79,f59,f2158])).
% 0.20/0.57  fof(f59,plain,(
% 0.20/0.57    spl3_6 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.57  fof(f79,plain,(
% 0.20/0.57    spl3_11 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.57  fof(f132,plain,(
% 0.20/0.57    spl3_17 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.57  fof(f195,plain,(
% 0.20/0.57    spl3_19 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.57  fof(f274,plain,(
% 0.20/0.57    spl3_28 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.57  fof(f1214,plain,(
% 0.20/0.57    spl3_58 <=> ! [X3,X2,X4] : k3_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.20/0.57  fof(f1336,plain,(
% 0.20/0.57    spl3_60 <=> ! [X9,X8,X10] : k3_xboole_0(k4_xboole_0(X8,X9),X10) = k3_xboole_0(X8,k4_xboole_0(X10,X9))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 0.20/0.57  fof(f1403,plain,(
% 0.20/0.57    ( ! [X51] : (k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(X51,sK2))) ) | (~spl3_6 | ~spl3_11 | ~spl3_17 | ~spl3_19 | ~spl3_28 | ~spl3_58 | ~spl3_60)),
% 0.20/0.57    inference(forward_demodulation,[],[f1354,f1267])).
% 0.20/0.57  fof(f1267,plain,(
% 0.20/0.57    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) ) | (~spl3_6 | ~spl3_11 | ~spl3_17 | ~spl3_28 | ~spl3_58)),
% 0.20/0.57    inference(forward_demodulation,[],[f1217,f290])).
% 0.20/0.57  fof(f290,plain,(
% 0.20/0.57    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) ) | (~spl3_6 | ~spl3_11 | ~spl3_17 | ~spl3_28)),
% 0.20/0.57    inference(forward_demodulation,[],[f281,f106])).
% 0.20/0.57  fof(f106,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | (~spl3_6 | ~spl3_11)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f60,f80])).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) ) | ~spl3_11),
% 0.20/0.57    inference(avatar_component_clause,[],[f79])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_6),
% 0.20/0.57    inference(avatar_component_clause,[],[f59])).
% 0.20/0.57  fof(f281,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1)) ) | (~spl3_17 | ~spl3_28)),
% 0.20/0.57    inference(superposition,[],[f133,f275])).
% 0.20/0.57  fof(f275,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl3_28),
% 0.20/0.57    inference(avatar_component_clause,[],[f274])).
% 0.20/0.57  fof(f133,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_17),
% 0.20/0.57    inference(avatar_component_clause,[],[f132])).
% 0.20/0.57  fof(f1217,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))) ) | (~spl3_28 | ~spl3_58)),
% 0.20/0.57    inference(superposition,[],[f1215,f275])).
% 0.20/0.57  fof(f1215,plain,(
% 0.20/0.57    ( ! [X4,X2,X3] : (k3_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4)))) ) | ~spl3_58),
% 0.20/0.57    inference(avatar_component_clause,[],[f1214])).
% 0.20/0.57  fof(f1354,plain,(
% 0.20/0.57    ( ! [X51] : (k3_xboole_0(k1_xboole_0,X51) = k3_xboole_0(sK0,k4_xboole_0(X51,sK2))) ) | (~spl3_19 | ~spl3_60)),
% 0.20/0.57    inference(superposition,[],[f1337,f197])).
% 0.20/0.57  fof(f197,plain,(
% 0.20/0.57    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl3_19),
% 0.20/0.57    inference(avatar_component_clause,[],[f195])).
% 0.20/0.57  fof(f1337,plain,(
% 0.20/0.57    ( ! [X10,X8,X9] : (k3_xboole_0(k4_xboole_0(X8,X9),X10) = k3_xboole_0(X8,k4_xboole_0(X10,X9))) ) | ~spl3_60),
% 0.20/0.57    inference(avatar_component_clause,[],[f1336])).
% 0.20/0.57  fof(f1338,plain,(
% 0.20/0.57    spl3_60 | ~spl3_7 | ~spl3_51 | ~spl3_56 | ~spl3_59),
% 0.20/0.57    inference(avatar_split_clause,[],[f1334,f1330,f1040,f860,f63,f1336])).
% 0.20/0.57  fof(f63,plain,(
% 0.20/0.57    spl3_7 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.57  fof(f860,plain,(
% 0.20/0.57    spl3_51 <=> ! [X5,X7,X6] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.20/0.57  fof(f1040,plain,(
% 0.20/0.57    spl3_56 <=> ! [X5,X7,X6] : k3_xboole_0(X5,k4_xboole_0(X6,X7)) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.20/0.57  fof(f1330,plain,(
% 0.20/0.57    spl3_59 <=> ! [X9,X8,X10] : k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,k2_xboole_0(X9,X10))))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.20/0.57  fof(f1334,plain,(
% 0.20/0.57    ( ! [X10,X8,X9] : (k3_xboole_0(k4_xboole_0(X8,X9),X10) = k3_xboole_0(X8,k4_xboole_0(X10,X9))) ) | (~spl3_7 | ~spl3_51 | ~spl3_56 | ~spl3_59)),
% 0.20/0.57    inference(forward_demodulation,[],[f1333,f1059])).
% 0.20/0.57  fof(f1059,plain,(
% 0.20/0.57    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k4_xboole_0(X6,X7)) = k4_xboole_0(X5,k2_xboole_0(X7,k4_xboole_0(X5,X6)))) ) | (~spl3_7 | ~spl3_56)),
% 0.20/0.57    inference(superposition,[],[f1041,f64])).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_7),
% 0.20/0.57    inference(avatar_component_clause,[],[f63])).
% 0.20/0.57  fof(f1041,plain,(
% 0.20/0.57    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k4_xboole_0(X6,X7)) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7))) ) | ~spl3_56),
% 0.20/0.57    inference(avatar_component_clause,[],[f1040])).
% 0.20/0.57  fof(f1333,plain,(
% 0.20/0.57    ( ! [X10,X8,X9] : (k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X10)))) ) | (~spl3_7 | ~spl3_51 | ~spl3_59)),
% 0.20/0.57    inference(forward_demodulation,[],[f1331,f864])).
% 0.20/0.57  fof(f864,plain,(
% 0.20/0.57    ( ! [X4,X5,X3] : (k2_xboole_0(X4,k4_xboole_0(X5,X3)) = k2_xboole_0(X4,k4_xboole_0(X5,k2_xboole_0(X4,X3)))) ) | (~spl3_7 | ~spl3_51)),
% 0.20/0.57    inference(superposition,[],[f861,f64])).
% 0.20/0.57  fof(f861,plain,(
% 0.20/0.57    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) ) | ~spl3_51),
% 0.20/0.57    inference(avatar_component_clause,[],[f860])).
% 0.20/0.57  fof(f1331,plain,(
% 0.20/0.57    ( ! [X10,X8,X9] : (k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,k2_xboole_0(X9,X10))))) ) | ~spl3_59),
% 0.20/0.57    inference(avatar_component_clause,[],[f1330])).
% 0.20/0.57  fof(f1332,plain,(
% 0.20/0.57    spl3_59 | ~spl3_14 | ~spl3_17),
% 0.20/0.57    inference(avatar_split_clause,[],[f174,f132,f93,f1330])).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    spl3_14 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.57  fof(f174,plain,(
% 0.20/0.57    ( ! [X10,X8,X9] : (k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,k2_xboole_0(X9,X10))))) ) | (~spl3_14 | ~spl3_17)),
% 0.20/0.57    inference(forward_demodulation,[],[f162,f133])).
% 0.20/0.57  fof(f162,plain,(
% 0.20/0.57    ( ! [X10,X8,X9] : (k3_xboole_0(k4_xboole_0(X8,X9),X10) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(k4_xboole_0(X8,X9),X10)))) ) | (~spl3_14 | ~spl3_17)),
% 0.20/0.57    inference(superposition,[],[f133,f94])).
% 0.20/0.57  fof(f94,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_14),
% 0.20/0.57    inference(avatar_component_clause,[],[f93])).
% 0.20/0.57  fof(f1216,plain,(
% 0.20/0.57    spl3_58 | ~spl3_14 | ~spl3_17),
% 0.20/0.57    inference(avatar_split_clause,[],[f164,f132,f93,f1214])).
% 0.20/0.57  fof(f164,plain,(
% 0.20/0.57    ( ! [X4,X2,X3] : (k3_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4)))) ) | (~spl3_14 | ~spl3_17)),
% 0.20/0.57    inference(superposition,[],[f94,f133])).
% 0.20/0.57  fof(f1042,plain,(
% 0.20/0.57    spl3_56 | ~spl3_14 | ~spl3_15 | ~spl3_17),
% 0.20/0.57    inference(avatar_split_clause,[],[f169,f132,f123,f93,f1040])).
% 0.20/0.57  fof(f169,plain,(
% 0.20/0.57    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k4_xboole_0(X6,X7)) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7))) ) | (~spl3_14 | ~spl3_15 | ~spl3_17)),
% 0.20/0.57    inference(forward_demodulation,[],[f157,f124])).
% 0.20/0.57  fof(f157,plain,(
% 0.20/0.57    ( ! [X6,X7,X5] : (k4_xboole_0(k3_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7))) ) | (~spl3_14 | ~spl3_17)),
% 0.20/0.57    inference(superposition,[],[f133,f94])).
% 0.20/0.57  fof(f937,plain,(
% 0.20/0.57    spl3_53 | ~spl3_22 | ~spl3_49),
% 0.20/0.57    inference(avatar_split_clause,[],[f789,f786,f221,f934])).
% 0.20/0.57  fof(f221,plain,(
% 0.20/0.57    spl3_22 <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.57  fof(f786,plain,(
% 0.20/0.57    spl3_49 <=> ! [X7,X8,X6] : (k1_xboole_0 != k3_xboole_0(X6,k3_xboole_0(X7,X8)) | r1_xboole_0(k3_xboole_0(X6,X7),X8))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.20/0.57  fof(f789,plain,(
% 0.20/0.57    r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | (~spl3_22 | ~spl3_49)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f223,f787])).
% 0.20/0.57  fof(f787,plain,(
% 0.20/0.57    ( ! [X6,X8,X7] : (k1_xboole_0 != k3_xboole_0(X6,k3_xboole_0(X7,X8)) | r1_xboole_0(k3_xboole_0(X6,X7),X8)) ) | ~spl3_49),
% 0.20/0.57    inference(avatar_component_clause,[],[f786])).
% 0.20/0.57  fof(f223,plain,(
% 0.20/0.57    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_22),
% 0.20/0.57    inference(avatar_component_clause,[],[f221])).
% 0.20/0.57  fof(f862,plain,(
% 0.20/0.57    spl3_51 | ~spl3_12 | ~spl3_17),
% 0.20/0.57    inference(avatar_split_clause,[],[f165,f132,f85,f860])).
% 0.20/0.57  fof(f85,plain,(
% 0.20/0.57    spl3_12 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.57  fof(f165,plain,(
% 0.20/0.57    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) ) | (~spl3_12 | ~spl3_17)),
% 0.20/0.57    inference(superposition,[],[f86,f133])).
% 0.20/0.57  fof(f86,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_12),
% 0.20/0.57    inference(avatar_component_clause,[],[f85])).
% 0.20/0.57  fof(f788,plain,(
% 0.20/0.57    spl3_49 | ~spl3_9 | ~spl3_18),
% 0.20/0.57    inference(avatar_split_clause,[],[f183,f136,f71,f786])).
% 0.20/0.57  fof(f71,plain,(
% 0.20/0.57    spl3_9 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.57  fof(f136,plain,(
% 0.20/0.57    spl3_18 <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.57  fof(f183,plain,(
% 0.20/0.57    ( ! [X6,X8,X7] : (k1_xboole_0 != k3_xboole_0(X6,k3_xboole_0(X7,X8)) | r1_xboole_0(k3_xboole_0(X6,X7),X8)) ) | (~spl3_9 | ~spl3_18)),
% 0.20/0.57    inference(superposition,[],[f72,f137])).
% 0.20/0.57  fof(f137,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) ) | ~spl3_18),
% 0.20/0.57    inference(avatar_component_clause,[],[f136])).
% 0.20/0.57  fof(f72,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl3_9),
% 0.20/0.57    inference(avatar_component_clause,[],[f71])).
% 0.20/0.57  fof(f492,plain,(
% 0.20/0.57    spl3_39 | ~spl3_10 | ~spl3_14),
% 0.20/0.57    inference(avatar_split_clause,[],[f118,f93,f75,f490])).
% 0.20/0.57  fof(f75,plain,(
% 0.20/0.57    spl3_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.57  fof(f118,plain,(
% 0.20/0.57    ( ! [X4,X5] : (k1_xboole_0 != k3_xboole_0(X4,X5) | r1_tarski(X4,k4_xboole_0(X4,X5))) ) | (~spl3_10 | ~spl3_14)),
% 0.20/0.57    inference(superposition,[],[f76,f94])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.20/0.57    inference(avatar_component_clause,[],[f75])).
% 0.20/0.57  fof(f407,plain,(
% 0.20/0.57    ~spl3_34 | spl3_16 | ~spl3_27),
% 0.20/0.57    inference(avatar_split_clause,[],[f270,f267,f127,f404])).
% 0.20/0.57  fof(f127,plain,(
% 0.20/0.57    spl3_16 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.57  fof(f267,plain,(
% 0.20/0.57    spl3_27 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.57  fof(f270,plain,(
% 0.20/0.57    ~r1_tarski(k3_xboole_0(sK0,sK1),k1_xboole_0) | (spl3_16 | ~spl3_27)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f129,f268])).
% 0.20/0.57  fof(f268,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl3_27),
% 0.20/0.57    inference(avatar_component_clause,[],[f267])).
% 0.20/0.57  fof(f129,plain,(
% 0.20/0.57    k1_xboole_0 != k3_xboole_0(sK0,sK1) | spl3_16),
% 0.20/0.57    inference(avatar_component_clause,[],[f127])).
% 0.20/0.57  fof(f276,plain,(
% 0.20/0.57    spl3_28 | ~spl3_4 | ~spl3_5 | ~spl3_14),
% 0.20/0.57    inference(avatar_split_clause,[],[f119,f93,f55,f51,f274])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    spl3_4 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    spl3_5 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.57  fof(f119,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl3_4 | ~spl3_5 | ~spl3_14)),
% 0.20/0.57    inference(forward_demodulation,[],[f112,f52])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl3_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f51])).
% 0.20/0.57  fof(f112,plain,(
% 0.20/0.57    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) ) | (~spl3_5 | ~spl3_14)),
% 0.20/0.57    inference(superposition,[],[f94,f56])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f55])).
% 0.20/0.57  fof(f269,plain,(
% 0.20/0.57    spl3_27 | ~spl3_5 | ~spl3_11),
% 0.20/0.57    inference(avatar_split_clause,[],[f107,f79,f55,f267])).
% 0.20/0.57  fof(f107,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) ) | (~spl3_5 | ~spl3_11)),
% 0.20/0.57    inference(superposition,[],[f80,f56])).
% 0.20/0.57  fof(f224,plain,(
% 0.20/0.57    spl3_22 | ~spl3_3 | ~spl3_8),
% 0.20/0.57    inference(avatar_split_clause,[],[f96,f67,f46,f221])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    spl3_3 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.57  fof(f96,plain,(
% 0.20/0.57    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_8)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f48,f68])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f46])).
% 0.20/0.57  fof(f198,plain,(
% 0.20/0.57    spl3_19 | ~spl3_2 | ~spl3_11),
% 0.20/0.57    inference(avatar_split_clause,[],[f105,f79,f41,f195])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    spl3_2 <=> r1_tarski(sK0,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    k1_xboole_0 = k4_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_11)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f43,f80])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    r1_tarski(sK0,sK2) | ~spl3_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f41])).
% 0.20/0.57  fof(f138,plain,(
% 0.20/0.57    spl3_18),
% 0.20/0.57    inference(avatar_split_clause,[],[f34,f136])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.57  fof(f134,plain,(
% 0.20/0.57    spl3_17),
% 0.20/0.57    inference(avatar_split_clause,[],[f33,f132])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.57  fof(f130,plain,(
% 0.20/0.57    ~spl3_16 | spl3_1 | ~spl3_9),
% 0.20/0.57    inference(avatar_split_clause,[],[f98,f71,f36,f127])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.57  fof(f98,plain,(
% 0.20/0.57    k1_xboole_0 != k3_xboole_0(sK0,sK1) | (spl3_1 | ~spl3_9)),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f38,f72])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ~r1_xboole_0(sK0,sK1) | spl3_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f36])).
% 0.20/0.57  fof(f125,plain,(
% 0.20/0.57    spl3_15),
% 0.20/0.57    inference(avatar_split_clause,[],[f32,f123])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.57  fof(f95,plain,(
% 0.20/0.57    spl3_14),
% 0.20/0.57    inference(avatar_split_clause,[],[f27,f93])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.57  fof(f87,plain,(
% 0.20/0.57    spl3_12),
% 0.20/0.57    inference(avatar_split_clause,[],[f26,f85])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.57  fof(f81,plain,(
% 0.20/0.57    spl3_11),
% 0.20/0.57    inference(avatar_split_clause,[],[f31,f79])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.57    inference(nnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.57  fof(f77,plain,(
% 0.20/0.57    spl3_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f30,f75])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f73,plain,(
% 0.20/0.57    spl3_9),
% 0.20/0.57    inference(avatar_split_clause,[],[f29,f71])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(nnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    spl3_8),
% 0.20/0.57    inference(avatar_split_clause,[],[f28,f67])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f17])).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    spl3_7),
% 0.20/0.57    inference(avatar_split_clause,[],[f25,f63])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    spl3_6),
% 0.20/0.57    inference(avatar_split_clause,[],[f24,f59])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    spl3_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f23,f55])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    spl3_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f22,f51])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    spl3_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f21,f46])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f14,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.57    inference(negated_conjecture,[],[f12])).
% 0.20/0.57  fof(f12,conjecture,(
% 0.20/0.57    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    spl3_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f20,f41])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    r1_tarski(sK0,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ~spl3_1),
% 0.20/0.57    inference(avatar_split_clause,[],[f19,f36])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ~r1_xboole_0(sK0,sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (9187)------------------------------
% 0.20/0.57  % (9187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (9187)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (9187)Memory used [KB]: 8443
% 0.20/0.57  % (9187)Time elapsed: 0.152 s
% 0.20/0.57  % (9187)------------------------------
% 0.20/0.57  % (9187)------------------------------
% 0.20/0.57  % (9181)Success in time 0.23 s
%------------------------------------------------------------------------------
