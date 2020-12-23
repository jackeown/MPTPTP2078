%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0497+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:05 EST 2020

% Result     : Theorem 2.37s
% Output     : Refutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  319 (1441 expanded)
%              Number of leaves         :   59 ( 513 expanded)
%              Depth                    :   16
%              Number of atoms          : 1092 (6473 expanded)
%              Number of equality atoms :   99 ( 755 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f100,f158,f168,f179,f180,f187,f197,f205,f248,f313,f334,f385,f393,f400,f468,f473,f483,f485,f531,f562,f580,f628,f640,f662,f676,f713,f728,f781,f783,f785,f787,f789,f791,f798,f801,f807,f810,f813,f821,f832,f855,f901,f932,f954,f971,f1000,f1002,f1004,f1006,f1008,f1014,f1017,f1055,f1058,f1095,f1100,f1130,f1132,f1134,f1136,f1138])).

fof(f1138,plain,
    ( spl9_6
    | ~ spl9_9 ),
    inference(avatar_contradiction_clause,[],[f1137])).

fof(f1137,plain,
    ( $false
    | spl9_6
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f196,f1034])).

fof(f1034,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k1_relat_1(sK1))
    | spl9_6 ),
    inference(resolution,[],[f166,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f166,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(sK1))
    | spl9_6 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl9_6
  <=> r1_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f196,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl9_9
  <=> k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f1136,plain,
    ( spl9_5
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f1135])).

fof(f1135,plain,
    ( $false
    | spl9_5
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f1030,f186])).

fof(f186,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl9_8
  <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f1030,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),sK0)
    | spl9_5 ),
    inference(resolution,[],[f156,f65])).

fof(f156,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl9_5
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f1134,plain,
    ( spl9_5
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f1133])).

fof(f1133,plain,
    ( $false
    | spl9_5
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f1028,f186])).

fof(f1028,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),sK0)
    | spl9_5 ),
    inference(unit_resulting_resolution,[],[f156,f65])).

fof(f1132,plain,
    ( ~ spl9_8
    | spl9_9 ),
    inference(avatar_contradiction_clause,[],[f1131])).

fof(f1131,plain,
    ( $false
    | ~ spl9_8
    | spl9_9 ),
    inference(subsumption_resolution,[],[f186,f1069])).

fof(f1069,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),sK0)
    | spl9_9 ),
    inference(unit_resulting_resolution,[],[f195,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) != k1_xboole_0
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f114,f65])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f64,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f195,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k1_relat_1(sK1))
    | spl9_9 ),
    inference(avatar_component_clause,[],[f194])).

fof(f1130,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_8
    | ~ spl9_38 ),
    inference(avatar_contradiction_clause,[],[f1129])).

fof(f1129,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_8
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f1122,f1044])).

fof(f1044,plain,
    ( r2_hidden(sK8(k1_relat_1(sK1),sK0,k1_xboole_0),k1_relat_1(sK1))
    | ~ spl9_2
    | spl9_8 ),
    inference(unit_resulting_resolution,[],[f103,f185,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X2)
      | r2_hidden(sK8(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(sK8(X0,X1,X2),X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f185,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_relat_1(sK1),sK0)
    | spl9_8 ),
    inference(avatar_component_clause,[],[f184])).

fof(f103,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f93,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f93,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl9_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f1122,plain,
    ( ~ r2_hidden(sK8(k1_relat_1(sK1),sK0,k1_xboole_0),k1_relat_1(sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f1099,f1077])).

fof(f1077,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(resolution,[],[f1064,f81])).

fof(f81,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f37,f40,f39,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1064,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f1063,f88])).

fof(f88,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl9_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f1063,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f1062,f103])).

fof(f1062,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X0,sK0)
        | r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f1059,f99])).

fof(f99,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl9_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f1059,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k1_xboole_0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X0,sK0)
        | r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_4 ),
    inference(superposition,[],[f77,f153])).

fof(f153,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl9_4
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f77,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK2(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
                    & r2_hidden(sK2(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
            & r2_hidden(sK2(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f1099,plain,
    ( r2_hidden(sK8(k1_relat_1(sK1),sK0,k1_xboole_0),sK0)
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f1097])).

fof(f1097,plain,
    ( spl9_38
  <=> r2_hidden(sK8(k1_relat_1(sK1),sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f1100,plain,
    ( spl9_38
    | ~ spl9_2
    | spl9_8 ),
    inference(avatar_split_clause,[],[f1043,f184,f91,f1097])).

fof(f1043,plain,
    ( r2_hidden(sK8(k1_relat_1(sK1),sK0,k1_xboole_0),sK0)
    | ~ spl9_2
    | spl9_8 ),
    inference(unit_resulting_resolution,[],[f103,f185,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X2)
      | r2_hidden(sK8(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1095,plain,
    ( ~ spl9_37
    | ~ spl9_21
    | spl9_30 ),
    inference(avatar_split_clause,[],[f1088,f829,f528,f1092])).

fof(f1092,plain,
    ( spl9_37
  <=> m1_subset_1(sK2(sK1,sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f528,plain,
    ( spl9_21
  <=> r2_hidden(sK4(sK0),k3_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f829,plain,
    ( spl9_30
  <=> r2_hidden(sK2(sK1,sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f1088,plain,
    ( ~ m1_subset_1(sK2(sK1,sK0,k1_xboole_0),sK0)
    | ~ spl9_21
    | spl9_30 ),
    inference(unit_resulting_resolution,[],[f530,f830,f141])).

fof(f141,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_subset_1(X5,X3)
      | r2_hidden(X5,X3)
      | ~ r2_hidden(X2,k3_xboole_0(X3,X4)) ) ),
    inference(resolution,[],[f135,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f84,f70])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f830,plain,
    ( ~ r2_hidden(sK2(sK1,sK0,k1_xboole_0),sK0)
    | spl9_30 ),
    inference(avatar_component_clause,[],[f829])).

fof(f530,plain,
    ( r2_hidden(sK4(sK0),k3_xboole_0(sK0,sK0))
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f528])).

fof(f1058,plain,
    ( spl9_4
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_34 ),
    inference(avatar_split_clause,[],[f990,f951,f97,f91,f86,f151])).

fof(f951,plain,
    ( spl9_34
  <=> r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f990,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_34 ),
    inference(unit_resulting_resolution,[],[f88,f99,f103,f955,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | k7_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f955,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK2(sK1,sK0,k1_xboole_0),X0),sK1)
    | spl9_34 ),
    inference(unit_resulting_resolution,[],[f953,f80])).

fof(f80,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f953,plain,
    ( ~ r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_relat_1(sK1))
    | spl9_34 ),
    inference(avatar_component_clause,[],[f951])).

fof(f1055,plain,
    ( ~ spl9_36
    | spl9_8 ),
    inference(avatar_split_clause,[],[f1047,f184,f1052])).

fof(f1052,plain,
    ( spl9_36
  <=> v1_xboole_0(k3_xboole_0(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f1047,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,k1_relat_1(sK1)))
    | spl9_8 ),
    inference(forward_demodulation,[],[f1039,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1039,plain,
    ( ~ v1_xboole_0(k3_xboole_0(k1_relat_1(sK1),sK0))
    | spl9_8 ),
    inference(unit_resulting_resolution,[],[f185,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f1017,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_13
    | spl9_34 ),
    inference(avatar_contradiction_clause,[],[f1016])).

fof(f1016,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_13
    | spl9_34 ),
    inference(subsumption_resolution,[],[f1015,f103])).

fof(f1015,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_xboole_0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_13
    | spl9_34 ),
    inference(forward_demodulation,[],[f1010,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f1010,plain,
    ( r2_hidden(sK4(k3_xboole_0(k1_xboole_0,k1_xboole_0)),k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_13
    | spl9_34 ),
    inference(backward_demodulation,[],[f336,f990])).

fof(f336,plain,
    ( r2_hidden(sK4(k3_xboole_0(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0))),k3_xboole_0(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0)))
    | spl9_13 ),
    inference(unit_resulting_resolution,[],[f60,f333,f62])).

fof(f333,plain,
    ( ~ v1_xboole_0(k3_xboole_0(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0)))
    | spl9_13 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl9_13
  <=> v1_xboole_0(k3_xboole_0(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f7,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f1014,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_13
    | spl9_34 ),
    inference(avatar_contradiction_clause,[],[f1013])).

fof(f1013,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_13
    | spl9_34 ),
    inference(subsumption_resolution,[],[f1012,f93])).

fof(f1012,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_13
    | spl9_34 ),
    inference(forward_demodulation,[],[f1009,f51])).

fof(f1009,plain,
    ( ~ v1_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_13
    | spl9_34 ),
    inference(backward_demodulation,[],[f333,f990])).

fof(f1008,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | spl9_34 ),
    inference(avatar_contradiction_clause,[],[f1007])).

fof(f1007,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | spl9_34 ),
    inference(subsumption_resolution,[],[f989,f103])).

fof(f989,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,sK0,k1_xboole_0),sK3(sK1,sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | spl9_34 ),
    inference(unit_resulting_resolution,[],[f88,f99,f152,f955,f56])).

fof(f152,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | spl9_4 ),
    inference(avatar_component_clause,[],[f151])).

fof(f1006,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | spl9_34 ),
    inference(avatar_contradiction_clause,[],[f1005])).

fof(f1005,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | spl9_34 ),
    inference(subsumption_resolution,[],[f990,f152])).

fof(f1004,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | spl9_34 ),
    inference(avatar_contradiction_clause,[],[f1003])).

fof(f1003,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | spl9_34 ),
    inference(subsumption_resolution,[],[f991,f99])).

fof(f991,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl9_1
    | ~ spl9_2
    | spl9_4
    | spl9_34 ),
    inference(unit_resulting_resolution,[],[f88,f152,f103,f955,f56])).

fof(f1002,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | spl9_34 ),
    inference(avatar_contradiction_clause,[],[f1001])).

fof(f1001,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | spl9_34 ),
    inference(subsumption_resolution,[],[f992,f88])).

fof(f992,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | spl9_34 ),
    inference(unit_resulting_resolution,[],[f99,f152,f103,f955,f56])).

fof(f1000,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | spl9_34 ),
    inference(avatar_contradiction_clause,[],[f993])).

fof(f993,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4
    | spl9_34 ),
    inference(unit_resulting_resolution,[],[f88,f99,f152,f103,f955,f56])).

fof(f971,plain,
    ( ~ spl9_35
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f913,f725,f184,f91,f968])).

fof(f968,plain,
    ( spl9_35
  <=> r2_hidden(sK4(k3_xboole_0(sK0,sK0)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f725,plain,
    ( spl9_28
  <=> r2_hidden(sK4(k3_xboole_0(sK0,sK0)),k3_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f913,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK0)),k1_relat_1(sK1))
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f727,f351])).

fof(f351,plain,
    ( ! [X12,X11] :
        ( ~ r2_hidden(X11,k1_relat_1(sK1))
        | ~ r2_hidden(X11,k3_xboole_0(sK0,X12)) )
    | ~ spl9_2
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f346,f103])).

fof(f346,plain,
    ( ! [X12,X11] :
        ( r2_hidden(X11,k1_xboole_0)
        | ~ r2_hidden(X11,k1_relat_1(sK1))
        | ~ r2_hidden(X11,k3_xboole_0(sK0,X12)) )
    | ~ spl9_8 ),
    inference(superposition,[],[f259,f186])).

fof(f259,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k3_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_xboole_0(X2,X3)) ) ),
    inference(resolution,[],[f82,f84])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f727,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK0)),k3_xboole_0(sK0,sK0))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f725])).

fof(f954,plain,
    ( ~ spl9_34
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_31 ),
    inference(avatar_split_clause,[],[f915,f852,f184,f91,f951])).

fof(f852,plain,
    ( spl9_31
  <=> r2_hidden(sK2(sK1,sK0,k1_xboole_0),k3_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f915,plain,
    ( ~ r2_hidden(sK2(sK1,sK0,k1_xboole_0),k1_relat_1(sK1))
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_31 ),
    inference(unit_resulting_resolution,[],[f854,f351])).

fof(f854,plain,
    ( r2_hidden(sK2(sK1,sK0,k1_xboole_0),k3_xboole_0(sK0,sK0))
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f852])).

fof(f932,plain,
    ( ~ spl9_33
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f914,f637,f184,f91,f929])).

fof(f929,plain,
    ( spl9_33
  <=> r2_hidden(sK5(k1_xboole_0,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f637,plain,
    ( spl9_25
  <=> r2_hidden(sK5(k1_xboole_0,sK0),k3_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f914,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,sK0),k1_relat_1(sK1))
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_25 ),
    inference(unit_resulting_resolution,[],[f639,f351])).

fof(f639,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK0),k3_xboole_0(sK0,sK0))
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f637])).

fof(f901,plain,
    ( spl9_32
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f878,f725,f898])).

fof(f898,plain,
    ( spl9_32
  <=> r2_hidden(sK4(k3_xboole_0(sK0,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f878,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK0)),sK0)
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f727,f84])).

fof(f855,plain,
    ( spl9_31
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f847,f829,f852])).

fof(f847,plain,
    ( r2_hidden(sK2(sK1,sK0,k1_xboole_0),k3_xboole_0(sK0,sK0))
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f831,f831,f82])).

fof(f831,plain,
    ( r2_hidden(sK2(sK1,sK0,k1_xboole_0),sK0)
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f829])).

fof(f832,plain,
    ( spl9_30
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f772,f151,f97,f91,f86,f829])).

fof(f772,plain,
    ( r2_hidden(sK2(sK1,sK0,k1_xboole_0),sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(unit_resulting_resolution,[],[f88,f99,f152,f103,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | k7_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f821,plain,
    ( spl9_29
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f774,f97,f91,f818])).

fof(f818,plain,
    ( spl9_29
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f774,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f99,f99,f103,f103,f55])).

fof(f813,plain,
    ( spl9_18
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f773,f97,f91,f86,f465])).

fof(f465,plain,
    ( spl9_18
  <=> k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f773,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,k1_xboole_0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f88,f99,f103,f103,f55])).

fof(f810,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_20 ),
    inference(avatar_contradiction_clause,[],[f809])).

fof(f809,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f808,f93])).

fof(f808,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_20 ),
    inference(forward_demodulation,[],[f665,f773])).

fof(f665,plain,
    ( ~ v1_xboole_0(k7_relat_1(sK1,k1_xboole_0))
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f482,f70])).

fof(f482,plain,
    ( r2_hidden(sK4(k7_relat_1(sK1,k1_xboole_0)),k7_relat_1(sK1,k1_xboole_0))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl9_20
  <=> r2_hidden(sK4(k7_relat_1(sK1,k1_xboole_0)),k7_relat_1(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f807,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_20 ),
    inference(avatar_contradiction_clause,[],[f806])).

fof(f806,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f805,f93])).

fof(f805,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_20 ),
    inference(forward_demodulation,[],[f667,f773])).

fof(f667,plain,
    ( ~ v1_xboole_0(k7_relat_1(sK1,k1_xboole_0))
    | ~ spl9_20 ),
    inference(resolution,[],[f482,f70])).

fof(f801,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_20 ),
    inference(avatar_contradiction_clause,[],[f800])).

fof(f800,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f799,f103])).

fof(f799,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_xboole_0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_20 ),
    inference(forward_demodulation,[],[f795,f51])).

fof(f795,plain,
    ( r2_hidden(sK4(k1_xboole_0),k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_20 ),
    inference(backward_demodulation,[],[f664,f773])).

fof(f664,plain,
    ( r2_hidden(sK4(k7_relat_1(sK1,k1_xboole_0)),k3_xboole_0(k7_relat_1(sK1,k1_xboole_0),k7_relat_1(sK1,k1_xboole_0)))
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f482,f482,f82])).

fof(f798,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_20 ),
    inference(avatar_contradiction_clause,[],[f797])).

fof(f797,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f794,f103])).

fof(f794,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_xboole_0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_20 ),
    inference(backward_demodulation,[],[f482,f773])).

fof(f791,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_18 ),
    inference(avatar_contradiction_clause,[],[f790])).

fof(f790,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_18 ),
    inference(subsumption_resolution,[],[f770,f103])).

fof(f770,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,k1_xboole_0,k1_xboole_0),sK3(sK1,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_18 ),
    inference(unit_resulting_resolution,[],[f88,f99,f467,f103,f55])).

fof(f467,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,k1_xboole_0)
    | spl9_18 ),
    inference(avatar_component_clause,[],[f465])).

fof(f789,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_18 ),
    inference(avatar_contradiction_clause,[],[f788])).

fof(f788,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_18 ),
    inference(subsumption_resolution,[],[f771,f103])).

fof(f771,plain,
    ( r2_hidden(sK2(sK1,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_18 ),
    inference(unit_resulting_resolution,[],[f88,f99,f467,f103,f55])).

fof(f787,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_18 ),
    inference(avatar_contradiction_clause,[],[f786])).

fof(f786,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_18 ),
    inference(subsumption_resolution,[],[f773,f467])).

fof(f785,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_18 ),
    inference(avatar_contradiction_clause,[],[f784])).

fof(f784,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_18 ),
    inference(subsumption_resolution,[],[f775,f99])).

fof(f775,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl9_1
    | ~ spl9_2
    | spl9_18 ),
    inference(unit_resulting_resolution,[],[f88,f467,f103,f103,f55])).

fof(f783,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_18 ),
    inference(avatar_contradiction_clause,[],[f782])).

fof(f782,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_18 ),
    inference(subsumption_resolution,[],[f776,f88])).

fof(f776,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl9_2
    | ~ spl9_3
    | spl9_18 ),
    inference(unit_resulting_resolution,[],[f99,f467,f103,f103,f55])).

fof(f781,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_18 ),
    inference(avatar_contradiction_clause,[],[f777])).

fof(f777,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_18 ),
    inference(unit_resulting_resolution,[],[f88,f99,f467,f103,f103,f55])).

fof(f728,plain,
    ( spl9_28
    | spl9_22 ),
    inference(avatar_split_clause,[],[f563,f559,f725])).

fof(f559,plain,
    ( spl9_22
  <=> v1_xboole_0(k3_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f563,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK0)),k3_xboole_0(sK0,sK0))
    | spl9_22 ),
    inference(unit_resulting_resolution,[],[f60,f561,f62])).

fof(f561,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,sK0))
    | spl9_22 ),
    inference(avatar_component_clause,[],[f559])).

fof(f713,plain,
    ( ~ spl9_27
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f700,f673,f710])).

fof(f710,plain,
    ( spl9_27
  <=> v1_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f673,plain,
    ( spl9_26
  <=> r2_hidden(sK4(sK0),k3_xboole_0(sK0,k3_xboole_0(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f700,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK0)))
    | ~ spl9_26 ),
    inference(unit_resulting_resolution,[],[f675,f70])).

fof(f675,plain,
    ( r2_hidden(sK4(sK0),k3_xboole_0(sK0,k3_xboole_0(sK0,sK0)))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f673])).

fof(f676,plain,
    ( spl9_26
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f545,f528,f397,f673])).

fof(f397,plain,
    ( spl9_17
  <=> r2_hidden(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f545,plain,
    ( r2_hidden(sK4(sK0),k3_xboole_0(sK0,k3_xboole_0(sK0,sK0)))
    | ~ spl9_17
    | ~ spl9_21 ),
    inference(unit_resulting_resolution,[],[f399,f530,f82])).

fof(f399,plain,
    ( r2_hidden(sK4(sK0),sK0)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f397])).

fof(f662,plain,
    ( spl9_20
    | spl9_18 ),
    inference(avatar_split_clause,[],[f476,f465,f480])).

fof(f476,plain,
    ( r2_hidden(sK4(k7_relat_1(sK1,k1_xboole_0)),k7_relat_1(sK1,k1_xboole_0))
    | spl9_18 ),
    inference(unit_resulting_resolution,[],[f467,f210])).

fof(f210,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f113,f60])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f62,f59])).

fof(f640,plain,
    ( spl9_25
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f631,f625,f637])).

fof(f625,plain,
    ( spl9_24
  <=> r2_hidden(sK5(k1_xboole_0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f631,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK0),k3_xboole_0(sK0,sK0))
    | ~ spl9_24 ),
    inference(unit_resulting_resolution,[],[f627,f627,f82])).

fof(f627,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK0),sK0)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f625])).

fof(f628,plain,
    ( spl9_24
    | ~ spl9_2
    | ~ spl9_11
    | spl9_14 ),
    inference(avatar_split_clause,[],[f618,f379,f245,f91,f625])).

fof(f245,plain,
    ( spl9_11
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f379,plain,
    ( spl9_14
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f618,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK0),sK0)
    | ~ spl9_2
    | ~ spl9_11
    | spl9_14 ),
    inference(unit_resulting_resolution,[],[f380,f591])).

fof(f591,plain,
    ( ! [X5] :
        ( r2_hidden(sK5(k1_xboole_0,X5),X5)
        | k1_xboole_0 = X5 )
    | ~ spl9_2
    | ~ spl9_11 ),
    inference(forward_demodulation,[],[f590,f247])).

fof(f247,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f245])).

fof(f590,plain,
    ( ! [X5] :
        ( k1_relat_1(k1_xboole_0) = X5
        | r2_hidden(sK5(k1_xboole_0,X5),X5) )
    | ~ spl9_2 ),
    inference(resolution,[],[f68,f103])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f380,plain,
    ( k1_xboole_0 != sK0
    | spl9_14 ),
    inference(avatar_component_clause,[],[f379])).

fof(f580,plain,
    ( ~ spl9_23
    | ~ spl9_15
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f566,f397,f383,f577])).

fof(f577,plain,
    ( spl9_23
  <=> r2_hidden(sK4(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f383,plain,
    ( spl9_15
  <=> ! [X14] : ~ r2_hidden(sK4(sK0),k3_xboole_0(k1_relat_1(sK1),X14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f566,plain,
    ( ~ r2_hidden(sK4(sK0),k1_relat_1(sK1))
    | ~ spl9_15
    | ~ spl9_17 ),
    inference(unit_resulting_resolution,[],[f399,f384,f82])).

fof(f384,plain,
    ( ! [X14] : ~ r2_hidden(sK4(sK0),k3_xboole_0(k1_relat_1(sK1),X14))
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f383])).

fof(f562,plain,
    ( ~ spl9_22
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f547,f528,f559])).

fof(f547,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,sK0))
    | ~ spl9_21 ),
    inference(unit_resulting_resolution,[],[f530,f70])).

fof(f531,plain,
    ( spl9_21
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f504,f397,f528])).

fof(f504,plain,
    ( r2_hidden(sK4(sK0),k3_xboole_0(sK0,sK0))
    | ~ spl9_17 ),
    inference(unit_resulting_resolution,[],[f399,f399,f82])).

fof(f485,plain,
    ( spl9_18
    | spl9_20 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | spl9_18
    | spl9_20 ),
    inference(subsumption_resolution,[],[f481,f476])).

fof(f481,plain,
    ( ~ r2_hidden(sK4(k7_relat_1(sK1,k1_xboole_0)),k7_relat_1(sK1,k1_xboole_0))
    | spl9_20 ),
    inference(avatar_component_clause,[],[f480])).

fof(f483,plain,
    ( spl9_20
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f408,f379,f202,f480])).

fof(f202,plain,
    ( spl9_10
  <=> r2_hidden(sK4(k7_relat_1(sK1,sK0)),k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f408,plain,
    ( r2_hidden(sK4(k7_relat_1(sK1,k1_xboole_0)),k7_relat_1(sK1,k1_xboole_0))
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(backward_demodulation,[],[f204,f381])).

fof(f381,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f379])).

fof(f204,plain,
    ( r2_hidden(sK4(k7_relat_1(sK1,sK0)),k7_relat_1(sK1,sK0))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f202])).

fof(f473,plain,
    ( ~ spl9_19
    | spl9_7
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f404,f379,f176,f470])).

fof(f470,plain,
    ( spl9_19
  <=> v1_xboole_0(k7_relat_1(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f176,plain,
    ( spl9_7
  <=> v1_xboole_0(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f404,plain,
    ( ~ v1_xboole_0(k7_relat_1(sK1,k1_xboole_0))
    | spl9_7
    | ~ spl9_14 ),
    inference(backward_demodulation,[],[f178,f381])).

fof(f178,plain,
    ( ~ v1_xboole_0(k7_relat_1(sK1,sK0))
    | spl9_7 ),
    inference(avatar_component_clause,[],[f176])).

fof(f468,plain,
    ( ~ spl9_18
    | spl9_4
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f401,f379,f151,f465])).

fof(f401,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,k1_xboole_0)
    | spl9_4
    | ~ spl9_14 ),
    inference(backward_demodulation,[],[f152,f381])).

fof(f400,plain,
    ( spl9_17
    | spl9_14 ),
    inference(avatar_split_clause,[],[f387,f379,f397])).

fof(f387,plain,
    ( r2_hidden(sK4(sK0),sK0)
    | spl9_14 ),
    inference(unit_resulting_resolution,[],[f60,f380,f113])).

fof(f393,plain,
    ( ~ spl9_16
    | spl9_14 ),
    inference(avatar_split_clause,[],[f388,f379,f390])).

fof(f390,plain,
    ( spl9_16
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f388,plain,
    ( ~ v1_xboole_0(sK0)
    | spl9_14 ),
    inference(unit_resulting_resolution,[],[f380,f59])).

fof(f385,plain,
    ( spl9_14
    | spl9_15
    | ~ spl9_2
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f366,f194,f91,f383,f379])).

fof(f366,plain,
    ( ! [X14] :
        ( ~ r2_hidden(sK4(sK0),k3_xboole_0(k1_relat_1(sK1),X14))
        | k1_xboole_0 = sK0 )
    | ~ spl9_2
    | ~ spl9_9 ),
    inference(resolution,[],[f352,f210])).

fof(f352,plain,
    ( ! [X17,X16] :
        ( ~ r2_hidden(X16,sK0)
        | ~ r2_hidden(X16,k3_xboole_0(k1_relat_1(sK1),X17)) )
    | ~ spl9_2
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f348,f103])).

fof(f348,plain,
    ( ! [X17,X16] :
        ( r2_hidden(X16,k1_xboole_0)
        | ~ r2_hidden(X16,sK0)
        | ~ r2_hidden(X16,k3_xboole_0(k1_relat_1(sK1),X17)) )
    | ~ spl9_9 ),
    inference(superposition,[],[f259,f196])).

fof(f334,plain,
    ( ~ spl9_13
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f326,f310,f331])).

fof(f310,plain,
    ( spl9_12
  <=> r2_hidden(sK4(k7_relat_1(sK1,sK0)),k3_xboole_0(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f326,plain,
    ( ~ v1_xboole_0(k3_xboole_0(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0)))
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f312,f70])).

fof(f312,plain,
    ( r2_hidden(sK4(k7_relat_1(sK1,sK0)),k3_xboole_0(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0)))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f310])).

fof(f313,plain,
    ( spl9_12
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f258,f202,f310])).

fof(f258,plain,
    ( r2_hidden(sK4(k7_relat_1(sK1,sK0)),k3_xboole_0(k7_relat_1(sK1,sK0),k7_relat_1(sK1,sK0)))
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f204,f204,f82])).

fof(f248,plain,
    ( spl9_11
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f223,f91,f245])).

fof(f223,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f215,f210])).

fof(f215,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f103,f81])).

fof(f205,plain,
    ( spl9_10
    | spl9_7 ),
    inference(avatar_split_clause,[],[f181,f176,f202])).

fof(f181,plain,
    ( r2_hidden(sK4(k7_relat_1(sK1,sK0)),k7_relat_1(sK1,sK0))
    | spl9_7 ),
    inference(unit_resulting_resolution,[],[f60,f178,f62])).

fof(f197,plain,
    ( spl9_9
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f159,f155,f194])).

fof(f159,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f157,f114])).

fof(f157,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f155])).

fof(f187,plain,
    ( spl9_8
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f160,f155,f184])).

fof(f160,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f157,f64])).

fof(f180,plain,
    ( ~ spl9_4
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f49,f155,f151])).

fof(f49,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f179,plain,
    ( ~ spl9_7
    | spl9_4 ),
    inference(avatar_split_clause,[],[f174,f151,f176])).

fof(f174,plain,
    ( ~ v1_xboole_0(k7_relat_1(sK1,sK0))
    | spl9_4 ),
    inference(unit_resulting_resolution,[],[f152,f59])).

fof(f168,plain,
    ( spl9_6
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f161,f155,f165])).

fof(f161,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f157,f63])).

fof(f158,plain,
    ( spl9_4
    | spl9_5 ),
    inference(avatar_split_clause,[],[f48,f155,f151])).

fof(f48,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f100,plain,
    ( spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f95,f91,f97])).

fof(f95,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f93,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f94,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f50,f91])).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f89,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f47,f86])).

fof(f47,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

%------------------------------------------------------------------------------
