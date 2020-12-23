%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 442 expanded)
%              Number of leaves         :   55 ( 208 expanded)
%              Depth                    :   11
%              Number of atoms          :  563 (1058 expanded)
%              Number of equality atoms :  143 ( 310 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1468,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f75,f79,f83,f87,f91,f104,f111,f120,f131,f149,f163,f167,f183,f193,f197,f205,f209,f222,f227,f262,f276,f303,f315,f401,f421,f725,f1034,f1051,f1074,f1088,f1113,f1143,f1352,f1445])).

fof(f1445,plain,
    ( ~ spl2_2
    | spl2_68
    | ~ spl2_79 ),
    inference(avatar_contradiction_clause,[],[f1444])).

fof(f1444,plain,
    ( $false
    | ~ spl2_2
    | spl2_68
    | ~ spl2_79 ),
    inference(subsumption_resolution,[],[f1433,f1351])).

fof(f1351,plain,
    ( ! [X26,X27] : k7_relat_1(k6_relat_1(X27),X26) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X27),X26)))
    | ~ spl2_79 ),
    inference(avatar_component_clause,[],[f1350])).

fof(f1350,plain,
    ( spl2_79
  <=> ! [X27,X26] : k7_relat_1(k6_relat_1(X27),X26) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X27),X26))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).

fof(f1433,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl2_2
    | spl2_68
    | ~ spl2_79 ),
    inference(backward_demodulation,[],[f1050,f1363])).

fof(f1363,plain,
    ( ! [X2,X3] : k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))
    | ~ spl2_2
    | ~ spl2_79 ),
    inference(superposition,[],[f74,f1351])).

fof(f74,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_2
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1050,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))
    | spl2_68 ),
    inference(avatar_component_clause,[],[f1048])).

fof(f1048,plain,
    ( spl2_68
  <=> k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).

fof(f1352,plain,
    ( spl2_79
    | ~ spl2_34
    | ~ spl2_40
    | ~ spl2_73 ),
    inference(avatar_split_clause,[],[f1236,f1141,f419,f313,f1350])).

fof(f313,plain,
    ( spl2_34
  <=> ! [X3,X2] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f419,plain,
    ( spl2_40
  <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f1141,plain,
    ( spl2_73
  <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).

fof(f1236,plain,
    ( ! [X26,X27] : k7_relat_1(k6_relat_1(X27),X26) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X27),X26)))
    | ~ spl2_34
    | ~ spl2_40
    | ~ spl2_73 ),
    inference(forward_demodulation,[],[f1160,f420])).

fof(f420,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f419])).

fof(f1160,plain,
    ( ! [X26,X27] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X27),X26))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X27),X26))),X26)
    | ~ spl2_34
    | ~ spl2_73 ),
    inference(superposition,[],[f314,f1142])).

fof(f1142,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)
    | ~ spl2_73 ),
    inference(avatar_component_clause,[],[f1141])).

fof(f314,plain,
    ( ! [X2,X3] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f313])).

fof(f1143,plain,
    ( spl2_73
    | ~ spl2_24
    | ~ spl2_72 ),
    inference(avatar_split_clause,[],[f1120,f1111,f220,f1141])).

fof(f220,plain,
    ( spl2_24
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f1111,plain,
    ( spl2_72
  <=> ! [X7,X6] : k7_relat_1(k6_relat_1(X6),X7) = k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).

fof(f1120,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)
    | ~ spl2_24
    | ~ spl2_72 ),
    inference(superposition,[],[f1112,f221])).

fof(f221,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f220])).

fof(f1112,plain,
    ( ! [X6,X7] : k7_relat_1(k6_relat_1(X6),X7) = k4_relat_1(k7_relat_1(k6_relat_1(X6),X7))
    | ~ spl2_72 ),
    inference(avatar_component_clause,[],[f1111])).

fof(f1113,plain,
    ( spl2_72
    | ~ spl2_32
    | ~ spl2_71 ),
    inference(avatar_split_clause,[],[f1099,f1086,f301,f1111])).

fof(f301,plain,
    ( spl2_32
  <=> ! [X5,X7,X6] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f1086,plain,
    ( spl2_71
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).

fof(f1099,plain,
    ( ! [X6,X7] : k7_relat_1(k6_relat_1(X6),X7) = k4_relat_1(k7_relat_1(k6_relat_1(X6),X7))
    | ~ spl2_32
    | ~ spl2_71 ),
    inference(superposition,[],[f302,f1087])).

fof(f1087,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)
    | ~ spl2_71 ),
    inference(avatar_component_clause,[],[f1086])).

fof(f302,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f301])).

fof(f1088,plain,
    ( spl2_71
    | ~ spl2_25
    | ~ spl2_70 ),
    inference(avatar_split_clause,[],[f1081,f1072,f225,f1086])).

fof(f225,plain,
    ( spl2_25
  <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f1072,plain,
    ( spl2_70
  <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).

fof(f1081,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)
    | ~ spl2_25
    | ~ spl2_70 ),
    inference(superposition,[],[f1073,f226])).

fof(f226,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f225])).

fof(f1073,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_70 ),
    inference(avatar_component_clause,[],[f1072])).

fof(f1074,plain,
    ( spl2_70
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_67 ),
    inference(avatar_split_clause,[],[f1043,f1032,f161,f118,f1072])).

fof(f118,plain,
    ( spl2_10
  <=> ! [X1,X2] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f161,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f1032,plain,
    ( spl2_67
  <=> ! [X1,X0] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f1043,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_67 ),
    inference(subsumption_resolution,[],[f1035,f119])).

fof(f119,plain,
    ( ! [X2,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f1035,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))
        | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) )
    | ~ spl2_16
    | ~ spl2_67 ),
    inference(resolution,[],[f1033,f162])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k5_relat_1(k6_relat_1(X0),X1) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f161])).

fof(f1033,plain,
    ( ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f1032])).

fof(f1051,plain,
    ( ~ spl2_68
    | ~ spl2_1
    | ~ spl2_2
    | spl2_20
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f1026,f723,f190,f73,f69,f1048])).

fof(f69,plain,
    ( spl2_1
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f190,plain,
    ( spl2_20
  <=> k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f723,plain,
    ( spl2_54
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f1026,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_20
    | ~ spl2_54 ),
    inference(backward_demodulation,[],[f192,f1025])).

fof(f1025,plain,
    ( ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_54 ),
    inference(forward_demodulation,[],[f1020,f74])).

fof(f1020,plain,
    ( ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1))
    | ~ spl2_1
    | ~ spl2_54 ),
    inference(resolution,[],[f724,f70])).

fof(f70,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f724,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) )
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f723])).

fof(f192,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_20 ),
    inference(avatar_component_clause,[],[f190])).

fof(f1034,plain,
    ( spl2_67
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_17
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f1028,f723,f165,f73,f69,f1032])).

fof(f165,plain,
    ( spl2_17
  <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f1028,plain,
    ( ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_17
    | ~ spl2_54 ),
    inference(backward_demodulation,[],[f166,f1025])).

fof(f166,plain,
    ( ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f165])).

fof(f725,plain,(
    spl2_54 ),
    inference(avatar_split_clause,[],[f67,f723])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f421,plain,
    ( spl2_40
    | ~ spl2_29
    | ~ spl2_34
    | ~ spl2_39 ),
    inference(avatar_split_clause,[],[f413,f399,f313,f274,f419])).

fof(f274,plain,
    ( spl2_29
  <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f399,plain,
    ( spl2_39
  <=> ! [X3,X4] : k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f413,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)
    | ~ spl2_29
    | ~ spl2_34
    | ~ spl2_39 ),
    inference(forward_demodulation,[],[f405,f314])).

fof(f405,plain,
    ( ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),X3)
    | ~ spl2_29
    | ~ spl2_39 ),
    inference(superposition,[],[f400,f275])).

fof(f275,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f274])).

fof(f400,plain,
    ( ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4))))
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f399])).

fof(f401,plain,
    ( spl2_39
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f122,f118,f89,f399])).

fof(f89,plain,
    ( spl2_6
  <=> ! [X0] :
        ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f122,plain,
    ( ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4))))
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(resolution,[],[f119,f90])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f315,plain,
    ( spl2_34
    | ~ spl2_14
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f185,f181,f147,f313])).

fof(f147,plain,
    ( spl2_14
  <=> ! [X1,X2] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f181,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f185,plain,
    ( ! [X2,X3] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2)
    | ~ spl2_14
    | ~ spl2_19 ),
    inference(resolution,[],[f182,f148])).

fof(f148,plain,
    ( ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f182,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f181])).

fof(f303,plain,
    ( spl2_32
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_22
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f270,f260,f203,f118,f109,f102,f81,f69,f301])).

fof(f81,plain,
    ( spl2_4
  <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f102,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f109,plain,
    ( spl2_9
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f203,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f260,plain,
    ( spl2_28
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f270,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_22
    | ~ spl2_28 ),
    inference(backward_demodulation,[],[f218,f267])).

fof(f267,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f263,f110])).

fof(f110,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f263,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))
    | ~ spl2_1
    | ~ spl2_28 ),
    inference(resolution,[],[f261,f70])).

fof(f261,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f260])).

fof(f218,plain,
    ( ! [X6,X7,X5] : k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f217,f121])).

fof(f121,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(resolution,[],[f119,f103])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f217,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f212,f215])).

fof(f215,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f214,f110])).

fof(f214,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f213,f110])).

fof(f213,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f210,f82])).

fof(f82,plain,
    ( ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f210,plain,
    ( ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))
    | ~ spl2_1
    | ~ spl2_22 ),
    inference(resolution,[],[f204,f70])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f203])).

fof(f212,plain,
    ( ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)),k6_relat_1(X5))
    | ~ spl2_10
    | ~ spl2_22 ),
    inference(resolution,[],[f204,f119])).

fof(f276,plain,
    ( spl2_29
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f267,f260,f109,f69,f274])).

fof(f262,plain,
    ( spl2_28
    | ~ spl2_1
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f255,f207,f69,f260])).

fof(f207,plain,
    ( spl2_23
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f255,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) )
    | ~ spl2_1
    | ~ spl2_23 ),
    inference(resolution,[],[f208,f70])).

fof(f208,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f207])).

fof(f227,plain,
    ( spl2_25
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f121,f118,f102,f225])).

fof(f222,plain,
    ( spl2_24
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f215,f203,f109,f81,f69,f220])).

fof(f209,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f52,f207])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

fof(f205,plain,
    ( spl2_22
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f201,f195,f81,f69,f203])).

fof(f195,plain,
    ( spl2_21
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f198,f82])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1))) )
    | ~ spl2_1
    | ~ spl2_21 ),
    inference(resolution,[],[f196,f70])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f195])).

fof(f197,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f44,f195])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f193,plain,
    ( ~ spl2_20
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f107,f102,f69,f190])).

fof(f107,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(backward_demodulation,[],[f65,f105])).

fof(f105,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(resolution,[],[f103,f70])).

fof(f65,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f37,f64])).

fof(f37,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f35])).

fof(f35,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f183,plain,
    ( spl2_19
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f171,f161,f109,f73,f69,f181])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f170,f110])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f169,f70])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_2
    | ~ spl2_16 ),
    inference(superposition,[],[f162,f74])).

fof(f167,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f66,f165])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f46,f64])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f163,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f51,f161])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f149,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f140,f129,f109,f77,f69,f147])).

fof(f77,plain,
    ( spl2_3
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

% (28561)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f129,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f140,plain,
    ( ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f139,f78])).

fof(f78,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f139,plain,
    ( ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f138,f70])).

fof(f138,plain,
    ( ! [X2,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f133,f70])).

fof(f133,plain,
    ( ! [X2,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_9
    | ~ spl2_12 ),
    inference(superposition,[],[f130,f110])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f131,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f43,f129])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f120,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f116,f109,f85,f69,f118])).

fof(f85,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f116,plain,
    ( ! [X2,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f115,f70])).

fof(f115,plain,
    ( ! [X2,X1] :
        ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f114,f70])).

fof(f114,plain,
    ( ! [X2,X1] :
        ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(superposition,[],[f86,f110])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f111,plain,
    ( spl2_9
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f105,f102,f69,f109])).

fof(f104,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f49,f102])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f91,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f42,f89])).

fof(f42,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f87,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f53,f85])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f83,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f39,f81])).

fof(f39,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f79,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f41,f77])).

fof(f41,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f75,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f40,f73])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:53:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.42  % (28560)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.45  % (28555)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (28548)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (28550)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (28557)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (28565)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (28551)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (28552)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (28555)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f1468,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f71,f75,f79,f83,f87,f91,f104,f111,f120,f131,f149,f163,f167,f183,f193,f197,f205,f209,f222,f227,f262,f276,f303,f315,f401,f421,f725,f1034,f1051,f1074,f1088,f1113,f1143,f1352,f1445])).
% 0.22/0.50  fof(f1445,plain,(
% 0.22/0.50    ~spl2_2 | spl2_68 | ~spl2_79),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f1444])).
% 0.22/0.50  fof(f1444,plain,(
% 0.22/0.50    $false | (~spl2_2 | spl2_68 | ~spl2_79)),
% 0.22/0.50    inference(subsumption_resolution,[],[f1433,f1351])).
% 0.22/0.50  fof(f1351,plain,(
% 0.22/0.50    ( ! [X26,X27] : (k7_relat_1(k6_relat_1(X27),X26) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X27),X26)))) ) | ~spl2_79),
% 0.22/0.50    inference(avatar_component_clause,[],[f1350])).
% 0.22/0.50  fof(f1350,plain,(
% 0.22/0.50    spl2_79 <=> ! [X27,X26] : k7_relat_1(k6_relat_1(X27),X26) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X27),X26)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).
% 0.22/0.50  fof(f1433,plain,(
% 0.22/0.50    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) | (~spl2_2 | spl2_68 | ~spl2_79)),
% 0.22/0.50    inference(backward_demodulation,[],[f1050,f1363])).
% 0.22/0.50  fof(f1363,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ) | (~spl2_2 | ~spl2_79)),
% 0.22/0.50    inference(superposition,[],[f74,f1351])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl2_2 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.50  fof(f1050,plain,(
% 0.22/0.50    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) | spl2_68),
% 0.22/0.50    inference(avatar_component_clause,[],[f1048])).
% 0.22/0.50  fof(f1048,plain,(
% 0.22/0.50    spl2_68 <=> k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).
% 0.22/0.50  fof(f1352,plain,(
% 0.22/0.50    spl2_79 | ~spl2_34 | ~spl2_40 | ~spl2_73),
% 0.22/0.50    inference(avatar_split_clause,[],[f1236,f1141,f419,f313,f1350])).
% 0.22/0.50  fof(f313,plain,(
% 0.22/0.50    spl2_34 <=> ! [X3,X2] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.22/0.50  fof(f419,plain,(
% 0.22/0.50    spl2_40 <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 0.22/0.50  fof(f1141,plain,(
% 0.22/0.50    spl2_73 <=> ! [X3,X2] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_73])])).
% 0.22/0.50  fof(f1236,plain,(
% 0.22/0.50    ( ! [X26,X27] : (k7_relat_1(k6_relat_1(X27),X26) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X27),X26)))) ) | (~spl2_34 | ~spl2_40 | ~spl2_73)),
% 0.22/0.50    inference(forward_demodulation,[],[f1160,f420])).
% 0.22/0.50  fof(f420,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)) ) | ~spl2_40),
% 0.22/0.50    inference(avatar_component_clause,[],[f419])).
% 0.22/0.50  fof(f1160,plain,(
% 0.22/0.50    ( ! [X26,X27] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X27),X26))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X27),X26))),X26)) ) | (~spl2_34 | ~spl2_73)),
% 0.22/0.50    inference(superposition,[],[f314,f1142])).
% 0.22/0.50  fof(f1142,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) ) | ~spl2_73),
% 0.22/0.50    inference(avatar_component_clause,[],[f1141])).
% 0.22/0.50  fof(f314,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2)) ) | ~spl2_34),
% 0.22/0.50    inference(avatar_component_clause,[],[f313])).
% 0.22/0.50  fof(f1143,plain,(
% 0.22/0.50    spl2_73 | ~spl2_24 | ~spl2_72),
% 0.22/0.50    inference(avatar_split_clause,[],[f1120,f1111,f220,f1141])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    spl2_24 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.50  fof(f1111,plain,(
% 0.22/0.50    spl2_72 <=> ! [X7,X6] : k7_relat_1(k6_relat_1(X6),X7) = k4_relat_1(k7_relat_1(k6_relat_1(X6),X7))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).
% 0.22/0.50  fof(f1120,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) ) | (~spl2_24 | ~spl2_72)),
% 0.22/0.50    inference(superposition,[],[f1112,f221])).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ) | ~spl2_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f220])).
% 0.22/0.50  fof(f1112,plain,(
% 0.22/0.50    ( ! [X6,X7] : (k7_relat_1(k6_relat_1(X6),X7) = k4_relat_1(k7_relat_1(k6_relat_1(X6),X7))) ) | ~spl2_72),
% 0.22/0.50    inference(avatar_component_clause,[],[f1111])).
% 0.22/0.50  fof(f1113,plain,(
% 0.22/0.50    spl2_72 | ~spl2_32 | ~spl2_71),
% 0.22/0.50    inference(avatar_split_clause,[],[f1099,f1086,f301,f1111])).
% 0.22/0.50  fof(f301,plain,(
% 0.22/0.50    spl2_32 <=> ! [X5,X7,X6] : k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.22/0.50  fof(f1086,plain,(
% 0.22/0.50    spl2_71 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_71])])).
% 0.22/0.50  fof(f1099,plain,(
% 0.22/0.50    ( ! [X6,X7] : (k7_relat_1(k6_relat_1(X6),X7) = k4_relat_1(k7_relat_1(k6_relat_1(X6),X7))) ) | (~spl2_32 | ~spl2_71)),
% 0.22/0.50    inference(superposition,[],[f302,f1087])).
% 0.22/0.50  fof(f1087,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) ) | ~spl2_71),
% 0.22/0.50    inference(avatar_component_clause,[],[f1086])).
% 0.22/0.50  fof(f302,plain,(
% 0.22/0.50    ( ! [X6,X7,X5] : (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)) ) | ~spl2_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f301])).
% 0.22/0.50  fof(f1088,plain,(
% 0.22/0.50    spl2_71 | ~spl2_25 | ~spl2_70),
% 0.22/0.50    inference(avatar_split_clause,[],[f1081,f1072,f225,f1086])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    spl2_25 <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.22/0.50  fof(f1072,plain,(
% 0.22/0.50    spl2_70 <=> ! [X1,X0] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).
% 0.22/0.50  fof(f1081,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) ) | (~spl2_25 | ~spl2_70)),
% 0.22/0.50    inference(superposition,[],[f1073,f226])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) ) | ~spl2_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f225])).
% 0.22/0.50  fof(f1073,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) ) | ~spl2_70),
% 0.22/0.50    inference(avatar_component_clause,[],[f1072])).
% 0.22/0.50  fof(f1074,plain,(
% 0.22/0.50    spl2_70 | ~spl2_10 | ~spl2_16 | ~spl2_67),
% 0.22/0.50    inference(avatar_split_clause,[],[f1043,f1032,f161,f118,f1072])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    spl2_10 <=> ! [X1,X2] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    spl2_16 <=> ! [X1,X0] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.50  fof(f1032,plain,(
% 0.22/0.50    spl2_67 <=> ! [X1,X0] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 0.22/0.50  fof(f1043,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_10 | ~spl2_16 | ~spl2_67)),
% 0.22/0.50    inference(subsumption_resolution,[],[f1035,f119])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ) | ~spl2_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f118])).
% 0.22/0.50  fof(f1035,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_16 | ~spl2_67)),
% 0.22/0.50    inference(resolution,[],[f1033,f162])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) ) | ~spl2_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f161])).
% 0.22/0.50  fof(f1033,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) ) | ~spl2_67),
% 0.22/0.50    inference(avatar_component_clause,[],[f1032])).
% 0.22/0.50  fof(f1051,plain,(
% 0.22/0.50    ~spl2_68 | ~spl2_1 | ~spl2_2 | spl2_20 | ~spl2_54),
% 0.22/0.50    inference(avatar_split_clause,[],[f1026,f723,f190,f73,f69,f1048])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl2_1 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    spl2_20 <=> k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.50  fof(f723,plain,(
% 0.22/0.50    spl2_54 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 0.22/0.50  fof(f1026,plain,(
% 0.22/0.50    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) | (~spl2_1 | ~spl2_2 | spl2_20 | ~spl2_54)),
% 0.22/0.50    inference(backward_demodulation,[],[f192,f1025])).
% 0.22/0.50  fof(f1025,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_1 | ~spl2_2 | ~spl2_54)),
% 0.22/0.50    inference(forward_demodulation,[],[f1020,f74])).
% 0.22/0.50  fof(f1020,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1))) ) | (~spl2_1 | ~spl2_54)),
% 0.22/0.50    inference(resolution,[],[f724,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f69])).
% 0.22/0.50  fof(f724,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) ) | ~spl2_54),
% 0.22/0.50    inference(avatar_component_clause,[],[f723])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f190])).
% 0.22/0.50  fof(f1034,plain,(
% 0.22/0.50    spl2_67 | ~spl2_1 | ~spl2_2 | ~spl2_17 | ~spl2_54),
% 0.22/0.50    inference(avatar_split_clause,[],[f1028,f723,f165,f73,f69,f1032])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    spl2_17 <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.50  fof(f1028,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_17 | ~spl2_54)),
% 0.22/0.50    inference(backward_demodulation,[],[f166,f1025])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) ) | ~spl2_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f165])).
% 0.22/0.50  fof(f725,plain,(
% 0.22/0.50    spl2_54),
% 0.22/0.50    inference(avatar_split_clause,[],[f67,f723])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f50,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f47,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f48,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f54,f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f55,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f56,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f57,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.22/0.50  fof(f421,plain,(
% 0.22/0.50    spl2_40 | ~spl2_29 | ~spl2_34 | ~spl2_39),
% 0.22/0.50    inference(avatar_split_clause,[],[f413,f399,f313,f274,f419])).
% 0.22/0.50  fof(f274,plain,(
% 0.22/0.50    spl2_29 <=> ! [X1,X0,X2] : k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.22/0.50  fof(f399,plain,(
% 0.22/0.50    spl2_39 <=> ! [X3,X4] : k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.22/0.50  fof(f413,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)) ) | (~spl2_29 | ~spl2_34 | ~spl2_39)),
% 0.22/0.50    inference(forward_demodulation,[],[f405,f314])).
% 0.22/0.50  fof(f405,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),X3)) ) | (~spl2_29 | ~spl2_39)),
% 0.22/0.50    inference(superposition,[],[f400,f275])).
% 0.22/0.50  fof(f275,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))) ) | ~spl2_29),
% 0.22/0.50    inference(avatar_component_clause,[],[f274])).
% 0.22/0.50  fof(f400,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4))))) ) | ~spl2_39),
% 0.22/0.50    inference(avatar_component_clause,[],[f399])).
% 0.22/0.50  fof(f401,plain,(
% 0.22/0.50    spl2_39 | ~spl2_6 | ~spl2_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f122,f118,f89,f399])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl2_6 <=> ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k5_relat_1(k7_relat_1(k6_relat_1(X3),X4),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4))))) ) | (~spl2_6 | ~spl2_10)),
% 0.22/0.50    inference(resolution,[],[f119,f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) ) | ~spl2_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f89])).
% 0.22/0.50  fof(f315,plain,(
% 0.22/0.50    spl2_34 | ~spl2_14 | ~spl2_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f185,f181,f147,f313])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    spl2_14 <=> ! [X1,X2] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    spl2_19 <=> ! [X1,X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.50  fof(f185,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2)) ) | (~spl2_14 | ~spl2_19)),
% 0.22/0.50    inference(resolution,[],[f182,f148])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2)) ) | ~spl2_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f147])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f181])).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    spl2_32 | ~spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_9 | ~spl2_10 | ~spl2_22 | ~spl2_28),
% 0.22/0.50    inference(avatar_split_clause,[],[f270,f260,f203,f118,f109,f102,f81,f69,f301])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl2_4 <=> ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    spl2_8 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl2_9 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    spl2_22 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    spl2_28 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.22/0.50  fof(f270,plain,(
% 0.22/0.50    ( ! [X6,X7,X5] : (k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5)) = k7_relat_1(k7_relat_1(k6_relat_1(X5),X7),X6)) ) | (~spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_9 | ~spl2_10 | ~spl2_22 | ~spl2_28)),
% 0.22/0.50    inference(backward_demodulation,[],[f218,f267])).
% 0.22/0.50  fof(f267,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_9 | ~spl2_28)),
% 0.22/0.50    inference(forward_demodulation,[],[f263,f110])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f109])).
% 0.22/0.50  fof(f263,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_28)),
% 0.22/0.50    inference(resolution,[],[f261,f70])).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)) ) | ~spl2_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f260])).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    ( ! [X6,X7,X5] : (k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X5))) ) | (~spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_9 | ~spl2_10 | ~spl2_22)),
% 0.22/0.50    inference(forward_demodulation,[],[f217,f121])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_8 | ~spl2_10)),
% 0.22/0.50    inference(resolution,[],[f119,f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f102])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X6),k6_relat_1(X5))) ) | (~spl2_1 | ~spl2_4 | ~spl2_9 | ~spl2_10 | ~spl2_22)),
% 0.22/0.50    inference(forward_demodulation,[],[f212,f215])).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ) | (~spl2_1 | ~spl2_4 | ~spl2_9 | ~spl2_22)),
% 0.22/0.50    inference(forward_demodulation,[],[f214,f110])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ) | (~spl2_1 | ~spl2_4 | ~spl2_9 | ~spl2_22)),
% 0.22/0.50    inference(forward_demodulation,[],[f213,f110])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) ) | (~spl2_1 | ~spl2_4 | ~spl2_22)),
% 0.22/0.50    inference(forward_demodulation,[],[f210,f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) ) | ~spl2_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f81])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))) ) | (~spl2_1 | ~spl2_22)),
% 0.22/0.50    inference(resolution,[],[f204,f70])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) ) | ~spl2_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f203])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X6),X7))) = k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)),k6_relat_1(X5))) ) | (~spl2_10 | ~spl2_22)),
% 0.22/0.50    inference(resolution,[],[f204,f119])).
% 0.22/0.50  fof(f276,plain,(
% 0.22/0.50    spl2_29 | ~spl2_1 | ~spl2_9 | ~spl2_28),
% 0.22/0.50    inference(avatar_split_clause,[],[f267,f260,f109,f69,f274])).
% 0.22/0.50  fof(f262,plain,(
% 0.22/0.50    spl2_28 | ~spl2_1 | ~spl2_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f255,f207,f69,f260])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    spl2_23 <=> ! [X1,X0,X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k7_relat_1(k5_relat_1(k6_relat_1(X1),X0),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0)) ) | (~spl2_1 | ~spl2_23)),
% 0.22/0.50    inference(resolution,[],[f208,f70])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)) ) | ~spl2_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f207])).
% 0.22/0.50  fof(f227,plain,(
% 0.22/0.50    spl2_25 | ~spl2_8 | ~spl2_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f121,f118,f102,f225])).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    spl2_24 | ~spl2_1 | ~spl2_4 | ~spl2_9 | ~spl2_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f215,f203,f109,f81,f69,f220])).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    spl2_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f52,f207])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    spl2_22 | ~spl2_1 | ~spl2_4 | ~spl2_21),
% 0.22/0.50    inference(avatar_split_clause,[],[f201,f195,f81,f69,f203])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    spl2_21 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(X0)) ) | (~spl2_1 | ~spl2_4 | ~spl2_21)),
% 0.22/0.50    inference(forward_demodulation,[],[f198,f82])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1)))) ) | (~spl2_1 | ~spl2_21)),
% 0.22/0.50    inference(resolution,[],[f196,f70])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) ) | ~spl2_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f195])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    spl2_21),
% 0.22/0.50    inference(avatar_split_clause,[],[f44,f195])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    ~spl2_20 | ~spl2_1 | ~spl2_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f107,f102,f69,f190])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | (~spl2_1 | ~spl2_8)),
% 0.22/0.50    inference(backward_demodulation,[],[f65,f105])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_8)),
% 0.22/0.50    inference(resolution,[],[f103,f70])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 0.22/0.50    inference(definition_unfolding,[],[f37,f64])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.50    inference(negated_conjecture,[],[f21])).
% 0.22/0.50  fof(f21,conjecture,(
% 0.22/0.50    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    spl2_19 | ~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f171,f161,f109,f73,f69,f181])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~r1_tarski(X0,X1)) ) | (~spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_16)),
% 0.22/0.50    inference(forward_demodulation,[],[f170,f110])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ) | (~spl2_1 | ~spl2_2 | ~spl2_16)),
% 0.22/0.50    inference(subsumption_resolution,[],[f169,f70])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl2_2 | ~spl2_16)),
% 0.22/0.51    inference(superposition,[],[f162,f74])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    spl2_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f66,f165])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f46,f64])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    spl2_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f51,f161])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    spl2_14 | ~spl2_1 | ~spl2_3 | ~spl2_9 | ~spl2_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f140,f129,f109,f77,f69,f147])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    spl2_3 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.51  % (28561)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    spl2_12 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2)) ) | (~spl2_1 | ~spl2_3 | ~spl2_9 | ~spl2_12)),
% 0.22/0.51    inference(forward_demodulation,[],[f139,f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f77])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))) ) | (~spl2_1 | ~spl2_9 | ~spl2_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f138,f70])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_9 | ~spl2_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f133,f70])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_9 | ~spl2_12)),
% 0.22/0.51    inference(superposition,[],[f130,f110])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f129])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    spl2_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f43,f129])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    spl2_10 | ~spl2_1 | ~spl2_5 | ~spl2_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f116,f109,f85,f69,f118])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl2_5 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) ) | (~spl2_1 | ~spl2_5 | ~spl2_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f115,f70])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_5 | ~spl2_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f114,f70])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl2_5 | ~spl2_9)),
% 0.22/0.51    inference(superposition,[],[f86,f110])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f85])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    spl2_9 | ~spl2_1 | ~spl2_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f105,f102,f69,f109])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    spl2_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f49,f102])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    spl2_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f42,f89])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl2_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f53,f85])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    spl2_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f39,f81])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,axiom,(
% 0.22/0.51    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    spl2_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f41,f77])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    spl2_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f40,f73])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    spl2_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f38,f69])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (28555)------------------------------
% 0.22/0.51  % (28555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28555)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (28555)Memory used [KB]: 7419
% 0.22/0.51  % (28555)Time elapsed: 0.057 s
% 0.22/0.51  % (28555)------------------------------
% 0.22/0.51  % (28555)------------------------------
% 0.22/0.51  % (28549)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (28547)Success in time 0.142 s
%------------------------------------------------------------------------------
