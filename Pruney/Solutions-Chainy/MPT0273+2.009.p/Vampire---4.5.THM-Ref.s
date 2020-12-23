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
% DateTime   : Thu Dec  3 12:41:19 EST 2020

% Result     : Theorem 14.74s
% Output     : Refutation 15.24s
% Verified   : 
% Statistics : Number of formulae       :  595 (3752 expanded)
%              Number of leaves         :  110 (1364 expanded)
%              Depth                    :   13
%              Number of atoms          : 1507 (14239 expanded)
%              Number of equality atoms :  100 (2699 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2437,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f95,f101,f122,f123,f131,f151,f157,f165,f179,f181,f183,f185,f188,f189,f190,f191,f192,f217,f233,f268,f273,f287,f292,f297,f332,f333,f334,f339,f340,f341,f355,f377,f378,f405,f416,f418,f433,f435,f438,f454,f459,f472,f477,f494,f498,f503,f505,f510,f511,f512,f513,f514,f569,f574,f579,f580,f581,f603,f608,f613,f618,f623,f628,f633,f638,f640,f641,f653,f682,f684,f687,f692,f789,f991,f996,f1001,f1129,f1134,f1139,f1158,f1163,f1168,f1169,f1179,f1181,f1182,f1183,f1188,f1211,f1213,f1215,f1216,f1217,f1232,f1233,f1234,f1244,f1260,f1261,f1262,f1282,f1287,f1292,f1319,f1322,f1325,f1334,f1339,f1342,f1437,f1466,f1471,f1472,f1498,f1503,f1584,f1589,f1594,f1599,f1610,f1622,f1638,f1643,f1644,f1649,f1650,f1702,f1709,f1711,f1715,f1728,f2217,f2218,f2219,f2323,f2324,f2330,f2335,f2340,f2345,f2350,f2378,f2383,f2388,f2393,f2395,f2400,f2405,f2406,f2407,f2408,f2409,f2414,f2415,f2416,f2417,f2418,f2423,f2428,f2429,f2430,f2435,f2436])).

fof(f2436,plain,
    ( spl10_95
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f1690,f615,f2420])).

fof(f2420,plain,
    ( spl10_95
  <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_95])])).

fof(f615,plain,
    ( spl10_34
  <=> sP1(k1_tarski(sK5),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f1690,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5)))
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f81,f617,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ sP1(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(X1,sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sP1(X1,sK8(X0,X1,X2),X0)
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(X1,sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sP1(X1,sK8(X0,X1,X2),X0)
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X1,X3,X0) )
            & ( sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f617,plain,
    ( sP1(k1_tarski(sK5),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f615])).

fof(f81,plain,(
    ! [X0,X1] : sP2(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f19,f18])).

fof(f18,plain,(
    ! [X1,X3,X0] :
      ( sP1(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f2435,plain,
    ( ~ spl10_97
    | spl10_29
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f1689,f615,f571,f2432])).

fof(f2432,plain,
    ( spl10_97
  <=> sP2(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_97])])).

fof(f571,plain,
    ( spl10_29
  <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f1689,plain,
    ( ~ sP2(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5),sK7)
    | spl10_29
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f573,f617,f58])).

fof(f573,plain,
    ( ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7)
    | spl10_29 ),
    inference(avatar_component_clause,[],[f571])).

fof(f2430,plain,
    ( spl10_95
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f1687,f615,f2420])).

fof(f1687,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5)))
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f617,f218])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r2_hidden(X1,k4_xboole_0(X2,X0)) ) ),
    inference(resolution,[],[f58,f81])).

fof(f2429,plain,
    ( spl10_95
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f1694,f615,f2420])).

fof(f1694,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5)))
    | ~ spl10_34 ),
    inference(resolution,[],[f617,f218])).

fof(f2428,plain,
    ( spl10_96
    | spl10_29 ),
    inference(avatar_split_clause,[],[f2302,f571,f2425])).

fof(f2425,plain,
    ( spl10_96
  <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).

fof(f2302,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),sK7))
    | spl10_29 ),
    inference(unit_resulting_resolution,[],[f249,f573,f827])).

fof(f827,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f218,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f249,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f84,f103,f68])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP4(X0,X1,X2,X3)
      | ~ sP3(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ( ( ~ sP3(sK9(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK9(X0,X1,X2,X3),X3) )
          & ( sP3(sK9(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK9(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP3(X5,X2,X1,X0) )
            & ( sP3(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f39,f40])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP3(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP3(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP3(sK9(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK9(X0,X1,X2,X3),X3) )
        & ( sP3(sK9(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK9(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP3(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP3(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP3(X5,X2,X1,X0) )
            & ( sP3(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP3(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP3(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP3(X4,X2,X1,X0) )
            & ( sP3(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP4(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( sP4(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP3(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f103,plain,(
    ! [X0] : sP4(X0,X0,X0,k1_tarski(X0)) ),
    inference(superposition,[],[f102,f52])).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f102,plain,(
    ! [X0,X1] : sP4(X0,X0,X1,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f85,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f85,plain,(
    ! [X2,X0,X1] : sP4(X0,X1,X2,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP4(X0,X1,X2,X3) )
      & ( sP4(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP4(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f15,f22,f21])).

fof(f21,plain,(
    ! [X4,X2,X1,X0] :
      ( sP3(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f84,plain,(
    ! [X2,X3,X1] : sP3(X3,X1,X2,X3) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | X0 != X3 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP3(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP3(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP3(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP3(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP3(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP3(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f2423,plain,
    ( spl10_95
    | spl10_19 ),
    inference(avatar_split_clause,[],[f2294,f370,f2420])).

fof(f370,plain,
    ( spl10_19
  <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f2294,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5)))
    | spl10_19 ),
    inference(unit_resulting_resolution,[],[f249,f371,f827])).

fof(f371,plain,
    ( ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5))
    | spl10_19 ),
    inference(avatar_component_clause,[],[f370])).

fof(f2418,plain,
    ( ~ spl10_18
    | spl10_40 ),
    inference(avatar_split_clause,[],[f1276,f679,f336])).

fof(f336,plain,
    ( spl10_18
  <=> sP3(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f679,plain,
    ( spl10_40
  <=> r2_hidden(k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f1276,plain,
    ( ~ sP3(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | spl10_40 ),
    inference(unit_resulting_resolution,[],[f103,f681,f68])).

fof(f681,plain,
    ( ~ r2_hidden(k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))
    | spl10_40 ),
    inference(avatar_component_clause,[],[f679])).

fof(f2417,plain,
    ( ~ spl10_18
    | spl10_40 ),
    inference(avatar_split_clause,[],[f1263,f679,f336])).

fof(f1263,plain,
    ( ~ sP3(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | spl10_40 ),
    inference(unit_resulting_resolution,[],[f681,f252])).

fof(f252,plain,(
    ! [X8,X7] :
      ( ~ sP3(X7,X8,X8,X8)
      | r2_hidden(X7,k1_tarski(X8)) ) ),
    inference(resolution,[],[f68,f103])).

fof(f2416,plain,
    ( ~ spl10_17
    | spl10_27 ),
    inference(avatar_split_clause,[],[f1120,f507,f329])).

fof(f329,plain,
    ( spl10_17
  <=> sP3(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f507,plain,
    ( spl10_27
  <=> r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f1120,plain,
    ( ~ sP3(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5))
    | spl10_27 ),
    inference(unit_resulting_resolution,[],[f103,f509,f68])).

fof(f509,plain,
    ( ~ r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5)))
    | spl10_27 ),
    inference(avatar_component_clause,[],[f507])).

fof(f2415,plain,
    ( ~ spl10_17
    | spl10_27 ),
    inference(avatar_split_clause,[],[f1110,f507,f329])).

fof(f1110,plain,
    ( ~ sP3(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5))
    | spl10_27 ),
    inference(unit_resulting_resolution,[],[f509,f252])).

fof(f2414,plain,
    ( ~ spl10_94
    | spl10_4
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f642,f630,f119,f2411])).

fof(f2411,plain,
    ( spl10_94
  <=> sP2(k1_tarski(sK5),sK7,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f119,plain,
    ( spl10_4
  <=> r2_hidden(sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f630,plain,
    ( spl10_37
  <=> sP1(sK7,sK5,k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f642,plain,
    ( ~ sP2(k1_tarski(sK5),sK7,sK7)
    | spl10_4
    | ~ spl10_37 ),
    inference(unit_resulting_resolution,[],[f121,f632,f58])).

fof(f632,plain,
    ( sP1(sK7,sK5,k1_tarski(sK5))
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f630])).

fof(f121,plain,
    ( ~ r2_hidden(sK5,sK7)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f2409,plain,
    ( spl10_7
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f782,f289,f148])).

fof(f148,plain,
    ( spl10_7
  <=> r2_hidden(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f289,plain,
    ( spl10_15
  <=> sP1(k1_tarski(sK5),sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f782,plain,
    ( r2_hidden(sK6,sK7)
    | ~ spl10_15 ),
    inference(unit_resulting_resolution,[],[f291,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f291,plain,
    ( sP1(k1_tarski(sK5),sK6,sK7)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f289])).

fof(f2408,plain,
    ( spl10_7
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f784,f289,f148])).

fof(f784,plain,
    ( r2_hidden(sK6,sK7)
    | ~ spl10_15 ),
    inference(resolution,[],[f291,f61])).

fof(f2407,plain,
    ( spl10_7
    | spl10_21 ),
    inference(avatar_split_clause,[],[f1107,f402,f148])).

fof(f402,plain,
    ( spl10_21
  <=> sP1(sK7,sK6,k2_tarski(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f1107,plain,
    ( r2_hidden(sK6,sK7)
    | spl10_21 ),
    inference(unit_resulting_resolution,[],[f244,f404,f63])).

fof(f404,plain,
    ( ~ sP1(sK7,sK6,k2_tarski(sK5,sK6))
    | spl10_21 ),
    inference(avatar_component_clause,[],[f402])).

fof(f244,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f82,f102,f68])).

fof(f82,plain,(
    ! [X2,X3,X1] : sP3(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2406,plain,
    ( ~ spl10_92
    | spl10_21 ),
    inference(avatar_split_clause,[],[f1106,f402,f2397])).

fof(f2397,plain,
    ( spl10_92
  <=> r2_hidden(sK6,k4_xboole_0(k2_tarski(sK5,sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).

fof(f1106,plain,
    ( ~ r2_hidden(sK6,k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | spl10_21 ),
    inference(unit_resulting_resolution,[],[f81,f404,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP1(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2405,plain,
    ( ~ spl10_93
    | spl10_21 ),
    inference(avatar_split_clause,[],[f1100,f402,f2402])).

fof(f2402,plain,
    ( spl10_93
  <=> sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).

fof(f1100,plain,
    ( ~ sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK6))
    | spl10_21 ),
    inference(unit_resulting_resolution,[],[f249,f404,f57])).

fof(f2400,plain,
    ( ~ spl10_92
    | spl10_21 ),
    inference(avatar_split_clause,[],[f1098,f402,f2397])).

fof(f1098,plain,
    ( ~ r2_hidden(sK6,k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | spl10_21 ),
    inference(unit_resulting_resolution,[],[f404,f206])).

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | sP1(X2,X0,X1) ) ),
    inference(resolution,[],[f57,f81])).

fof(f2395,plain,
    ( spl10_7
    | spl10_21 ),
    inference(avatar_split_clause,[],[f2394,f402,f148])).

fof(f2394,plain,
    ( r2_hidden(sK6,sK7)
    | spl10_21 ),
    inference(subsumption_resolution,[],[f1109,f244])).

fof(f1109,plain,
    ( r2_hidden(sK6,sK7)
    | ~ r2_hidden(sK6,k2_tarski(sK5,sK6))
    | spl10_21 ),
    inference(resolution,[],[f404,f63])).

fof(f2393,plain,
    ( ~ spl10_91
    | spl10_4
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f1246,f625,f119,f2390])).

fof(f2390,plain,
    ( spl10_91
  <=> sP2(k1_tarski(sK5),k1_tarski(sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_91])])).

fof(f625,plain,
    ( spl10_36
  <=> sP1(k1_tarski(sK6),sK5,k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f1246,plain,
    ( ~ sP2(k1_tarski(sK5),k1_tarski(sK6),sK7)
    | spl10_4
    | ~ spl10_36 ),
    inference(unit_resulting_resolution,[],[f121,f627,f58])).

fof(f627,plain,
    ( sP1(k1_tarski(sK6),sK5,k1_tarski(sK5))
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f625])).

fof(f2388,plain,
    ( ~ spl10_90
    | spl10_22
    | ~ spl10_45 ),
    inference(avatar_split_clause,[],[f2203,f998,f430,f2385])).

fof(f2385,plain,
    ( spl10_90
  <=> sP2(k4_xboole_0(k1_tarski(sK5),sK7),sK7,k1_tarski(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).

fof(f430,plain,
    ( spl10_22
  <=> r2_hidden(sK5,k1_tarski(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f998,plain,
    ( spl10_45
  <=> sP1(sK7,sK5,k4_xboole_0(k1_tarski(sK5),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f2203,plain,
    ( ~ sP2(k4_xboole_0(k1_tarski(sK5),sK7),sK7,k1_tarski(sK6))
    | spl10_22
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f432,f1000,f58])).

fof(f1000,plain,
    ( sP1(sK7,sK5,k4_xboole_0(k1_tarski(sK5),sK7))
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f998])).

fof(f432,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK6))
    | spl10_22 ),
    inference(avatar_component_clause,[],[f430])).

fof(f2383,plain,
    ( ~ spl10_89
    | spl10_4
    | ~ spl10_45 ),
    inference(avatar_split_clause,[],[f2202,f998,f119,f2380])).

fof(f2380,plain,
    ( spl10_89
  <=> sP2(k4_xboole_0(k1_tarski(sK5),sK7),sK7,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).

fof(f2202,plain,
    ( ~ sP2(k4_xboole_0(k1_tarski(sK5),sK7),sK7,sK7)
    | spl10_4
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f121,f1000,f58])).

fof(f2378,plain,
    ( spl10_88
    | ~ spl10_28
    | spl10_60 ),
    inference(avatar_split_clause,[],[f2373,f1316,f566,f2375])).

fof(f2375,plain,
    ( spl10_88
  <=> sK6 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f566,plain,
    ( spl10_28
  <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f1316,plain,
    ( spl10_60
  <=> sK5 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f2373,plain,
    ( sK6 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))
    | ~ spl10_28
    | spl10_60 ),
    inference(subsumption_resolution,[],[f2366,f1317])).

fof(f1317,plain,
    ( sK5 != sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))
    | spl10_60 ),
    inference(avatar_component_clause,[],[f1316])).

fof(f2366,plain,
    ( sK5 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))
    | sK6 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))
    | ~ spl10_28 ),
    inference(resolution,[],[f881,f568])).

fof(f568,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f566])).

fof(f881,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_tarski(X1,X2))
      | X0 = X1
      | X0 = X2 ) ),
    inference(duplicate_literal_removal,[],[f874])).

fof(f874,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_tarski(X1,X2))
      | X0 = X1
      | X0 = X1
      | X0 = X2 ) ),
    inference(resolution,[],[f235,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X0,X1,X2,X3)
      | X0 = X2
      | X0 = X3
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f235,plain,(
    ! [X6,X4,X5] :
      ( sP3(X4,X6,X5,X5)
      | ~ r2_hidden(X4,k2_tarski(X5,X6)) ) ),
    inference(resolution,[],[f67,f102])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP4(X0,X1,X2,X3)
      | ~ r2_hidden(X5,X3)
      | sP3(X5,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2350,plain,
    ( spl10_87
    | spl10_27 ),
    inference(avatar_split_clause,[],[f2220,f507,f2347])).

fof(f2347,plain,
    ( spl10_87
  <=> r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)),k1_tarski(k1_tarski(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_87])])).

fof(f2220,plain,
    ( r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)),k1_tarski(k1_tarski(sK5))))
    | spl10_27 ),
    inference(unit_resulting_resolution,[],[f249,f509,f827])).

fof(f2345,plain,
    ( spl10_86
    | spl10_40 ),
    inference(avatar_split_clause,[],[f2226,f679,f2342])).

fof(f2342,plain,
    ( spl10_86
  <=> r2_hidden(k1_tarski(sK5),k4_xboole_0(k1_tarski(k1_tarski(sK5)),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).

fof(f2226,plain,
    ( r2_hidden(k1_tarski(sK5),k4_xboole_0(k1_tarski(k1_tarski(sK5)),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))))
    | spl10_40 ),
    inference(unit_resulting_resolution,[],[f249,f681,f827])).

fof(f2340,plain,
    ( spl10_85
    | spl10_22
    | ~ spl10_39 ),
    inference(avatar_split_clause,[],[f2241,f650,f430,f2337])).

fof(f2337,plain,
    ( spl10_85
  <=> r2_hidden(sK5,k4_xboole_0(k4_xboole_0(k1_tarski(sK5),sK7),k1_tarski(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_85])])).

fof(f650,plain,
    ( spl10_39
  <=> r2_hidden(sK5,k4_xboole_0(k1_tarski(sK5),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f2241,plain,
    ( r2_hidden(sK5,k4_xboole_0(k4_xboole_0(k1_tarski(sK5),sK7),k1_tarski(sK6)))
    | spl10_22
    | ~ spl10_39 ),
    inference(unit_resulting_resolution,[],[f652,f432,f827])).

fof(f652,plain,
    ( r2_hidden(sK5,k4_xboole_0(k1_tarski(sK5),sK7))
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f650])).

fof(f2335,plain,
    ( spl10_84
    | spl10_10
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f2269,f786,f214,f2332])).

fof(f2332,plain,
    ( spl10_84
  <=> r2_hidden(sK6,k4_xboole_0(k4_xboole_0(sK7,k1_tarski(sK5)),k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f214,plain,
    ( spl10_10
  <=> r2_hidden(sK6,k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

% (9596)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% (9325)Termination reason: Time limit

% (9325)Memory used [KB]: 9850
% (9325)Time elapsed: 1.839 s
% (9325)------------------------------
% (9325)------------------------------
fof(f786,plain,
    ( spl10_42
  <=> r2_hidden(sK6,k4_xboole_0(sK7,k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f2269,plain,
    ( r2_hidden(sK6,k4_xboole_0(k4_xboole_0(sK7,k1_tarski(sK5)),k1_tarski(sK5)))
    | spl10_10
    | ~ spl10_42 ),
    inference(unit_resulting_resolution,[],[f788,f216,f827])).

fof(f216,plain,
    ( ~ r2_hidden(sK6,k1_tarski(sK5))
    | spl10_10 ),
    inference(avatar_component_clause,[],[f214])).

fof(f788,plain,
    ( r2_hidden(sK6,k4_xboole_0(sK7,k1_tarski(sK5)))
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f786])).

fof(f2330,plain,
    ( spl10_83
    | spl10_19
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f2292,f566,f370,f2327])).

fof(f2327,plain,
    ( spl10_83
  <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).

fof(f2292,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK5)))
    | spl10_19
    | ~ spl10_28 ),
    inference(unit_resulting_resolution,[],[f568,f371,f827])).

fof(f2324,plain,
    ( spl10_82
    | spl10_29
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f2301,f576,f571,f2320])).

fof(f2320,plain,
    ( spl10_82
  <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).

fof(f576,plain,
    ( spl10_30
  <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f2301,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),sK7))
    | spl10_29
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f578,f573,f827])).

fof(f578,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f576])).

fof(f2323,plain,
    ( spl10_82
    | spl10_29
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f2318,f1635,f571,f2320])).

fof(f1635,plain,
    ( spl10_74
  <=> k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).

fof(f2318,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),sK7))
    | spl10_29
    | ~ spl10_74 ),
    inference(forward_demodulation,[],[f2302,f1637])).

fof(f1637,plain,
    ( k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))
    | ~ spl10_74 ),
    inference(avatar_component_clause,[],[f1635])).

fof(f2219,plain,
    ( spl10_81
    | ~ spl10_45 ),
    inference(avatar_split_clause,[],[f2210,f998,f2214])).

fof(f2214,plain,
    ( spl10_81
  <=> r2_hidden(sK5,k4_xboole_0(k4_xboole_0(k1_tarski(sK5),sK7),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_81])])).

fof(f2210,plain,
    ( r2_hidden(sK5,k4_xboole_0(k4_xboole_0(k1_tarski(sK5),sK7),sK7))
    | ~ spl10_45 ),
    inference(resolution,[],[f1000,f218])).

fof(f2218,plain,
    ( spl10_81
    | ~ spl10_45 ),
    inference(avatar_split_clause,[],[f2201,f998,f2214])).

fof(f2201,plain,
    ( r2_hidden(sK5,k4_xboole_0(k4_xboole_0(k1_tarski(sK5),sK7),sK7))
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f1000,f218])).

fof(f2217,plain,
    ( spl10_81
    | ~ spl10_45 ),
    inference(avatar_split_clause,[],[f2206,f998,f2214])).

fof(f2206,plain,
    ( r2_hidden(sK5,k4_xboole_0(k4_xboole_0(k1_tarski(sK5),sK7),sK7))
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f81,f1000,f58])).

fof(f1728,plain,
    ( spl10_79
    | spl10_80
    | spl10_41 ),
    inference(avatar_split_clause,[],[f1719,f689,f1725,f1721])).

fof(f1721,plain,
    ( spl10_79
  <=> r2_hidden(sK9(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))),k1_tarski(k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f1725,plain,
    ( spl10_80
  <=> sP3(sK9(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f689,plain,
    ( spl10_41
  <=> sP4(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f1719,plain,
    ( sP3(sK9(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | r2_hidden(sK9(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))),k1_tarski(k1_tarski(sK5)))
    | spl10_41 ),
    inference(resolution,[],[f691,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X0,X1,X2,X3)
      | sP3(sK9(X0,X1,X2,X3),X2,X1,X0)
      | r2_hidden(sK9(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f691,plain,
    ( ~ sP4(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5)))
    | spl10_41 ),
    inference(avatar_component_clause,[],[f689])).

fof(f1715,plain,
    ( spl10_77
    | ~ spl10_34
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f1714,f1635,f615,f1699])).

fof(f1699,plain,
    ( spl10_77
  <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).

fof(f1714,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5)))
    | ~ spl10_34
    | ~ spl10_74 ),
    inference(forward_demodulation,[],[f1694,f1637])).

fof(f1711,plain,
    ( spl10_77
    | ~ spl10_34
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f1710,f1635,f615,f1699])).

fof(f1710,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5)))
    | ~ spl10_34
    | ~ spl10_74 ),
    inference(forward_demodulation,[],[f1687,f1637])).

fof(f1709,plain,
    ( ~ spl10_78
    | spl10_19
    | ~ spl10_34
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f1704,f1635,f615,f370,f1706])).

fof(f1706,plain,
    ( spl10_78
  <=> sP2(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).

fof(f1704,plain,
    ( ~ sP2(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5))
    | spl10_19
    | ~ spl10_34
    | ~ spl10_74 ),
    inference(forward_demodulation,[],[f1688,f1637])).

fof(f1688,plain,
    ( ~ sP2(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5),k1_tarski(sK5))
    | spl10_19
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f371,f617,f58])).

fof(f1702,plain,
    ( spl10_77
    | ~ spl10_34
    | ~ spl10_74 ),
    inference(avatar_split_clause,[],[f1697,f1635,f615,f1699])).

fof(f1697,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5)))
    | ~ spl10_34
    | ~ spl10_74 ),
    inference(forward_demodulation,[],[f1690,f1637])).

fof(f1650,plain,
    ( spl10_74
    | ~ spl10_53 ),
    inference(avatar_split_clause,[],[f1633,f1208,f1635])).

fof(f1208,plain,
    ( spl10_53
  <=> sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f1633,plain,
    ( k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))
    | ~ spl10_53 ),
    inference(resolution,[],[f1209,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1209,plain,
    ( sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))
    | ~ spl10_53 ),
    inference(avatar_component_clause,[],[f1208])).

fof(f1649,plain,
    ( spl10_76
    | spl10_4
    | ~ spl10_53 ),
    inference(avatar_split_clause,[],[f1625,f1208,f119,f1646])).

fof(f1646,plain,
    ( spl10_76
  <=> r2_hidden(sK5,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f1625,plain,
    ( r2_hidden(sK5,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))
    | spl10_4
    | ~ spl10_53 ),
    inference(unit_resulting_resolution,[],[f727,f1209,f58])).

fof(f727,plain,
    ( ! [X0] : sP1(sK7,sK5,k2_tarski(sK5,X0))
    | spl10_4 ),
    inference(unit_resulting_resolution,[],[f121,f246,f63])).

fof(f246,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f84,f102,f68])).

fof(f1644,plain,
    ( ~ spl10_75
    | spl10_21
    | ~ spl10_53 ),
    inference(avatar_split_clause,[],[f1627,f1208,f402,f1640])).

fof(f1640,plain,
    ( spl10_75
  <=> r2_hidden(sK6,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).

fof(f1627,plain,
    ( ~ r2_hidden(sK6,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))
    | spl10_21
    | ~ spl10_53 ),
    inference(unit_resulting_resolution,[],[f404,f1209,f57])).

fof(f1643,plain,
    ( ~ spl10_75
    | ~ spl10_7
    | ~ spl10_53 ),
    inference(avatar_split_clause,[],[f1628,f1208,f148,f1640])).

fof(f1628,plain,
    ( ~ r2_hidden(sK6,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))
    | ~ spl10_7
    | ~ spl10_53 ),
    inference(unit_resulting_resolution,[],[f518,f1209,f57])).

fof(f518,plain,
    ( ! [X0] : ~ sP1(sK7,sK6,X0)
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f150,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f150,plain,
    ( r2_hidden(sK6,sK7)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f148])).

fof(f1638,plain,
    ( spl10_74
    | ~ spl10_53 ),
    inference(avatar_split_clause,[],[f1630,f1208,f1635])).

fof(f1630,plain,
    ( k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))
    | ~ spl10_53 ),
    inference(unit_resulting_resolution,[],[f1209,f65])).

fof(f1622,plain,
    ( spl10_72
    | spl10_73
    | spl10_53 ),
    inference(avatar_split_clause,[],[f1613,f1208,f1619,f1615])).

fof(f1615,plain,
    ( spl10_72
  <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))),k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f1619,plain,
    ( spl10_73
  <=> sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))),k2_tarski(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f1613,plain,
    ( sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))),k2_tarski(sK5,sK6))
    | r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))),k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))
    | spl10_53 ),
    inference(resolution,[],[f1210,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | sP1(X1,sK8(X0,X1,X2),X0)
      | r2_hidden(sK8(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1210,plain,
    ( ~ sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))
    | spl10_53 ),
    inference(avatar_component_clause,[],[f1208])).

fof(f1610,plain,
    ( spl10_70
    | spl10_71
    | spl10_38 ),
    inference(avatar_split_clause,[],[f1601,f635,f1607,f1603])).

fof(f1603,plain,
    ( spl10_70
  <=> r2_hidden(sK9(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f1607,plain,
    ( spl10_71
  <=> sP3(sK9(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).

fof(f635,plain,
    ( spl10_38
  <=> sP4(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f1601,plain,
    ( sP3(sK9(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5))
    | r2_hidden(sK9(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))
    | spl10_38 ),
    inference(resolution,[],[f637,f69])).

fof(f637,plain,
    ( ~ sP4(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))
    | spl10_38 ),
    inference(avatar_component_clause,[],[f635])).

fof(f1599,plain,
    ( spl10_69
    | ~ spl10_7
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f1572,f576,f148,f1596])).

fof(f1596,plain,
    ( spl10_69
  <=> sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK6,k4_xboole_0(k2_tarski(sK5,sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f1572,plain,
    ( sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK6,k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | ~ spl10_7
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f547,f578,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( X0 != X1
          & ~ r2_hidden(X0,X2) )
        | r2_hidden(X1,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X0,X2) )
          & ~ r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f547,plain,
    ( ! [X0] : ~ r2_hidden(sK6,k4_xboole_0(X0,sK7))
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f81,f518,f57])).

fof(f1594,plain,
    ( spl10_68
    | spl10_19
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f1576,f576,f370,f1591])).

fof(f1591,plain,
    ( spl10_68
  <=> sP1(k1_tarski(sK5),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).

fof(f1576,plain,
    ( sP1(k1_tarski(sK5),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | spl10_19
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f371,f578,f63])).

fof(f1589,plain,
    ( spl10_67
    | spl10_29
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f1577,f576,f571,f1586])).

fof(f1586,plain,
    ( spl10_67
  <=> sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_67])])).

fof(f1577,plain,
    ( sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | spl10_29
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f573,f578,f63])).

fof(f1584,plain,
    ( ~ spl10_66
    | spl10_26
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f1578,f576,f474,f1581])).

fof(f1581,plain,
    ( spl10_66
  <=> sP4(sK5,sK5,sK5,k4_xboole_0(k2_tarski(sK5,sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f474,plain,
    ( spl10_26
  <=> sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f1578,plain,
    ( ~ sP4(sK5,sK5,sK5,k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | spl10_26
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f476,f578,f67])).

fof(f476,plain,
    ( ~ sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK5,sK5)
    | spl10_26 ),
    inference(avatar_component_clause,[],[f474])).

fof(f1503,plain,
    ( spl10_65
    | spl10_4
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f1482,f786,f119,f1500])).

fof(f1500,plain,
    ( spl10_65
  <=> sP0(sK6,sK5,k4_xboole_0(sK7,k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).

fof(f1482,plain,
    ( sP0(sK6,sK5,k4_xboole_0(sK7,k1_tarski(sK5)))
    | spl10_4
    | ~ spl10_42 ),
    inference(unit_resulting_resolution,[],[f346,f788,f48])).

fof(f346,plain,
    ( ! [X0] : ~ r2_hidden(sK5,k4_xboole_0(sK7,X0))
    | spl10_4 ),
    inference(unit_resulting_resolution,[],[f81,f304,f57])).

fof(f304,plain,
    ( ! [X0] : ~ sP1(X0,sK5,sK7)
    | spl10_4 ),
    inference(unit_resulting_resolution,[],[f121,f61])).

fof(f1498,plain,
    ( spl10_64
    | spl10_10
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f1489,f786,f214,f1495])).

fof(f1495,plain,
    ( spl10_64
  <=> sP1(k1_tarski(sK5),sK6,k4_xboole_0(sK7,k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f1489,plain,
    ( sP1(k1_tarski(sK5),sK6,k4_xboole_0(sK7,k1_tarski(sK5)))
    | spl10_10
    | ~ spl10_42 ),
    inference(unit_resulting_resolution,[],[f216,f788,f63])).

fof(f1472,plain,
    ( spl10_62
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f1455,f566,f1463])).

fof(f1463,plain,
    ( spl10_62
  <=> sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK6,sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f1455,plain,
    ( sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK6,sK5,sK5)
    | ~ spl10_28 ),
    inference(unit_resulting_resolution,[],[f568,f235])).

fof(f1471,plain,
    ( spl10_63
    | spl10_19
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f1458,f566,f370,f1468])).

fof(f1468,plain,
    ( spl10_63
  <=> sP1(k1_tarski(sK5),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_63])])).

fof(f1458,plain,
    ( sP1(k1_tarski(sK5),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | spl10_19
    | ~ spl10_28 ),
    inference(unit_resulting_resolution,[],[f371,f568,f63])).

fof(f1466,plain,
    ( spl10_62
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f1460,f566,f1463])).

fof(f1460,plain,
    ( sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK6,sK5,sK5)
    | ~ spl10_28 ),
    inference(unit_resulting_resolution,[],[f102,f568,f67])).

fof(f1437,plain,
    ( ~ spl10_61
    | spl10_26 ),
    inference(avatar_split_clause,[],[f1421,f474,f1434])).

fof(f1434,plain,
    ( spl10_61
  <=> sP4(sK5,sK5,sK5,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f1421,plain,
    ( ~ sP4(sK5,sK5,sK5,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))
    | spl10_26 ),
    inference(unit_resulting_resolution,[],[f249,f476,f67])).

fof(f1342,plain,
    ( spl10_28
    | ~ spl10_60 ),
    inference(avatar_contradiction_clause,[],[f1341])).

fof(f1341,plain,
    ( $false
    | spl10_28
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f1340,f246])).

fof(f1340,plain,
    ( ~ r2_hidden(sK5,k2_tarski(sK5,sK6))
    | spl10_28
    | ~ spl10_60 ),
    inference(forward_demodulation,[],[f567,f1318])).

fof(f1318,plain,
    ( sK5 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))
    | ~ spl10_60 ),
    inference(avatar_component_clause,[],[f1316])).

fof(f567,plain,
    ( ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | spl10_28 ),
    inference(avatar_component_clause,[],[f566])).

fof(f1339,plain,
    ( spl10_4
    | spl10_20
    | ~ spl10_60 ),
    inference(avatar_contradiction_clause,[],[f1338])).

fof(f1338,plain,
    ( $false
    | spl10_4
    | spl10_20
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f1337,f246])).

fof(f1337,plain,
    ( ~ r2_hidden(sK5,k2_tarski(sK5,sK6))
    | spl10_4
    | spl10_20
    | ~ spl10_60 ),
    inference(forward_demodulation,[],[f1336,f1318])).

fof(f1336,plain,
    ( ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | spl10_4
    | spl10_20
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f1335,f121])).

fof(f1335,plain,
    ( r2_hidden(sK5,sK7)
    | ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | spl10_20
    | ~ spl10_60 ),
    inference(forward_demodulation,[],[f1206,f1318])).

fof(f1206,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7)
    | ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | spl10_20 ),
    inference(resolution,[],[f375,f63])).

fof(f375,plain,
    ( ~ sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | spl10_20 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl10_20
  <=> sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f1334,plain,
    ( spl10_3
    | spl10_4
    | ~ spl10_19
    | ~ spl10_60 ),
    inference(avatar_contradiction_clause,[],[f1333])).

fof(f1333,plain,
    ( $false
    | spl10_3
    | spl10_4
    | ~ spl10_19
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f1332,f246])).

fof(f1332,plain,
    ( ~ r2_hidden(sK5,k2_tarski(sK5,sK6))
    | spl10_3
    | spl10_4
    | ~ spl10_19
    | ~ spl10_60 ),
    inference(forward_demodulation,[],[f1331,f1318])).

fof(f1331,plain,
    ( ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | spl10_3
    | spl10_4
    | ~ spl10_19
    | ~ spl10_60 ),
    inference(subsumption_resolution,[],[f1330,f121])).

fof(f1330,plain,
    ( r2_hidden(sK5,sK7)
    | ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | spl10_3
    | ~ spl10_19
    | ~ spl10_60 ),
    inference(forward_demodulation,[],[f1323,f1318])).

fof(f1323,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7)
    | ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | spl10_3
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f1177,f99])).

fof(f99,plain,
    ( ~ sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl10_3
  <=> sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f1177,plain,
    ( sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))
    | r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7)
    | ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | ~ spl10_19 ),
    inference(resolution,[],[f372,f419])).

fof(f419,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1,X2),X2)
      | sP2(X0,X1,X2)
      | r2_hidden(sK8(X0,X1,X2),X1)
      | ~ r2_hidden(sK8(X0,X1,X2),X0) ) ),
    inference(resolution,[],[f60,f63])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X1,sK8(X0,X1,X2),X0)
      | sP2(X0,X1,X2)
      | ~ r2_hidden(sK8(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f372,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f370])).

fof(f1325,plain,
    ( spl10_29
    | spl10_3
    | ~ spl10_19
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f1324,f566,f370,f98,f571])).

fof(f1324,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7)
    | spl10_3
    | ~ spl10_19
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f1323,f568])).

fof(f1322,plain,
    ( spl10_29
    | spl10_20
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f1321,f566,f374,f571])).

fof(f1321,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7)
    | spl10_20
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f1206,f568])).

fof(f1319,plain,
    ( spl10_60
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f1306,f474,f1316])).

fof(f1306,plain,
    ( sK5 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))
    | ~ spl10_26 ),
    inference(duplicate_literal_removal,[],[f1303])).

fof(f1303,plain,
    ( sK5 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))
    | sK5 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))
    | sK5 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))
    | ~ spl10_26 ),
    inference(resolution,[],[f475,f71])).

fof(f475,plain,
    ( sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK5,sK5)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f474])).

fof(f1292,plain,
    ( spl10_59
    | spl10_40 ),
    inference(avatar_split_clause,[],[f1265,f679,f1289])).

fof(f1289,plain,
    ( spl10_59
  <=> sP0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).

fof(f1265,plain,
    ( sP0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))
    | spl10_40 ),
    inference(unit_resulting_resolution,[],[f249,f681,f48])).

fof(f1287,plain,
    ( spl10_58
    | spl10_40 ),
    inference(avatar_split_clause,[],[f1267,f679,f1284])).

fof(f1284,plain,
    ( spl10_58
  <=> sP1(k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)),k1_tarski(sK5),k1_tarski(k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f1267,plain,
    ( sP1(k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)),k1_tarski(sK5),k1_tarski(k1_tarski(sK5)))
    | spl10_40 ),
    inference(unit_resulting_resolution,[],[f249,f681,f63])).

fof(f1282,plain,
    ( spl10_57
    | spl10_40 ),
    inference(avatar_split_clause,[],[f1277,f679,f1279])).

fof(f1279,plain,
    ( spl10_57
  <=> sP0(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f1277,plain,
    ( sP0(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))
    | spl10_40 ),
    inference(unit_resulting_resolution,[],[f681,f80])).

fof(f80,plain,(
    ! [X2,X1] :
      ( sP0(X1,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f49])).

% (9595)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | X0 != X1
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1262,plain,
    ( spl10_56
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f1253,f625,f1257])).

fof(f1257,plain,
    ( spl10_56
  <=> r2_hidden(sK5,k4_xboole_0(k1_tarski(sK5),k1_tarski(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f1253,plain,
    ( r2_hidden(sK5,k4_xboole_0(k1_tarski(sK5),k1_tarski(sK6)))
    | ~ spl10_36 ),
    inference(resolution,[],[f627,f218])).

fof(f1261,plain,
    ( spl10_56
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f1245,f625,f1257])).

fof(f1245,plain,
    ( r2_hidden(sK5,k4_xboole_0(k1_tarski(sK5),k1_tarski(sK6)))
    | ~ spl10_36 ),
    inference(unit_resulting_resolution,[],[f627,f218])).

fof(f1260,plain,
    ( spl10_56
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f1249,f625,f1257])).

fof(f1249,plain,
    ( r2_hidden(sK5,k4_xboole_0(k1_tarski(sK5),k1_tarski(sK6)))
    | ~ spl10_36 ),
    inference(unit_resulting_resolution,[],[f81,f627,f58])).

fof(f1244,plain,
    ( spl10_55
    | spl10_4
    | ~ spl10_29 ),
    inference(avatar_split_clause,[],[f1236,f571,f119,f1241])).

fof(f1241,plain,
    ( spl10_55
  <=> sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).

fof(f1236,plain,
    ( sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK7)
    | spl10_4
    | ~ spl10_29 ),
    inference(unit_resulting_resolution,[],[f121,f572,f48])).

fof(f572,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7)
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f571])).

fof(f1234,plain,
    ( spl10_54
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f1225,f620,f1229])).

fof(f1229,plain,
    ( spl10_54
  <=> r2_hidden(sK6,k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f620,plain,
    ( spl10_35
  <=> sP1(k1_tarski(sK5),sK6,k1_tarski(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f1225,plain,
    ( r2_hidden(sK6,k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))
    | ~ spl10_35 ),
    inference(resolution,[],[f622,f218])).

fof(f622,plain,
    ( sP1(k1_tarski(sK5),sK6,k1_tarski(sK6))
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f620])).

fof(f1233,plain,
    ( spl10_54
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f1218,f620,f1229])).

fof(f1218,plain,
    ( r2_hidden(sK6,k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f622,f218])).

fof(f1232,plain,
    ( spl10_54
    | ~ spl10_35 ),
    inference(avatar_split_clause,[],[f1221,f620,f1229])).

fof(f1221,plain,
    ( r2_hidden(sK6,k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f81,f622,f58])).

fof(f1217,plain,
    ( ~ spl10_30
    | spl10_20 ),
    inference(avatar_split_clause,[],[f1195,f374,f576])).

fof(f1195,plain,
    ( ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | spl10_20 ),
    inference(unit_resulting_resolution,[],[f81,f375,f57])).

fof(f1216,plain,
    ( ~ spl10_30
    | spl10_20 ),
    inference(avatar_split_clause,[],[f1194,f374,f576])).

fof(f1194,plain,
    ( ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | spl10_20 ),
    inference(unit_resulting_resolution,[],[f375,f206])).

fof(f1215,plain,
    ( spl10_20
    | ~ spl10_30 ),
    inference(avatar_contradiction_clause,[],[f1214])).

fof(f1214,plain,
    ( $false
    | spl10_20
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f1194,f578])).

fof(f1213,plain,
    ( spl10_20
    | ~ spl10_30 ),
    inference(avatar_contradiction_clause,[],[f1212])).

fof(f1212,plain,
    ( $false
    | spl10_20
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f1195,f578])).

fof(f1211,plain,
    ( ~ spl10_53
    | spl10_20 ),
    inference(avatar_split_clause,[],[f1197,f374,f1208])).

fof(f1197,plain,
    ( ~ sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))
    | spl10_20 ),
    inference(unit_resulting_resolution,[],[f249,f375,f57])).

fof(f1188,plain,
    ( spl10_52
    | spl10_10
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f1174,f370,f214,f1185])).

fof(f1185,plain,
    ( spl10_52
  <=> sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK6,k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f1174,plain,
    ( sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK6,k1_tarski(sK5))
    | spl10_10
    | ~ spl10_19 ),
    inference(unit_resulting_resolution,[],[f216,f372,f48])).

fof(f1183,plain,
    ( spl10_26
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f1176,f370,f474])).

fof(f1176,plain,
    ( sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK5,sK5)
    | ~ spl10_19 ),
    inference(unit_resulting_resolution,[],[f103,f372,f67])).

fof(f1182,plain,
    ( spl10_26
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f1172,f370,f474])).

fof(f1172,plain,
    ( sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK5,sK5)
    | ~ spl10_19 ),
    inference(unit_resulting_resolution,[],[f372,f236])).

fof(f236,plain,(
    ! [X8,X7] :
      ( sP3(X7,X8,X8,X8)
      | ~ r2_hidden(X7,k1_tarski(X8)) ) ),
    inference(resolution,[],[f67,f103])).

fof(f1181,plain,
    ( ~ spl10_19
    | spl10_26 ),
    inference(avatar_contradiction_clause,[],[f1180])).

fof(f1180,plain,
    ( $false
    | ~ spl10_19
    | spl10_26 ),
    inference(subsumption_resolution,[],[f1172,f476])).

fof(f1179,plain,
    ( ~ spl10_19
    | spl10_26 ),
    inference(avatar_contradiction_clause,[],[f1178])).

fof(f1178,plain,
    ( $false
    | ~ spl10_19
    | spl10_26 ),
    inference(subsumption_resolution,[],[f1176,f476])).

fof(f1169,plain,
    ( spl10_19
    | spl10_20
    | spl10_3 ),
    inference(avatar_split_clause,[],[f552,f98,f374,f370])).

fof(f552,plain,
    ( sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5))
    | spl10_3 ),
    inference(resolution,[],[f99,f59])).

fof(f1168,plain,
    ( spl10_51
    | ~ spl10_7
    | spl10_29 ),
    inference(avatar_split_clause,[],[f1141,f571,f148,f1165])).

fof(f1165,plain,
    ( spl10_51
  <=> sP0(sK6,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f1141,plain,
    ( sP0(sK6,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7)
    | ~ spl10_7
    | spl10_29 ),
    inference(unit_resulting_resolution,[],[f150,f573,f48])).

fof(f1163,plain,
    ( spl10_50
    | spl10_29 ),
    inference(avatar_split_clause,[],[f1144,f571,f1160])).

fof(f1160,plain,
    ( spl10_50
  <=> sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f1144,plain,
    ( sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))
    | spl10_29 ),
    inference(unit_resulting_resolution,[],[f249,f573,f63])).

fof(f1158,plain,
    ( spl10_49
    | spl10_29 ),
    inference(avatar_split_clause,[],[f1153,f571,f1155])).

fof(f1155,plain,
    ( spl10_49
  <=> sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f1153,plain,
    ( sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7)
    | spl10_29 ),
    inference(unit_resulting_resolution,[],[f573,f80])).

fof(f1139,plain,
    ( spl10_48
    | spl10_27 ),
    inference(avatar_split_clause,[],[f1112,f507,f1136])).

fof(f1136,plain,
    ( spl10_48
  <=> sP0(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f1112,plain,
    ( sP0(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5)))
    | spl10_27 ),
    inference(unit_resulting_resolution,[],[f249,f509,f48])).

fof(f1134,plain,
    ( spl10_47
    | spl10_27 ),
    inference(avatar_split_clause,[],[f1114,f507,f1131])).

fof(f1131,plain,
    ( spl10_47
  <=> sP1(k1_tarski(k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f1114,plain,
    ( sP1(k1_tarski(k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))
    | spl10_27 ),
    inference(unit_resulting_resolution,[],[f249,f509,f63])).

fof(f1129,plain,
    ( spl10_46
    | spl10_27 ),
    inference(avatar_split_clause,[],[f1124,f507,f1126])).

fof(f1126,plain,
    ( spl10_46
  <=> sP0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f1124,plain,
    ( sP0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5)))
    | spl10_27 ),
    inference(unit_resulting_resolution,[],[f509,f80])).

fof(f1001,plain,
    ( spl10_45
    | spl10_4
    | ~ spl10_39 ),
    inference(avatar_split_clause,[],[f980,f650,f119,f998])).

fof(f980,plain,
    ( sP1(sK7,sK5,k4_xboole_0(k1_tarski(sK5),sK7))
    | spl10_4
    | ~ spl10_39 ),
    inference(unit_resulting_resolution,[],[f121,f652,f63])).

fof(f996,plain,
    ( spl10_44
    | spl10_22
    | ~ spl10_39 ),
    inference(avatar_split_clause,[],[f981,f650,f430,f993])).

fof(f993,plain,
    ( spl10_44
  <=> sP1(k1_tarski(sK6),sK5,k4_xboole_0(k1_tarski(sK5),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f981,plain,
    ( sP1(k1_tarski(sK6),sK5,k4_xboole_0(k1_tarski(sK5),sK7))
    | spl10_22
    | ~ spl10_39 ),
    inference(unit_resulting_resolution,[],[f432,f652,f63])).

fof(f991,plain,
    ( spl10_43
    | ~ spl10_7
    | ~ spl10_39 ),
    inference(avatar_split_clause,[],[f983,f650,f148,f988])).

fof(f988,plain,
    ( spl10_43
  <=> sP0(sK5,sK6,k4_xboole_0(k1_tarski(sK5),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f983,plain,
    ( sP0(sK5,sK6,k4_xboole_0(k1_tarski(sK5),sK7))
    | ~ spl10_7
    | ~ spl10_39 ),
    inference(unit_resulting_resolution,[],[f547,f652,f48])).

fof(f789,plain,
    ( spl10_42
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f780,f289,f786])).

fof(f780,plain,
    ( r2_hidden(sK6,k4_xboole_0(sK7,k1_tarski(sK5)))
    | ~ spl10_15 ),
    inference(unit_resulting_resolution,[],[f81,f291,f58])).

fof(f692,plain,
    ( ~ spl10_41
    | spl10_18 ),
    inference(avatar_split_clause,[],[f674,f336,f689])).

fof(f674,plain,
    ( ~ sP4(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5)))
    | spl10_18 ),
    inference(unit_resulting_resolution,[],[f249,f338,f67])).

fof(f338,plain,
    ( ~ sP3(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | spl10_18 ),
    inference(avatar_component_clause,[],[f336])).

fof(f687,plain,
    ( ~ spl10_40
    | spl10_18 ),
    inference(avatar_split_clause,[],[f686,f336,f679])).

fof(f686,plain,
    ( ~ r2_hidden(k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))
    | spl10_18 ),
    inference(forward_demodulation,[],[f685,f52])).

fof(f685,plain,
    ( ~ r2_hidden(k1_tarski(sK5),k2_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7)))
    | spl10_18 ),
    inference(forward_demodulation,[],[f675,f54])).

fof(f675,plain,
    ( ~ r2_hidden(k1_tarski(sK5),k1_enumset1(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7)))
    | spl10_18 ),
    inference(unit_resulting_resolution,[],[f85,f338,f67])).

fof(f684,plain,
    ( ~ spl10_40
    | spl10_18 ),
    inference(avatar_split_clause,[],[f683,f336,f679])).

fof(f683,plain,
    ( ~ r2_hidden(k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))
    | spl10_18 ),
    inference(forward_demodulation,[],[f676,f52])).

fof(f676,plain,
    ( ~ r2_hidden(k1_tarski(sK5),k2_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7)))
    | spl10_18 ),
    inference(unit_resulting_resolution,[],[f102,f338,f67])).

fof(f682,plain,
    ( ~ spl10_40
    | spl10_18 ),
    inference(avatar_split_clause,[],[f677,f336,f679])).

fof(f677,plain,
    ( ~ r2_hidden(k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))
    | spl10_18 ),
    inference(unit_resulting_resolution,[],[f103,f338,f67])).

fof(f653,plain,
    ( spl10_39
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f644,f630,f650])).

fof(f644,plain,
    ( r2_hidden(sK5,k4_xboole_0(k1_tarski(sK5),sK7))
    | ~ spl10_37 ),
    inference(unit_resulting_resolution,[],[f81,f632,f58])).

fof(f641,plain,
    ( ~ spl10_19
    | spl10_3
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f557,f374,f98,f370])).

fof(f557,plain,
    ( ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5))
    | spl10_3
    | ~ spl10_20 ),
    inference(unit_resulting_resolution,[],[f99,f376,f60])).

fof(f376,plain,
    ( sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f374])).

fof(f640,plain,
    ( ~ spl10_19
    | spl10_3
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f639,f374,f98,f370])).

fof(f639,plain,
    ( ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5))
    | spl10_3
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f562,f99])).

fof(f562,plain,
    ( sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))
    | ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5))
    | ~ spl10_20 ),
    inference(resolution,[],[f376,f60])).

fof(f638,plain,
    ( ~ spl10_38
    | spl10_17 ),
    inference(avatar_split_clause,[],[f585,f329,f635])).

fof(f585,plain,
    ( ~ sP4(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))
    | spl10_17 ),
    inference(unit_resulting_resolution,[],[f331,f249,f67])).

fof(f331,plain,
    ( ~ sP3(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5))
    | spl10_17 ),
    inference(avatar_component_clause,[],[f329])).

fof(f633,plain,
    ( spl10_37
    | spl10_4 ),
    inference(avatar_split_clause,[],[f589,f119,f630])).

fof(f589,plain,
    ( sP1(sK7,sK5,k1_tarski(sK5))
    | spl10_4 ),
    inference(unit_resulting_resolution,[],[f121,f249,f63])).

fof(f628,plain,
    ( spl10_36
    | spl10_22 ),
    inference(avatar_split_clause,[],[f590,f430,f625])).

fof(f590,plain,
    ( sP1(k1_tarski(sK6),sK5,k1_tarski(sK5))
    | spl10_22 ),
    inference(unit_resulting_resolution,[],[f432,f249,f63])).

fof(f623,plain,
    ( spl10_35
    | spl10_10 ),
    inference(avatar_split_clause,[],[f591,f214,f620])).

fof(f591,plain,
    ( sP1(k1_tarski(sK5),sK6,k1_tarski(sK6))
    | spl10_10 ),
    inference(unit_resulting_resolution,[],[f216,f249,f63])).

fof(f618,plain,
    ( spl10_34
    | spl10_19 ),
    inference(avatar_split_clause,[],[f592,f370,f615])).

fof(f592,plain,
    ( sP1(k1_tarski(sK5),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))
    | spl10_19 ),
    inference(unit_resulting_resolution,[],[f371,f249,f63])).

fof(f613,plain,
    ( spl10_33
    | spl10_22 ),
    inference(avatar_split_clause,[],[f594,f430,f610])).

fof(f610,plain,
    ( spl10_33
  <=> sP0(sK6,sK5,k1_tarski(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f594,plain,
    ( sP0(sK6,sK5,k1_tarski(sK6))
    | spl10_22 ),
    inference(unit_resulting_resolution,[],[f432,f249,f48])).

fof(f608,plain,
    ( spl10_32
    | spl10_10 ),
    inference(avatar_split_clause,[],[f595,f214,f605])).

fof(f605,plain,
    ( spl10_32
  <=> sP0(sK5,sK6,k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f595,plain,
    ( sP0(sK5,sK6,k1_tarski(sK5))
    | spl10_10 ),
    inference(unit_resulting_resolution,[],[f216,f249,f48])).

fof(f603,plain,
    ( spl10_31
    | spl10_19 ),
    inference(avatar_split_clause,[],[f596,f370,f600])).

fof(f600,plain,
    ( spl10_31
  <=> sP0(sK5,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f596,plain,
    ( sP0(sK5,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5))
    | spl10_19 ),
    inference(unit_resulting_resolution,[],[f371,f249,f48])).

fof(f581,plain,
    ( spl10_28
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f564,f374,f566])).

fof(f564,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | ~ spl10_20 ),
    inference(resolution,[],[f376,f61])).

fof(f580,plain,
    ( ~ spl10_29
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f563,f374,f571])).

fof(f563,plain,
    ( ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7)
    | ~ spl10_20 ),
    inference(resolution,[],[f376,f62])).

fof(f579,plain,
    ( spl10_30
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f558,f374,f576])).

fof(f558,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | ~ spl10_20 ),
    inference(unit_resulting_resolution,[],[f81,f376,f58])).

fof(f574,plain,
    ( ~ spl10_29
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f560,f374,f571])).

fof(f560,plain,
    ( ~ r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7)
    | ~ spl10_20 ),
    inference(unit_resulting_resolution,[],[f376,f62])).

fof(f569,plain,
    ( spl10_28
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f561,f374,f566])).

fof(f561,plain,
    ( r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | ~ spl10_20 ),
    inference(unit_resulting_resolution,[],[f376,f61])).

fof(f514,plain,
    ( ~ spl10_7
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f389,f162,f148])).

fof(f162,plain,
    ( spl10_9
  <=> sP0(sK6,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f389,plain,
    ( ~ r2_hidden(sK6,sK7)
    | ~ spl10_9 ),
    inference(unit_resulting_resolution,[],[f164,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f164,plain,
    ( sP0(sK6,sK6,sK7)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f162])).

fof(f513,plain,
    ( ~ spl10_7
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f391,f162,f148])).

fof(f391,plain,
    ( ~ r2_hidden(sK6,sK7)
    | ~ spl10_9 ),
    inference(resolution,[],[f164,f46])).

fof(f512,plain,
    ( ~ spl10_27
    | spl10_17 ),
    inference(avatar_split_clause,[],[f490,f329,f507])).

fof(f490,plain,
    ( ~ r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5)))
    | spl10_17 ),
    inference(unit_resulting_resolution,[],[f103,f331,f67])).

fof(f511,plain,
    ( ~ spl10_27
    | spl10_17 ),
    inference(avatar_split_clause,[],[f495,f329,f507])).

fof(f495,plain,
    ( ~ r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5)))
    | spl10_17 ),
    inference(forward_demodulation,[],[f489,f52])).

fof(f489,plain,
    ( ~ r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k2_tarski(k1_tarski(sK5),k1_tarski(sK5)))
    | spl10_17 ),
    inference(unit_resulting_resolution,[],[f102,f331,f67])).

fof(f510,plain,
    ( ~ spl10_27
    | spl10_17 ),
    inference(avatar_split_clause,[],[f500,f329,f507])).

fof(f500,plain,
    ( ~ r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5)))
    | spl10_17 ),
    inference(forward_demodulation,[],[f499,f52])).

fof(f499,plain,
    ( ~ r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k2_tarski(k1_tarski(sK5),k1_tarski(sK5)))
    | spl10_17 ),
    inference(forward_demodulation,[],[f488,f54])).

fof(f488,plain,
    ( ~ r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_enumset1(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5)))
    | spl10_17 ),
    inference(unit_resulting_resolution,[],[f85,f331,f67])).

fof(f505,plain,
    ( ~ spl10_1
    | spl10_17 ),
    inference(avatar_contradiction_clause,[],[f504])).

fof(f504,plain,
    ( $false
    | ~ spl10_1
    | spl10_17 ),
    inference(subsumption_resolution,[],[f491,f82])).

fof(f491,plain,
    ( ~ sP3(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5))
    | ~ spl10_1
    | spl10_17 ),
    inference(superposition,[],[f331,f88])).

fof(f88,plain,
    ( k1_tarski(sK5) = k4_xboole_0(k2_tarski(sK5,sK6),sK7)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl10_1
  <=> k1_tarski(sK5) = k4_xboole_0(k2_tarski(sK5,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f503,plain,
    ( ~ spl10_1
    | spl10_17 ),
    inference(avatar_contradiction_clause,[],[f502])).

fof(f502,plain,
    ( $false
    | ~ spl10_1
    | spl10_17 ),
    inference(subsumption_resolution,[],[f501,f249])).

fof(f501,plain,
    ( ~ r2_hidden(k1_tarski(sK5),k1_tarski(k1_tarski(sK5)))
    | ~ spl10_1
    | spl10_17 ),
    inference(forward_demodulation,[],[f500,f88])).

fof(f498,plain,
    ( ~ spl10_1
    | spl10_17 ),
    inference(avatar_contradiction_clause,[],[f497])).

fof(f497,plain,
    ( $false
    | ~ spl10_1
    | spl10_17 ),
    inference(subsumption_resolution,[],[f496,f249])).

fof(f496,plain,
    ( ~ r2_hidden(k1_tarski(sK5),k1_tarski(k1_tarski(sK5)))
    | ~ spl10_1
    | spl10_17 ),
    inference(forward_demodulation,[],[f495,f88])).

fof(f494,plain,
    ( ~ spl10_1
    | spl10_17 ),
    inference(avatar_contradiction_clause,[],[f493])).

fof(f493,plain,
    ( $false
    | ~ spl10_1
    | spl10_17 ),
    inference(subsumption_resolution,[],[f492,f249])).

fof(f492,plain,
    ( ~ r2_hidden(k1_tarski(sK5),k1_tarski(k1_tarski(sK5)))
    | ~ spl10_1
    | spl10_17 ),
    inference(forward_demodulation,[],[f490,f88])).

fof(f477,plain,
    ( ~ spl10_26
    | spl10_19 ),
    inference(avatar_split_clause,[],[f463,f370,f474])).

fof(f463,plain,
    ( ~ sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK5,sK5)
    | spl10_19 ),
    inference(unit_resulting_resolution,[],[f103,f371,f68])).

fof(f472,plain,
    ( spl10_25
    | spl10_19 ),
    inference(avatar_split_clause,[],[f467,f370,f469])).

fof(f469,plain,
    ( spl10_25
  <=> sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f467,plain,
    ( sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5))
    | spl10_19 ),
    inference(unit_resulting_resolution,[],[f371,f80])).

fof(f459,plain,
    ( ~ spl10_24
    | spl10_6
    | spl10_22 ),
    inference(avatar_split_clause,[],[f442,f430,f144,f456])).

fof(f456,plain,
    ( spl10_24
  <=> sP0(sK5,sK6,k1_tarski(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f144,plain,
    ( spl10_6
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f442,plain,
    ( ~ sP0(sK5,sK6,k1_tarski(sK6))
    | spl10_6
    | spl10_22 ),
    inference(unit_resulting_resolution,[],[f145,f432,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X0,X2)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f145,plain,
    ( sK5 != sK6
    | spl10_6 ),
    inference(avatar_component_clause,[],[f144])).

fof(f454,plain,
    ( spl10_23
    | spl10_22 ),
    inference(avatar_split_clause,[],[f449,f430,f451])).

fof(f451,plain,
    ( spl10_23
  <=> sP0(sK5,sK5,k1_tarski(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f449,plain,
    ( sP0(sK5,sK5,k1_tarski(sK6))
    | spl10_22 ),
    inference(unit_resulting_resolution,[],[f432,f80])).

fof(f438,plain,
    ( ~ spl10_22
    | spl10_13 ),
    inference(avatar_split_clause,[],[f437,f270,f430])).

fof(f270,plain,
    ( spl10_13
  <=> sP3(sK5,sK6,sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f437,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK6))
    | spl10_13 ),
    inference(forward_demodulation,[],[f436,f52])).

fof(f436,plain,
    ( ~ r2_hidden(sK5,k2_tarski(sK6,sK6))
    | spl10_13 ),
    inference(forward_demodulation,[],[f426,f54])).

fof(f426,plain,
    ( ~ r2_hidden(sK5,k1_enumset1(sK6,sK6,sK6))
    | spl10_13 ),
    inference(unit_resulting_resolution,[],[f85,f272,f67])).

fof(f272,plain,
    ( ~ sP3(sK5,sK6,sK6,sK6)
    | spl10_13 ),
    inference(avatar_component_clause,[],[f270])).

fof(f435,plain,
    ( ~ spl10_22
    | spl10_13 ),
    inference(avatar_split_clause,[],[f434,f270,f430])).

fof(f434,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK6))
    | spl10_13 ),
    inference(forward_demodulation,[],[f427,f52])).

fof(f427,plain,
    ( ~ r2_hidden(sK5,k2_tarski(sK6,sK6))
    | spl10_13 ),
    inference(unit_resulting_resolution,[],[f102,f272,f67])).

fof(f433,plain,
    ( ~ spl10_22
    | spl10_13 ),
    inference(avatar_split_clause,[],[f428,f270,f430])).

fof(f428,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK6))
    | spl10_13 ),
    inference(unit_resulting_resolution,[],[f103,f272,f67])).

fof(f418,plain,(
    spl10_11 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | spl10_11 ),
    inference(subsumption_resolution,[],[f413,f82])).

fof(f413,plain,
    ( ~ sP3(sK5,sK5,sK5,sK5)
    | spl10_11 ),
    inference(unit_resulting_resolution,[],[f103,f232,f68])).

fof(f232,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | spl10_11 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl10_11
  <=> r2_hidden(sK5,k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f416,plain,(
    spl10_11 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | spl10_11 ),
    inference(unit_resulting_resolution,[],[f82,f103,f232,f68])).

fof(f405,plain,
    ( ~ spl10_21
    | ~ spl10_3
    | spl10_10 ),
    inference(avatar_split_clause,[],[f396,f214,f98,f402])).

fof(f396,plain,
    ( ~ sP1(sK7,sK6,k2_tarski(sK5,sK6))
    | ~ spl10_3
    | spl10_10 ),
    inference(unit_resulting_resolution,[],[f216,f100,f58])).

fof(f100,plain,
    ( sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f378,plain,
    ( ~ spl10_3
    | spl10_1 ),
    inference(avatar_split_clause,[],[f318,f87,f98])).

fof(f318,plain,
    ( ~ sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f89,f65])).

fof(f89,plain,
    ( k1_tarski(sK5) != k4_xboole_0(k2_tarski(sK5,sK6),sK7)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f377,plain,
    ( spl10_19
    | spl10_20
    | spl10_3 ),
    inference(avatar_split_clause,[],[f368,f98,f374,f370])).

fof(f368,plain,
    ( sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))
    | r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5))
    | spl10_3 ),
    inference(resolution,[],[f59,f99])).

fof(f355,plain,
    ( ~ spl10_10
    | spl10_12 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | ~ spl10_10
    | spl10_12 ),
    inference(subsumption_resolution,[],[f349,f267])).

fof(f267,plain,
    ( ~ sP3(sK6,sK5,sK5,sK5)
    | spl10_12 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl10_12
  <=> sP3(sK6,sK5,sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f349,plain,
    ( sP3(sK6,sK5,sK5,sK5)
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f103,f215,f67])).

fof(f215,plain,
    ( r2_hidden(sK6,k1_tarski(sK5))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f214])).

fof(f341,plain,
    ( ~ spl10_18
    | spl10_1 ),
    inference(avatar_split_clause,[],[f309,f87,f336])).

fof(f309,plain,
    ( ~ sP3(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f89,f89,f89,f71])).

fof(f340,plain,
    ( ~ spl10_18
    | spl10_1 ),
    inference(avatar_split_clause,[],[f312,f87,f336])).

fof(f312,plain,
    ( ~ sP3(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f89,f89,f89,f71])).

fof(f339,plain,
    ( ~ spl10_18
    | spl10_1 ),
    inference(avatar_split_clause,[],[f315,f87,f336])).

fof(f315,plain,
    ( ~ sP3(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f89,f89,f89,f71])).

fof(f334,plain,
    ( ~ spl10_17
    | spl10_1 ),
    inference(avatar_split_clause,[],[f319,f87,f329])).

fof(f319,plain,
    ( ~ sP3(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f89,f89,f89,f71])).

fof(f333,plain,
    ( ~ spl10_17
    | spl10_1 ),
    inference(avatar_split_clause,[],[f322,f87,f329])).

fof(f322,plain,
    ( ~ sP3(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f89,f89,f89,f71])).

fof(f332,plain,
    ( ~ spl10_17
    | spl10_1 ),
    inference(avatar_split_clause,[],[f325,f87,f329])).

fof(f325,plain,
    ( ~ sP3(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f89,f89,f89,f71])).

fof(f297,plain,
    ( ~ spl10_16
    | spl10_6
    | spl10_10 ),
    inference(avatar_split_clause,[],[f274,f214,f144,f294])).

fof(f294,plain,
    ( spl10_16
  <=> sP0(sK6,sK5,k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f274,plain,
    ( ~ sP0(sK6,sK5,k1_tarski(sK5))
    | spl10_6
    | spl10_10 ),
    inference(unit_resulting_resolution,[],[f145,f216,f47])).

fof(f292,plain,
    ( spl10_15
    | ~ spl10_7
    | spl10_10 ),
    inference(avatar_split_clause,[],[f277,f214,f148,f289])).

fof(f277,plain,
    ( sP1(k1_tarski(sK5),sK6,sK7)
    | ~ spl10_7
    | spl10_10 ),
    inference(unit_resulting_resolution,[],[f150,f216,f63])).

fof(f287,plain,
    ( spl10_14
    | spl10_10 ),
    inference(avatar_split_clause,[],[f282,f214,f284])).

fof(f284,plain,
    ( spl10_14
  <=> sP0(sK6,sK6,k1_tarski(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f282,plain,
    ( sP0(sK6,sK6,k1_tarski(sK5))
    | spl10_10 ),
    inference(unit_resulting_resolution,[],[f216,f80])).

fof(f273,plain,
    ( ~ spl10_13
    | spl10_6 ),
    inference(avatar_split_clause,[],[f253,f144,f270])).

fof(f253,plain,
    ( ~ sP3(sK5,sK6,sK6,sK6)
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f145,f145,f145,f71])).

fof(f268,plain,
    ( ~ spl10_12
    | spl10_6 ),
    inference(avatar_split_clause,[],[f254,f144,f265])).

fof(f254,plain,
    ( ~ sP3(sK6,sK5,sK5,sK5)
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f145,f145,f145,f71])).

fof(f233,plain,
    ( ~ spl10_11
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f225,f119,f98,f230])).

fof(f225,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f100,f194,f57])).

fof(f194,plain,
    ( ! [X0] : ~ sP1(sK7,sK5,X0)
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f120,f62])).

fof(f120,plain,
    ( r2_hidden(sK5,sK7)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f217,plain,
    ( ~ spl10_10
    | ~ spl10_3
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f209,f148,f98,f214])).

fof(f209,plain,
    ( ~ r2_hidden(sK6,k1_tarski(sK5))
    | ~ spl10_3
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f100,f167,f57])).

fof(f167,plain,
    ( ! [X0] : ~ sP1(sK7,sK6,X0)
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f150,f62])).

fof(f192,plain,
    ( ~ spl10_4
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f132,f128,f119])).

fof(f128,plain,
    ( spl10_5
  <=> sP0(sK5,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f132,plain,
    ( ~ r2_hidden(sK5,sK7)
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f130,f46])).

fof(f130,plain,
    ( sP0(sK5,sK5,sK7)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f191,plain,
    ( ~ spl10_4
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f133,f128,f119])).

fof(f133,plain,
    ( ~ r2_hidden(sK5,sK7)
    | ~ spl10_5 ),
    inference(resolution,[],[f130,f46])).

fof(f190,plain,
    ( spl10_4
    | spl10_2
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f173,f148,f91,f119])).

fof(f91,plain,
    ( spl10_2
  <=> sP0(sK6,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f173,plain,
    ( r2_hidden(sK5,sK7)
    | spl10_2
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f150,f93,f48])).

fof(f93,plain,
    ( ~ sP0(sK6,sK5,sK7)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f189,plain,
    ( spl10_4
    | spl10_2
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f186,f148,f91,f119])).

fof(f186,plain,
    ( r2_hidden(sK5,sK7)
    | spl10_2
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f177,f150])).

fof(f177,plain,
    ( ~ r2_hidden(sK6,sK7)
    | r2_hidden(sK5,sK7)
    | spl10_2 ),
    inference(resolution,[],[f48,f93])).

fof(f188,plain,
    ( spl10_2
    | spl10_4
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl10_2
    | spl10_4
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f186,f121])).

fof(f185,plain,
    ( spl10_2
    | spl10_4
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl10_2
    | spl10_4
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f171,f93])).

fof(f171,plain,
    ( sP0(sK6,sK5,sK7)
    | spl10_4
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f121,f150,f48])).

fof(f183,plain,
    ( spl10_2
    | spl10_4
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl10_2
    | spl10_4
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f172,f150])).

fof(f172,plain,
    ( ~ r2_hidden(sK6,sK7)
    | spl10_2
    | spl10_4 ),
    inference(unit_resulting_resolution,[],[f121,f93,f48])).

fof(f181,plain,
    ( spl10_2
    | spl10_4
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl10_2
    | spl10_4
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f173,f121])).

fof(f179,plain,
    ( spl10_2
    | spl10_4
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl10_2
    | spl10_4
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f121,f150,f93,f48])).

fof(f165,plain,
    ( spl10_9
    | spl10_7 ),
    inference(avatar_split_clause,[],[f159,f148,f162])).

fof(f159,plain,
    ( sP0(sK6,sK6,sK7)
    | spl10_7 ),
    inference(unit_resulting_resolution,[],[f149,f80])).

fof(f149,plain,
    ( ~ r2_hidden(sK6,sK7)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f148])).

fof(f157,plain,
    ( ~ spl10_8
    | spl10_4
    | spl10_6 ),
    inference(avatar_split_clause,[],[f152,f144,f119,f154])).

fof(f154,plain,
    ( spl10_8
  <=> sP0(sK5,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f152,plain,
    ( ~ sP0(sK5,sK6,sK7)
    | spl10_4
    | spl10_6 ),
    inference(unit_resulting_resolution,[],[f121,f145,f47])).

fof(f151,plain,
    ( spl10_6
    | spl10_7
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f139,f91,f148,f144])).

fof(f139,plain,
    ( r2_hidden(sK6,sK7)
    | sK5 = sK6
    | ~ spl10_2 ),
    inference(resolution,[],[f47,f92])).

fof(f92,plain,
    ( sP0(sK6,sK5,sK7)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f131,plain,
    ( spl10_5
    | spl10_4 ),
    inference(avatar_split_clause,[],[f125,f119,f128])).

fof(f125,plain,
    ( sP0(sK5,sK5,sK7)
    | spl10_4 ),
    inference(unit_resulting_resolution,[],[f121,f80])).

fof(f123,plain,
    ( ~ spl10_4
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f117,f91,f119])).

fof(f117,plain,
    ( ~ r2_hidden(sK5,sK7)
    | ~ spl10_2 ),
    inference(resolution,[],[f46,f92])).

fof(f122,plain,
    ( ~ spl10_4
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f116,f91,f119])).

fof(f116,plain,
    ( ~ r2_hidden(sK5,sK7)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f92,f46])).

fof(f101,plain,
    ( spl10_3
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f96,f87,f98])).

fof(f96,plain,
    ( sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))
    | ~ spl10_1 ),
    inference(superposition,[],[f81,f88])).

fof(f95,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f50,f91,f87])).

fof(f50,plain,
    ( sP0(sK6,sK5,sK7)
    | k1_tarski(sK5) = k4_xboole_0(k2_tarski(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ sP0(sK6,sK5,sK7)
      | k1_tarski(sK5) != k4_xboole_0(k2_tarski(sK5,sK6),sK7) )
    & ( sP0(sK6,sK5,sK7)
      | k1_tarski(sK5) = k4_xboole_0(k2_tarski(sK5,sK6),sK7) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ sP0(X1,X0,X2)
          | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( sP0(X1,X0,X2)
          | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ sP0(sK6,sK5,sK7)
        | k1_tarski(sK5) != k4_xboole_0(k2_tarski(sK5,sK6),sK7) )
      & ( sP0(sK6,sK5,sK7)
        | k1_tarski(sK5) = k4_xboole_0(k2_tarski(sK5,sK6),sK7) ) ) ),
    introduced(choice_axiom,[])).

% (9595)Refutation not found, incomplete strategy% (9595)------------------------------
% (9595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9595)Termination reason: Refutation not found, incomplete strategy

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ sP0(X1,X0,X2)
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( sP0(X1,X0,X2)
        | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

% (9595)Memory used [KB]: 6140
% (9595)Time elapsed: 0.095 s
% (9595)------------------------------
% (9595)------------------------------
fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f14,f16])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_zfmisc_1)).

fof(f94,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f51,f91,f87])).

fof(f51,plain,
    ( ~ sP0(sK6,sK5,sK7)
    | k1_tarski(sK5) != k4_xboole_0(k2_tarski(sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:39:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (9316)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (9330)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (9324)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (9318)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (9319)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (9319)Refutation not found, incomplete strategy% (9319)------------------------------
% 0.21/0.52  % (9319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9319)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9319)Memory used [KB]: 10746
% 0.21/0.52  % (9319)Time elapsed: 0.116 s
% 0.21/0.52  % (9319)------------------------------
% 0.21/0.52  % (9319)------------------------------
% 0.21/0.52  % (9321)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (9314)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (9312)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (9310)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (9312)Refutation not found, incomplete strategy% (9312)------------------------------
% 0.21/0.52  % (9312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9312)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9312)Memory used [KB]: 10746
% 0.21/0.52  % (9312)Time elapsed: 0.114 s
% 0.21/0.52  % (9312)------------------------------
% 0.21/0.52  % (9312)------------------------------
% 0.21/0.53  % (9328)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (9333)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (9328)Refutation not found, incomplete strategy% (9328)------------------------------
% 0.21/0.53  % (9328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9328)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9328)Memory used [KB]: 10746
% 0.21/0.53  % (9328)Time elapsed: 0.125 s
% 0.21/0.53  % (9328)------------------------------
% 0.21/0.53  % (9328)------------------------------
% 0.21/0.53  % (9329)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (9339)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (9336)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (9325)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (9315)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (9311)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (9332)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (9327)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (9320)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (9322)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (9337)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (9317)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (9335)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (9341)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (9338)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (9331)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.56  % (9334)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.51/0.56  % (9326)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.56  % (9323)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.26/0.66  % (9362)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.26/0.68  % (9365)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.26/0.72  % (9370)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.18/0.84  % (9316)Time limit reached!
% 3.18/0.84  % (9316)------------------------------
% 3.18/0.84  % (9316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.73/0.86  % (9316)Termination reason: Time limit
% 3.73/0.86  
% 3.73/0.86  % (9316)Memory used [KB]: 9083
% 3.73/0.86  % (9316)Time elapsed: 0.435 s
% 3.73/0.86  % (9316)------------------------------
% 3.73/0.86  % (9316)------------------------------
% 3.97/0.92  % (9321)Time limit reached!
% 3.97/0.92  % (9321)------------------------------
% 3.97/0.92  % (9321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/0.92  % (9310)Time limit reached!
% 3.97/0.92  % (9310)------------------------------
% 3.97/0.92  % (9310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/0.92  % (9310)Termination reason: Time limit
% 3.97/0.92  
% 3.97/0.92  % (9310)Memory used [KB]: 2942
% 3.97/0.92  % (9310)Time elapsed: 0.517 s
% 3.97/0.92  % (9310)------------------------------
% 3.97/0.92  % (9310)------------------------------
% 4.41/0.93  % (9321)Termination reason: Time limit
% 4.41/0.93  
% 4.41/0.93  % (9321)Memory used [KB]: 13432
% 4.41/0.93  % (9321)Time elapsed: 0.515 s
% 4.41/0.93  % (9321)------------------------------
% 4.41/0.93  % (9321)------------------------------
% 4.41/0.93  % (9311)Time limit reached!
% 4.41/0.93  % (9311)------------------------------
% 4.41/0.93  % (9311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.93  % (9311)Termination reason: Time limit
% 4.41/0.93  
% 4.41/0.93  % (9311)Memory used [KB]: 8315
% 4.41/0.93  % (9311)Time elapsed: 0.519 s
% 4.41/0.93  % (9311)------------------------------
% 4.41/0.93  % (9311)------------------------------
% 4.41/0.93  % (9323)Time limit reached!
% 4.41/0.93  % (9323)------------------------------
% 4.41/0.93  % (9323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.93  % (9323)Termination reason: Time limit
% 4.41/0.93  
% 4.41/0.93  % (9323)Memory used [KB]: 8571
% 4.41/0.93  % (9323)Time elapsed: 0.523 s
% 4.41/0.93  % (9323)------------------------------
% 4.41/0.93  % (9323)------------------------------
% 4.58/0.97  % (9507)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.58/1.00  % (9327)Time limit reached!
% 4.58/1.00  % (9327)------------------------------
% 4.58/1.00  % (9327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/1.01  % (9339)Time limit reached!
% 4.58/1.01  % (9339)------------------------------
% 4.58/1.01  % (9339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/1.01  % (9339)Termination reason: Time limit
% 4.58/1.01  % (9339)Termination phase: Saturation
% 4.58/1.01  
% 4.58/1.01  % (9339)Memory used [KB]: 8827
% 4.58/1.01  % (9339)Time elapsed: 0.600 s
% 4.58/1.01  % (9339)------------------------------
% 4.58/1.01  % (9339)------------------------------
% 4.58/1.02  % (9327)Termination reason: Time limit
% 4.58/1.02  % (9327)Termination phase: Saturation
% 4.58/1.02  
% 4.58/1.02  % (9327)Memory used [KB]: 16247
% 4.58/1.02  % (9327)Time elapsed: 0.600 s
% 4.58/1.02  % (9327)------------------------------
% 4.58/1.02  % (9327)------------------------------
% 5.10/1.02  % (9524)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.10/1.02  % (9318)Time limit reached!
% 5.10/1.02  % (9318)------------------------------
% 5.10/1.02  % (9318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.10/1.02  % (9318)Termination reason: Time limit
% 5.10/1.02  % (9318)Termination phase: Saturation
% 5.10/1.02  
% 5.10/1.02  % (9318)Memory used [KB]: 13432
% 5.10/1.02  % (9318)Time elapsed: 0.600 s
% 5.10/1.02  % (9318)------------------------------
% 5.10/1.02  % (9318)------------------------------
% 5.10/1.06  % (9532)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.10/1.06  % (9528)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.10/1.06  % (9527)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.58/1.12  % (9566)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.58/1.12  % (9566)Refutation not found, incomplete strategy% (9566)------------------------------
% 5.58/1.12  % (9566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.58/1.12  % (9566)Termination reason: Refutation not found, incomplete strategy
% 5.58/1.12  
% 5.58/1.12  % (9566)Memory used [KB]: 1791
% 5.58/1.12  % (9566)Time elapsed: 0.059 s
% 5.58/1.12  % (9566)------------------------------
% 5.58/1.12  % (9566)------------------------------
% 5.58/1.13  % (9575)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 5.58/1.14  % (9570)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.77/1.23  % (9332)Time limit reached!
% 6.77/1.23  % (9332)------------------------------
% 6.77/1.23  % (9332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.77/1.23  % (9581)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.90/1.25  % (9332)Termination reason: Time limit
% 6.90/1.25  
% 6.90/1.25  % (9332)Memory used [KB]: 3965
% 6.90/1.25  % (9332)Time elapsed: 0.824 s
% 6.90/1.25  % (9332)------------------------------
% 6.90/1.25  % (9332)------------------------------
% 7.40/1.31  % (9507)Time limit reached!
% 7.40/1.31  % (9507)------------------------------
% 7.40/1.31  % (9507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.40/1.32  % (9507)Termination reason: Time limit
% 7.40/1.32  
% 7.40/1.32  % (9507)Memory used [KB]: 8443
% 7.40/1.32  % (9507)Time elapsed: 0.419 s
% 7.40/1.32  % (9507)------------------------------
% 7.40/1.32  % (9507)------------------------------
% 7.40/1.37  % (9582)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 7.85/1.37  % (9524)Time limit reached!
% 7.85/1.37  % (9524)------------------------------
% 7.85/1.37  % (9524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.85/1.38  % (9524)Termination reason: Time limit
% 7.85/1.38  % (9524)Termination phase: Saturation
% 7.85/1.38  
% 7.85/1.38  % (9524)Memory used [KB]: 15863
% 7.85/1.38  % (9524)Time elapsed: 0.400 s
% 7.85/1.38  % (9524)------------------------------
% 7.85/1.38  % (9524)------------------------------
% 7.85/1.45  % (9583)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 7.85/1.45  % (9583)Refutation not found, incomplete strategy% (9583)------------------------------
% 7.85/1.45  % (9583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.85/1.45  % (9583)Termination reason: Refutation not found, incomplete strategy
% 7.85/1.45  
% 7.85/1.45  % (9583)Memory used [KB]: 1663
% 7.85/1.45  % (9583)Time elapsed: 0.104 s
% 7.85/1.45  % (9583)------------------------------
% 7.85/1.45  % (9583)------------------------------
% 8.64/1.49  % (9584)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 9.06/1.57  % (9585)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 9.06/1.61  % (9337)Time limit reached!
% 9.06/1.61  % (9337)------------------------------
% 9.06/1.61  % (9337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.06/1.62  % (9337)Termination reason: Time limit
% 9.06/1.62  
% 9.06/1.62  % (9337)Memory used [KB]: 16247
% 9.06/1.62  % (9337)Time elapsed: 1.218 s
% 9.06/1.62  % (9337)------------------------------
% 9.06/1.62  % (9337)------------------------------
% 9.94/1.65  % (9333)Time limit reached!
% 9.94/1.65  % (9333)------------------------------
% 9.94/1.65  % (9333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.94/1.67  % (9333)Termination reason: Time limit
% 9.94/1.67  
% 9.94/1.67  % (9333)Memory used [KB]: 16630
% 9.94/1.67  % (9333)Time elapsed: 1.215 s
% 9.94/1.67  % (9333)------------------------------
% 9.94/1.67  % (9333)------------------------------
% 10.37/1.72  % (9326)Time limit reached!
% 10.37/1.72  % (9326)------------------------------
% 10.37/1.72  % (9326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.37/1.74  % (9326)Termination reason: Time limit
% 10.37/1.74  
% 10.37/1.74  % (9326)Memory used [KB]: 18293
% 10.37/1.74  % (9326)Time elapsed: 1.327 s
% 10.37/1.74  % (9326)------------------------------
% 10.37/1.74  % (9326)------------------------------
% 10.37/1.74  % (9335)Time limit reached!
% 10.37/1.74  % (9335)------------------------------
% 10.37/1.74  % (9335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.37/1.74  % (9586)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 10.37/1.75  % (9335)Termination reason: Time limit
% 10.37/1.75  
% 10.37/1.75  % (9335)Memory used [KB]: 12920
% 10.37/1.75  % (9335)Time elapsed: 1.330 s
% 10.37/1.75  % (9335)------------------------------
% 10.37/1.75  % (9335)------------------------------
% 11.16/1.79  % (9582)Time limit reached!
% 11.16/1.79  % (9582)------------------------------
% 11.16/1.79  % (9582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.16/1.79  % (9582)Termination reason: Time limit
% 11.16/1.79  % (9582)Termination phase: Saturation
% 11.16/1.79  
% 11.16/1.79  % (9582)Memory used [KB]: 3837
% 11.16/1.79  % (9582)Time elapsed: 0.500 s
% 11.16/1.79  % (9582)------------------------------
% 11.16/1.79  % (9582)------------------------------
% 11.16/1.80  % (9587)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 11.51/1.87  % (9589)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 11.51/1.88  % (9588)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.08/1.92  % (9338)Time limit reached!
% 12.08/1.92  % (9338)------------------------------
% 12.08/1.92  % (9338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.08/1.92  % (9338)Termination reason: Time limit
% 12.08/1.92  
% 12.08/1.92  % (9338)Memory used [KB]: 13432
% 12.08/1.92  % (9338)Time elapsed: 1.520 s
% 12.08/1.92  % (9338)------------------------------
% 12.08/1.92  % (9338)------------------------------
% 12.08/1.94  % (9590)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 12.08/1.96  % (9315)Time limit reached!
% 12.08/1.96  % (9315)------------------------------
% 12.08/1.96  % (9315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.08/1.96  % (9315)Termination reason: Time limit
% 12.08/1.96  
% 12.08/1.96  % (9315)Memory used [KB]: 19061
% 12.08/1.96  % (9315)Time elapsed: 1.540 s
% 12.08/1.96  % (9315)------------------------------
% 12.08/1.96  % (9315)------------------------------
% 12.51/2.03  % (9322)Time limit reached!
% 12.51/2.03  % (9322)------------------------------
% 12.51/2.03  % (9322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.51/2.05  % (9322)Termination reason: Time limit
% 12.51/2.05  
% 12.51/2.05  % (9322)Memory used [KB]: 22003
% 12.51/2.05  % (9322)Time elapsed: 1.608 s
% 12.51/2.05  % (9322)------------------------------
% 12.51/2.05  % (9322)------------------------------
% 13.03/2.06  % (9586)Time limit reached!
% 13.03/2.06  % (9586)------------------------------
% 13.03/2.06  % (9586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.03/2.06  % (9586)Termination reason: Time limit
% 13.03/2.06  
% 13.03/2.06  % (9586)Memory used [KB]: 4221
% 13.03/2.06  % (9586)Time elapsed: 0.416 s
% 13.03/2.06  % (9586)------------------------------
% 13.03/2.06  % (9586)------------------------------
% 13.03/2.07  % (9591)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 13.28/2.09  % (9592)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 14.06/2.16  % (9528)Time limit reached!
% 14.06/2.16  % (9528)------------------------------
% 14.06/2.16  % (9528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.06/2.17  % (9589)Time limit reached!
% 14.06/2.17  % (9589)------------------------------
% 14.06/2.17  % (9589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.06/2.17  % (9528)Termination reason: Time limit
% 14.06/2.17  
% 14.06/2.17  % (9528)Memory used [KB]: 11257
% 14.06/2.17  % (9528)Time elapsed: 1.204 s
% 14.06/2.17  % (9528)------------------------------
% 14.06/2.17  % (9528)------------------------------
% 14.06/2.17  % (9589)Termination reason: Time limit
% 14.06/2.17  
% 14.06/2.17  % (9589)Memory used [KB]: 2942
% 14.06/2.17  % (9589)Time elapsed: 0.406 s
% 14.06/2.17  % (9589)------------------------------
% 14.06/2.17  % (9589)------------------------------
% 14.06/2.19  % (9593)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 14.06/2.21  % (9594)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 14.74/2.27  % (9370)Time limit reached!
% 14.74/2.27  % (9370)------------------------------
% 14.74/2.27  % (9370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.74/2.27  % (9325)Time limit reached!
% 14.74/2.27  % (9325)------------------------------
% 14.74/2.27  % (9325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.74/2.28  % (9370)Termination reason: Time limit
% 14.74/2.28  
% 14.74/2.28  % (9370)Memory used [KB]: 21364
% 14.74/2.28  % (9370)Time elapsed: 1.705 s
% 14.74/2.28  % (9370)------------------------------
% 14.74/2.28  % (9370)------------------------------
% 14.74/2.28  % (9588)Refutation found. Thanks to Tanya!
% 14.74/2.28  % SZS status Theorem for theBenchmark
% 14.74/2.28  % SZS output start Proof for theBenchmark
% 14.74/2.28  fof(f2437,plain,(
% 14.74/2.28    $false),
% 14.74/2.28    inference(avatar_sat_refutation,[],[f94,f95,f101,f122,f123,f131,f151,f157,f165,f179,f181,f183,f185,f188,f189,f190,f191,f192,f217,f233,f268,f273,f287,f292,f297,f332,f333,f334,f339,f340,f341,f355,f377,f378,f405,f416,f418,f433,f435,f438,f454,f459,f472,f477,f494,f498,f503,f505,f510,f511,f512,f513,f514,f569,f574,f579,f580,f581,f603,f608,f613,f618,f623,f628,f633,f638,f640,f641,f653,f682,f684,f687,f692,f789,f991,f996,f1001,f1129,f1134,f1139,f1158,f1163,f1168,f1169,f1179,f1181,f1182,f1183,f1188,f1211,f1213,f1215,f1216,f1217,f1232,f1233,f1234,f1244,f1260,f1261,f1262,f1282,f1287,f1292,f1319,f1322,f1325,f1334,f1339,f1342,f1437,f1466,f1471,f1472,f1498,f1503,f1584,f1589,f1594,f1599,f1610,f1622,f1638,f1643,f1644,f1649,f1650,f1702,f1709,f1711,f1715,f1728,f2217,f2218,f2219,f2323,f2324,f2330,f2335,f2340,f2345,f2350,f2378,f2383,f2388,f2393,f2395,f2400,f2405,f2406,f2407,f2408,f2409,f2414,f2415,f2416,f2417,f2418,f2423,f2428,f2429,f2430,f2435,f2436])).
% 14.74/2.28  fof(f2436,plain,(
% 14.74/2.28    spl10_95 | ~spl10_34),
% 14.74/2.28    inference(avatar_split_clause,[],[f1690,f615,f2420])).
% 14.74/2.28  fof(f2420,plain,(
% 14.74/2.28    spl10_95 <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5)))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_95])])).
% 14.74/2.28  fof(f615,plain,(
% 14.74/2.28    spl10_34 <=> sP1(k1_tarski(sK5),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).
% 14.74/2.28  fof(f1690,plain,(
% 14.74/2.28    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5))) | ~spl10_34),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f81,f617,f58])).
% 14.74/2.28  fof(f58,plain,(
% 14.74/2.28    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~sP1(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 14.74/2.28    inference(cnf_transformation,[],[f33])).
% 14.74/2.28  fof(f33,plain,(
% 14.74/2.28    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP1(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 14.74/2.28    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f31,f32])).
% 14.74/2.28  fof(f32,plain,(
% 14.74/2.28    ! [X2,X1,X0] : (? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP1(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP1(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 14.74/2.28    introduced(choice_axiom,[])).
% 14.74/2.28  fof(f31,plain,(
% 14.74/2.28    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 14.74/2.28    inference(rectify,[],[f30])).
% 14.74/2.28  fof(f30,plain,(
% 14.74/2.28    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X1,X3,X0)) & (sP1(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 14.74/2.28    inference(nnf_transformation,[],[f19])).
% 14.74/2.28  fof(f19,plain,(
% 14.74/2.28    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X1,X3,X0)))),
% 14.74/2.28    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 14.74/2.28  fof(f617,plain,(
% 14.74/2.28    sP1(k1_tarski(sK5),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) | ~spl10_34),
% 14.74/2.28    inference(avatar_component_clause,[],[f615])).
% 14.74/2.28  fof(f81,plain,(
% 14.74/2.28    ( ! [X0,X1] : (sP2(X0,X1,k4_xboole_0(X0,X1))) )),
% 14.74/2.28    inference(equality_resolution,[],[f64])).
% 14.74/2.28  fof(f64,plain,(
% 14.74/2.28    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 14.74/2.28    inference(cnf_transformation,[],[f37])).
% 14.74/2.28  fof(f37,plain,(
% 14.74/2.28    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 14.74/2.28    inference(nnf_transformation,[],[f20])).
% 14.74/2.28  fof(f20,plain,(
% 14.74/2.28    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 14.74/2.28    inference(definition_folding,[],[f2,f19,f18])).
% 14.74/2.28  fof(f18,plain,(
% 14.74/2.28    ! [X1,X3,X0] : (sP1(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 14.74/2.28    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 14.74/2.28  fof(f2,axiom,(
% 14.74/2.28    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 14.74/2.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 14.74/2.28  fof(f2435,plain,(
% 14.74/2.28    ~spl10_97 | spl10_29 | ~spl10_34),
% 14.74/2.28    inference(avatar_split_clause,[],[f1689,f615,f571,f2432])).
% 14.74/2.28  fof(f2432,plain,(
% 14.74/2.28    spl10_97 <=> sP2(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5),sK7)),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_97])])).
% 14.74/2.28  fof(f571,plain,(
% 14.74/2.28    spl10_29 <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7)),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).
% 14.74/2.28  fof(f1689,plain,(
% 14.74/2.28    ~sP2(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5),sK7) | (spl10_29 | ~spl10_34)),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f573,f617,f58])).
% 14.74/2.28  fof(f573,plain,(
% 14.74/2.28    ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7) | spl10_29),
% 14.74/2.28    inference(avatar_component_clause,[],[f571])).
% 14.74/2.28  fof(f2430,plain,(
% 14.74/2.28    spl10_95 | ~spl10_34),
% 14.74/2.28    inference(avatar_split_clause,[],[f1687,f615,f2420])).
% 14.74/2.28  fof(f1687,plain,(
% 14.74/2.28    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5))) | ~spl10_34),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f617,f218])).
% 14.74/2.28  fof(f218,plain,(
% 14.74/2.28    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | r2_hidden(X1,k4_xboole_0(X2,X0))) )),
% 14.74/2.28    inference(resolution,[],[f58,f81])).
% 14.74/2.28  fof(f2429,plain,(
% 14.74/2.28    spl10_95 | ~spl10_34),
% 14.74/2.28    inference(avatar_split_clause,[],[f1694,f615,f2420])).
% 14.74/2.28  fof(f1694,plain,(
% 14.74/2.28    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5))) | ~spl10_34),
% 14.74/2.28    inference(resolution,[],[f617,f218])).
% 14.74/2.28  fof(f2428,plain,(
% 14.74/2.28    spl10_96 | spl10_29),
% 14.74/2.28    inference(avatar_split_clause,[],[f2302,f571,f2425])).
% 14.74/2.28  fof(f2425,plain,(
% 14.74/2.28    spl10_96 <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),sK7))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).
% 14.74/2.28  fof(f2302,plain,(
% 14.74/2.28    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),sK7)) | spl10_29),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f249,f573,f827])).
% 14.74/2.28  fof(f827,plain,(
% 14.74/2.28    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 14.74/2.28    inference(resolution,[],[f218,f63])).
% 14.74/2.28  fof(f63,plain,(
% 14.74/2.28    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 14.74/2.28    inference(cnf_transformation,[],[f36])).
% 14.74/2.28  fof(f36,plain,(
% 14.74/2.28    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP1(X0,X1,X2)))),
% 14.74/2.28    inference(rectify,[],[f35])).
% 14.74/2.28  fof(f35,plain,(
% 14.74/2.28    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP1(X1,X3,X0)))),
% 14.74/2.28    inference(flattening,[],[f34])).
% 14.74/2.28  fof(f34,plain,(
% 14.74/2.28    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP1(X1,X3,X0)))),
% 14.74/2.28    inference(nnf_transformation,[],[f18])).
% 14.74/2.28  fof(f249,plain,(
% 14.74/2.28    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f84,f103,f68])).
% 14.74/2.28  fof(f68,plain,(
% 14.74/2.28    ( ! [X2,X0,X5,X3,X1] : (~sP4(X0,X1,X2,X3) | ~sP3(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 14.74/2.28    inference(cnf_transformation,[],[f41])).
% 14.74/2.28  fof(f41,plain,(
% 14.74/2.28    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ((~sP3(sK9(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK9(X0,X1,X2,X3),X3)) & (sP3(sK9(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK9(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP3(X5,X2,X1,X0)) & (sP3(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP4(X0,X1,X2,X3)))),
% 14.74/2.28    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f39,f40])).
% 14.74/2.28  fof(f40,plain,(
% 14.74/2.28    ! [X3,X2,X1,X0] : (? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP3(sK9(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK9(X0,X1,X2,X3),X3)) & (sP3(sK9(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK9(X0,X1,X2,X3),X3))))),
% 14.74/2.28    introduced(choice_axiom,[])).
% 14.74/2.28  fof(f39,plain,(
% 14.74/2.28    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP3(X5,X2,X1,X0)) & (sP3(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP4(X0,X1,X2,X3)))),
% 14.74/2.28    inference(rectify,[],[f38])).
% 14.74/2.28  fof(f38,plain,(
% 14.74/2.28    ! [X0,X1,X2,X3] : ((sP4(X0,X1,X2,X3) | ? [X4] : ((~sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP3(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP3(X4,X2,X1,X0)) & (sP3(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP4(X0,X1,X2,X3)))),
% 14.74/2.28    inference(nnf_transformation,[],[f22])).
% 14.74/2.28  fof(f22,plain,(
% 14.74/2.28    ! [X0,X1,X2,X3] : (sP4(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP3(X4,X2,X1,X0)))),
% 14.74/2.28    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 14.74/2.28  fof(f103,plain,(
% 14.74/2.28    ( ! [X0] : (sP4(X0,X0,X0,k1_tarski(X0))) )),
% 14.74/2.28    inference(superposition,[],[f102,f52])).
% 14.74/2.28  fof(f52,plain,(
% 14.74/2.28    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 14.74/2.28    inference(cnf_transformation,[],[f5])).
% 14.74/2.28  fof(f5,axiom,(
% 14.74/2.28    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 14.74/2.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 14.74/2.28  fof(f102,plain,(
% 14.74/2.28    ( ! [X0,X1] : (sP4(X0,X0,X1,k2_tarski(X0,X1))) )),
% 14.74/2.28    inference(superposition,[],[f85,f54])).
% 14.74/2.28  fof(f54,plain,(
% 14.74/2.28    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 14.74/2.28    inference(cnf_transformation,[],[f6])).
% 14.74/2.28  fof(f6,axiom,(
% 14.74/2.28    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 14.74/2.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 14.74/2.28  fof(f85,plain,(
% 14.74/2.28    ( ! [X2,X0,X1] : (sP4(X0,X1,X2,k1_enumset1(X0,X1,X2))) )),
% 14.74/2.28    inference(equality_resolution,[],[f75])).
% 14.74/2.28  fof(f75,plain,(
% 14.74/2.28    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 14.74/2.28    inference(cnf_transformation,[],[f45])).
% 14.74/2.28  fof(f45,plain,(
% 14.74/2.28    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP4(X0,X1,X2,X3)) & (sP4(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 14.74/2.28    inference(nnf_transformation,[],[f23])).
% 14.74/2.28  fof(f23,plain,(
% 14.74/2.28    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP4(X0,X1,X2,X3))),
% 14.74/2.28    inference(definition_folding,[],[f15,f22,f21])).
% 14.74/2.28  fof(f21,plain,(
% 14.74/2.28    ! [X4,X2,X1,X0] : (sP3(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 14.74/2.28    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 14.74/2.28  fof(f15,plain,(
% 14.74/2.28    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 14.74/2.28    inference(ennf_transformation,[],[f4])).
% 14.74/2.28  fof(f4,axiom,(
% 14.74/2.28    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 14.74/2.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 14.74/2.28  fof(f84,plain,(
% 14.74/2.28    ( ! [X2,X3,X1] : (sP3(X3,X1,X2,X3)) )),
% 14.74/2.28    inference(equality_resolution,[],[f72])).
% 14.74/2.28  fof(f72,plain,(
% 14.74/2.28    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | X0 != X3) )),
% 14.74/2.28    inference(cnf_transformation,[],[f44])).
% 14.74/2.28  fof(f44,plain,(
% 14.74/2.28    ! [X0,X1,X2,X3] : ((sP3(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP3(X0,X1,X2,X3)))),
% 14.74/2.28    inference(rectify,[],[f43])).
% 14.74/2.28  fof(f43,plain,(
% 14.74/2.28    ! [X4,X2,X1,X0] : ((sP3(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP3(X4,X2,X1,X0)))),
% 14.74/2.28    inference(flattening,[],[f42])).
% 14.74/2.28  fof(f42,plain,(
% 14.74/2.28    ! [X4,X2,X1,X0] : ((sP3(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP3(X4,X2,X1,X0)))),
% 14.74/2.28    inference(nnf_transformation,[],[f21])).
% 14.74/2.28  fof(f2423,plain,(
% 14.74/2.28    spl10_95 | spl10_19),
% 14.74/2.28    inference(avatar_split_clause,[],[f2294,f370,f2420])).
% 14.74/2.28  fof(f370,plain,(
% 14.74/2.28    spl10_19 <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 14.74/2.28  fof(f2294,plain,(
% 14.74/2.28    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5))) | spl10_19),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f249,f371,f827])).
% 14.74/2.28  fof(f371,plain,(
% 14.74/2.28    ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5)) | spl10_19),
% 14.74/2.28    inference(avatar_component_clause,[],[f370])).
% 14.74/2.28  fof(f2418,plain,(
% 14.74/2.28    ~spl10_18 | spl10_40),
% 14.74/2.28    inference(avatar_split_clause,[],[f1276,f679,f336])).
% 14.74/2.28  fof(f336,plain,(
% 14.74/2.28    spl10_18 <=> sP3(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 14.74/2.28  fof(f679,plain,(
% 14.74/2.28    spl10_40 <=> r2_hidden(k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).
% 14.74/2.28  fof(f1276,plain,(
% 14.74/2.28    ~sP3(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | spl10_40),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f103,f681,f68])).
% 14.74/2.28  fof(f681,plain,(
% 14.74/2.28    ~r2_hidden(k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) | spl10_40),
% 14.74/2.28    inference(avatar_component_clause,[],[f679])).
% 14.74/2.28  fof(f2417,plain,(
% 14.74/2.28    ~spl10_18 | spl10_40),
% 14.74/2.28    inference(avatar_split_clause,[],[f1263,f679,f336])).
% 14.74/2.28  fof(f1263,plain,(
% 14.74/2.28    ~sP3(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | spl10_40),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f681,f252])).
% 14.74/2.28  fof(f252,plain,(
% 14.74/2.28    ( ! [X8,X7] : (~sP3(X7,X8,X8,X8) | r2_hidden(X7,k1_tarski(X8))) )),
% 14.74/2.28    inference(resolution,[],[f68,f103])).
% 14.74/2.28  fof(f2416,plain,(
% 14.74/2.28    ~spl10_17 | spl10_27),
% 14.74/2.28    inference(avatar_split_clause,[],[f1120,f507,f329])).
% 14.74/2.28  fof(f329,plain,(
% 14.74/2.28    spl10_17 <=> sP3(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 14.74/2.28  fof(f507,plain,(
% 14.74/2.28    spl10_27 <=> r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5)))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 14.74/2.28  fof(f1120,plain,(
% 14.74/2.28    ~sP3(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5)) | spl10_27),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f103,f509,f68])).
% 14.74/2.28  fof(f509,plain,(
% 14.74/2.28    ~r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))) | spl10_27),
% 14.74/2.28    inference(avatar_component_clause,[],[f507])).
% 14.74/2.28  fof(f2415,plain,(
% 14.74/2.28    ~spl10_17 | spl10_27),
% 14.74/2.28    inference(avatar_split_clause,[],[f1110,f507,f329])).
% 14.74/2.28  fof(f1110,plain,(
% 14.74/2.28    ~sP3(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5)) | spl10_27),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f509,f252])).
% 14.74/2.28  fof(f2414,plain,(
% 14.74/2.28    ~spl10_94 | spl10_4 | ~spl10_37),
% 14.74/2.28    inference(avatar_split_clause,[],[f642,f630,f119,f2411])).
% 14.74/2.28  fof(f2411,plain,(
% 14.74/2.28    spl10_94 <=> sP2(k1_tarski(sK5),sK7,sK7)),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).
% 14.74/2.28  fof(f119,plain,(
% 14.74/2.28    spl10_4 <=> r2_hidden(sK5,sK7)),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 14.74/2.28  fof(f630,plain,(
% 14.74/2.28    spl10_37 <=> sP1(sK7,sK5,k1_tarski(sK5))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).
% 14.74/2.28  fof(f642,plain,(
% 14.74/2.28    ~sP2(k1_tarski(sK5),sK7,sK7) | (spl10_4 | ~spl10_37)),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f121,f632,f58])).
% 14.74/2.28  fof(f632,plain,(
% 14.74/2.28    sP1(sK7,sK5,k1_tarski(sK5)) | ~spl10_37),
% 14.74/2.28    inference(avatar_component_clause,[],[f630])).
% 14.74/2.28  fof(f121,plain,(
% 14.74/2.28    ~r2_hidden(sK5,sK7) | spl10_4),
% 14.74/2.28    inference(avatar_component_clause,[],[f119])).
% 14.74/2.28  fof(f2409,plain,(
% 14.74/2.28    spl10_7 | ~spl10_15),
% 14.74/2.28    inference(avatar_split_clause,[],[f782,f289,f148])).
% 14.74/2.28  fof(f148,plain,(
% 14.74/2.28    spl10_7 <=> r2_hidden(sK6,sK7)),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 14.74/2.28  fof(f289,plain,(
% 14.74/2.28    spl10_15 <=> sP1(k1_tarski(sK5),sK6,sK7)),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 14.74/2.28  fof(f782,plain,(
% 14.74/2.28    r2_hidden(sK6,sK7) | ~spl10_15),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f291,f61])).
% 14.74/2.28  fof(f61,plain,(
% 14.74/2.28    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 14.74/2.28    inference(cnf_transformation,[],[f36])).
% 14.74/2.28  fof(f291,plain,(
% 14.74/2.28    sP1(k1_tarski(sK5),sK6,sK7) | ~spl10_15),
% 14.74/2.28    inference(avatar_component_clause,[],[f289])).
% 14.74/2.28  fof(f2408,plain,(
% 14.74/2.28    spl10_7 | ~spl10_15),
% 14.74/2.28    inference(avatar_split_clause,[],[f784,f289,f148])).
% 14.74/2.28  fof(f784,plain,(
% 14.74/2.28    r2_hidden(sK6,sK7) | ~spl10_15),
% 14.74/2.28    inference(resolution,[],[f291,f61])).
% 14.74/2.28  fof(f2407,plain,(
% 14.74/2.28    spl10_7 | spl10_21),
% 14.74/2.28    inference(avatar_split_clause,[],[f1107,f402,f148])).
% 14.74/2.28  fof(f402,plain,(
% 14.74/2.28    spl10_21 <=> sP1(sK7,sK6,k2_tarski(sK5,sK6))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 14.74/2.28  fof(f1107,plain,(
% 14.74/2.28    r2_hidden(sK6,sK7) | spl10_21),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f244,f404,f63])).
% 14.74/2.28  fof(f404,plain,(
% 14.74/2.28    ~sP1(sK7,sK6,k2_tarski(sK5,sK6)) | spl10_21),
% 14.74/2.28    inference(avatar_component_clause,[],[f402])).
% 14.74/2.28  fof(f244,plain,(
% 14.74/2.28    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f82,f102,f68])).
% 14.74/2.28  fof(f82,plain,(
% 14.74/2.28    ( ! [X2,X3,X1] : (sP3(X1,X1,X2,X3)) )),
% 14.74/2.28    inference(equality_resolution,[],[f74])).
% 14.74/2.28  fof(f74,plain,(
% 14.74/2.28    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2,X3) | X0 != X1) )),
% 14.74/2.28    inference(cnf_transformation,[],[f44])).
% 14.74/2.28  fof(f2406,plain,(
% 14.74/2.28    ~spl10_92 | spl10_21),
% 14.74/2.28    inference(avatar_split_clause,[],[f1106,f402,f2397])).
% 14.74/2.28  fof(f2397,plain,(
% 14.74/2.28    spl10_92 <=> r2_hidden(sK6,k4_xboole_0(k2_tarski(sK5,sK6),sK7))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).
% 14.74/2.28  fof(f1106,plain,(
% 14.74/2.28    ~r2_hidden(sK6,k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | spl10_21),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f81,f404,f57])).
% 14.74/2.28  fof(f57,plain,(
% 14.74/2.28    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | sP1(X1,X4,X0)) )),
% 14.74/2.28    inference(cnf_transformation,[],[f33])).
% 14.74/2.28  fof(f2405,plain,(
% 14.74/2.28    ~spl10_93 | spl10_21),
% 14.74/2.28    inference(avatar_split_clause,[],[f1100,f402,f2402])).
% 14.74/2.28  fof(f2402,plain,(
% 14.74/2.28    spl10_93 <=> sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK6))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).
% 14.74/2.28  fof(f1100,plain,(
% 14.74/2.28    ~sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK6)) | spl10_21),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f249,f404,f57])).
% 14.74/2.28  fof(f2400,plain,(
% 14.74/2.28    ~spl10_92 | spl10_21),
% 14.74/2.28    inference(avatar_split_clause,[],[f1098,f402,f2397])).
% 14.74/2.28  fof(f1098,plain,(
% 14.74/2.28    ~r2_hidden(sK6,k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | spl10_21),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f404,f206])).
% 14.74/2.28  fof(f206,plain,(
% 14.74/2.28    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | sP1(X2,X0,X1)) )),
% 14.74/2.28    inference(resolution,[],[f57,f81])).
% 14.74/2.28  fof(f2395,plain,(
% 14.74/2.28    spl10_7 | spl10_21),
% 14.74/2.28    inference(avatar_split_clause,[],[f2394,f402,f148])).
% 14.74/2.28  fof(f2394,plain,(
% 14.74/2.28    r2_hidden(sK6,sK7) | spl10_21),
% 14.74/2.28    inference(subsumption_resolution,[],[f1109,f244])).
% 14.74/2.28  fof(f1109,plain,(
% 14.74/2.28    r2_hidden(sK6,sK7) | ~r2_hidden(sK6,k2_tarski(sK5,sK6)) | spl10_21),
% 14.74/2.28    inference(resolution,[],[f404,f63])).
% 14.74/2.28  fof(f2393,plain,(
% 14.74/2.28    ~spl10_91 | spl10_4 | ~spl10_36),
% 14.74/2.28    inference(avatar_split_clause,[],[f1246,f625,f119,f2390])).
% 14.74/2.28  fof(f2390,plain,(
% 14.74/2.28    spl10_91 <=> sP2(k1_tarski(sK5),k1_tarski(sK6),sK7)),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_91])])).
% 14.74/2.28  fof(f625,plain,(
% 14.74/2.28    spl10_36 <=> sP1(k1_tarski(sK6),sK5,k1_tarski(sK5))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).
% 14.74/2.28  fof(f1246,plain,(
% 14.74/2.28    ~sP2(k1_tarski(sK5),k1_tarski(sK6),sK7) | (spl10_4 | ~spl10_36)),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f121,f627,f58])).
% 14.74/2.28  fof(f627,plain,(
% 14.74/2.28    sP1(k1_tarski(sK6),sK5,k1_tarski(sK5)) | ~spl10_36),
% 14.74/2.28    inference(avatar_component_clause,[],[f625])).
% 14.74/2.28  fof(f2388,plain,(
% 14.74/2.28    ~spl10_90 | spl10_22 | ~spl10_45),
% 14.74/2.28    inference(avatar_split_clause,[],[f2203,f998,f430,f2385])).
% 14.74/2.28  fof(f2385,plain,(
% 14.74/2.28    spl10_90 <=> sP2(k4_xboole_0(k1_tarski(sK5),sK7),sK7,k1_tarski(sK6))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).
% 14.74/2.28  fof(f430,plain,(
% 14.74/2.28    spl10_22 <=> r2_hidden(sK5,k1_tarski(sK6))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 14.74/2.28  fof(f998,plain,(
% 14.74/2.28    spl10_45 <=> sP1(sK7,sK5,k4_xboole_0(k1_tarski(sK5),sK7))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).
% 14.74/2.28  fof(f2203,plain,(
% 14.74/2.28    ~sP2(k4_xboole_0(k1_tarski(sK5),sK7),sK7,k1_tarski(sK6)) | (spl10_22 | ~spl10_45)),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f432,f1000,f58])).
% 14.74/2.28  fof(f1000,plain,(
% 14.74/2.28    sP1(sK7,sK5,k4_xboole_0(k1_tarski(sK5),sK7)) | ~spl10_45),
% 14.74/2.28    inference(avatar_component_clause,[],[f998])).
% 14.74/2.28  fof(f432,plain,(
% 14.74/2.28    ~r2_hidden(sK5,k1_tarski(sK6)) | spl10_22),
% 14.74/2.28    inference(avatar_component_clause,[],[f430])).
% 14.74/2.28  fof(f2383,plain,(
% 14.74/2.28    ~spl10_89 | spl10_4 | ~spl10_45),
% 14.74/2.28    inference(avatar_split_clause,[],[f2202,f998,f119,f2380])).
% 14.74/2.28  fof(f2380,plain,(
% 14.74/2.28    spl10_89 <=> sP2(k4_xboole_0(k1_tarski(sK5),sK7),sK7,sK7)),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).
% 14.74/2.28  fof(f2202,plain,(
% 14.74/2.28    ~sP2(k4_xboole_0(k1_tarski(sK5),sK7),sK7,sK7) | (spl10_4 | ~spl10_45)),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f121,f1000,f58])).
% 14.74/2.28  fof(f2378,plain,(
% 14.74/2.28    spl10_88 | ~spl10_28 | spl10_60),
% 14.74/2.28    inference(avatar_split_clause,[],[f2373,f1316,f566,f2375])).
% 14.74/2.28  fof(f2375,plain,(
% 14.74/2.28    spl10_88 <=> sK6 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).
% 14.74/2.28  fof(f566,plain,(
% 14.74/2.28    spl10_28 <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).
% 14.74/2.28  fof(f1316,plain,(
% 14.74/2.28    spl10_60 <=> sK5 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).
% 14.74/2.28  fof(f2373,plain,(
% 14.74/2.28    sK6 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) | (~spl10_28 | spl10_60)),
% 14.74/2.28    inference(subsumption_resolution,[],[f2366,f1317])).
% 14.74/2.28  fof(f1317,plain,(
% 14.74/2.28    sK5 != sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) | spl10_60),
% 14.74/2.28    inference(avatar_component_clause,[],[f1316])).
% 14.74/2.28  fof(f2366,plain,(
% 14.74/2.28    sK5 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) | sK6 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) | ~spl10_28),
% 14.74/2.28    inference(resolution,[],[f881,f568])).
% 14.74/2.28  fof(f568,plain,(
% 14.74/2.28    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | ~spl10_28),
% 14.74/2.28    inference(avatar_component_clause,[],[f566])).
% 14.74/2.28  fof(f881,plain,(
% 14.74/2.28    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2) )),
% 14.74/2.28    inference(duplicate_literal_removal,[],[f874])).
% 14.74/2.28  fof(f874,plain,(
% 14.74/2.28    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X1 | X0 = X2) )),
% 14.74/2.28    inference(resolution,[],[f235,f71])).
% 14.74/2.28  fof(f71,plain,(
% 14.74/2.28    ( ! [X2,X0,X3,X1] : (~sP3(X0,X1,X2,X3) | X0 = X2 | X0 = X3 | X0 = X1) )),
% 14.74/2.28    inference(cnf_transformation,[],[f44])).
% 14.74/2.28  fof(f235,plain,(
% 14.74/2.28    ( ! [X6,X4,X5] : (sP3(X4,X6,X5,X5) | ~r2_hidden(X4,k2_tarski(X5,X6))) )),
% 14.74/2.28    inference(resolution,[],[f67,f102])).
% 14.74/2.28  fof(f67,plain,(
% 14.74/2.28    ( ! [X2,X0,X5,X3,X1] : (~sP4(X0,X1,X2,X3) | ~r2_hidden(X5,X3) | sP3(X5,X2,X1,X0)) )),
% 14.74/2.28    inference(cnf_transformation,[],[f41])).
% 14.74/2.28  fof(f2350,plain,(
% 14.74/2.28    spl10_87 | spl10_27),
% 14.74/2.28    inference(avatar_split_clause,[],[f2220,f507,f2347])).
% 14.74/2.28  fof(f2347,plain,(
% 14.74/2.28    spl10_87 <=> r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)),k1_tarski(k1_tarski(sK5))))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_87])])).
% 14.74/2.28  fof(f2220,plain,(
% 14.74/2.28    r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)),k1_tarski(k1_tarski(sK5)))) | spl10_27),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f249,f509,f827])).
% 14.74/2.28  fof(f2345,plain,(
% 14.74/2.28    spl10_86 | spl10_40),
% 14.74/2.28    inference(avatar_split_clause,[],[f2226,f679,f2342])).
% 14.74/2.28  fof(f2342,plain,(
% 14.74/2.28    spl10_86 <=> r2_hidden(k1_tarski(sK5),k4_xboole_0(k1_tarski(k1_tarski(sK5)),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).
% 14.74/2.28  fof(f2226,plain,(
% 14.74/2.28    r2_hidden(k1_tarski(sK5),k4_xboole_0(k1_tarski(k1_tarski(sK5)),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))) | spl10_40),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f249,f681,f827])).
% 14.74/2.28  fof(f2340,plain,(
% 14.74/2.28    spl10_85 | spl10_22 | ~spl10_39),
% 14.74/2.28    inference(avatar_split_clause,[],[f2241,f650,f430,f2337])).
% 14.74/2.28  fof(f2337,plain,(
% 14.74/2.28    spl10_85 <=> r2_hidden(sK5,k4_xboole_0(k4_xboole_0(k1_tarski(sK5),sK7),k1_tarski(sK6)))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_85])])).
% 14.74/2.28  fof(f650,plain,(
% 14.74/2.28    spl10_39 <=> r2_hidden(sK5,k4_xboole_0(k1_tarski(sK5),sK7))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).
% 14.74/2.28  fof(f2241,plain,(
% 14.74/2.28    r2_hidden(sK5,k4_xboole_0(k4_xboole_0(k1_tarski(sK5),sK7),k1_tarski(sK6))) | (spl10_22 | ~spl10_39)),
% 14.74/2.28    inference(unit_resulting_resolution,[],[f652,f432,f827])).
% 14.74/2.28  fof(f652,plain,(
% 14.74/2.28    r2_hidden(sK5,k4_xboole_0(k1_tarski(sK5),sK7)) | ~spl10_39),
% 14.74/2.28    inference(avatar_component_clause,[],[f650])).
% 14.74/2.28  fof(f2335,plain,(
% 14.74/2.28    spl10_84 | spl10_10 | ~spl10_42),
% 14.74/2.28    inference(avatar_split_clause,[],[f2269,f786,f214,f2332])).
% 14.74/2.28  fof(f2332,plain,(
% 14.74/2.28    spl10_84 <=> r2_hidden(sK6,k4_xboole_0(k4_xboole_0(sK7,k1_tarski(sK5)),k1_tarski(sK5)))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).
% 14.74/2.28  fof(f214,plain,(
% 14.74/2.28    spl10_10 <=> r2_hidden(sK6,k1_tarski(sK5))),
% 14.74/2.28    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 14.74/2.29  % (9596)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 15.24/2.30  % (9325)Termination reason: Time limit
% 15.24/2.30  
% 15.24/2.30  % (9325)Memory used [KB]: 9850
% 15.24/2.30  % (9325)Time elapsed: 1.839 s
% 15.24/2.30  % (9325)------------------------------
% 15.24/2.30  % (9325)------------------------------
% 15.24/2.30  fof(f786,plain,(
% 15.24/2.30    spl10_42 <=> r2_hidden(sK6,k4_xboole_0(sK7,k1_tarski(sK5)))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).
% 15.24/2.30  fof(f2269,plain,(
% 15.24/2.30    r2_hidden(sK6,k4_xboole_0(k4_xboole_0(sK7,k1_tarski(sK5)),k1_tarski(sK5))) | (spl10_10 | ~spl10_42)),
% 15.24/2.30    inference(unit_resulting_resolution,[],[f788,f216,f827])).
% 15.24/2.30  fof(f216,plain,(
% 15.24/2.30    ~r2_hidden(sK6,k1_tarski(sK5)) | spl10_10),
% 15.24/2.30    inference(avatar_component_clause,[],[f214])).
% 15.24/2.30  fof(f788,plain,(
% 15.24/2.30    r2_hidden(sK6,k4_xboole_0(sK7,k1_tarski(sK5))) | ~spl10_42),
% 15.24/2.30    inference(avatar_component_clause,[],[f786])).
% 15.24/2.30  fof(f2330,plain,(
% 15.24/2.30    spl10_83 | spl10_19 | ~spl10_28),
% 15.24/2.30    inference(avatar_split_clause,[],[f2292,f566,f370,f2327])).
% 15.24/2.30  fof(f2327,plain,(
% 15.24/2.30    spl10_83 <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK5)))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).
% 15.24/2.30  fof(f2292,plain,(
% 15.24/2.30    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK5))) | (spl10_19 | ~spl10_28)),
% 15.24/2.30    inference(unit_resulting_resolution,[],[f568,f371,f827])).
% 15.24/2.30  fof(f2324,plain,(
% 15.24/2.30    spl10_82 | spl10_29 | ~spl10_30),
% 15.24/2.30    inference(avatar_split_clause,[],[f2301,f576,f571,f2320])).
% 15.24/2.30  fof(f2320,plain,(
% 15.24/2.30    spl10_82 <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),sK7))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).
% 15.24/2.30  fof(f576,plain,(
% 15.24/2.30    spl10_30 <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 15.24/2.30  fof(f2301,plain,(
% 15.24/2.30    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),sK7)) | (spl10_29 | ~spl10_30)),
% 15.24/2.30    inference(unit_resulting_resolution,[],[f578,f573,f827])).
% 15.24/2.30  fof(f578,plain,(
% 15.24/2.30    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | ~spl10_30),
% 15.24/2.30    inference(avatar_component_clause,[],[f576])).
% 15.24/2.30  fof(f2323,plain,(
% 15.24/2.30    spl10_82 | spl10_29 | ~spl10_74),
% 15.24/2.30    inference(avatar_split_clause,[],[f2318,f1635,f571,f2320])).
% 15.24/2.30  fof(f1635,plain,(
% 15.24/2.30    spl10_74 <=> k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).
% 15.24/2.30  fof(f2318,plain,(
% 15.24/2.30    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),sK7)) | (spl10_29 | ~spl10_74)),
% 15.24/2.30    inference(forward_demodulation,[],[f2302,f1637])).
% 15.24/2.30  fof(f1637,plain,(
% 15.24/2.30    k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))) | ~spl10_74),
% 15.24/2.30    inference(avatar_component_clause,[],[f1635])).
% 15.24/2.30  fof(f2219,plain,(
% 15.24/2.30    spl10_81 | ~spl10_45),
% 15.24/2.30    inference(avatar_split_clause,[],[f2210,f998,f2214])).
% 15.24/2.30  fof(f2214,plain,(
% 15.24/2.30    spl10_81 <=> r2_hidden(sK5,k4_xboole_0(k4_xboole_0(k1_tarski(sK5),sK7),sK7))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_81])])).
% 15.24/2.30  fof(f2210,plain,(
% 15.24/2.30    r2_hidden(sK5,k4_xboole_0(k4_xboole_0(k1_tarski(sK5),sK7),sK7)) | ~spl10_45),
% 15.24/2.30    inference(resolution,[],[f1000,f218])).
% 15.24/2.30  fof(f2218,plain,(
% 15.24/2.30    spl10_81 | ~spl10_45),
% 15.24/2.30    inference(avatar_split_clause,[],[f2201,f998,f2214])).
% 15.24/2.30  fof(f2201,plain,(
% 15.24/2.30    r2_hidden(sK5,k4_xboole_0(k4_xboole_0(k1_tarski(sK5),sK7),sK7)) | ~spl10_45),
% 15.24/2.30    inference(unit_resulting_resolution,[],[f1000,f218])).
% 15.24/2.30  fof(f2217,plain,(
% 15.24/2.30    spl10_81 | ~spl10_45),
% 15.24/2.30    inference(avatar_split_clause,[],[f2206,f998,f2214])).
% 15.24/2.30  fof(f2206,plain,(
% 15.24/2.30    r2_hidden(sK5,k4_xboole_0(k4_xboole_0(k1_tarski(sK5),sK7),sK7)) | ~spl10_45),
% 15.24/2.30    inference(unit_resulting_resolution,[],[f81,f1000,f58])).
% 15.24/2.30  fof(f1728,plain,(
% 15.24/2.30    spl10_79 | spl10_80 | spl10_41),
% 15.24/2.30    inference(avatar_split_clause,[],[f1719,f689,f1725,f1721])).
% 15.24/2.30  fof(f1721,plain,(
% 15.24/2.30    spl10_79 <=> r2_hidden(sK9(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))),k1_tarski(k1_tarski(sK5)))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).
% 15.24/2.30  fof(f1725,plain,(
% 15.24/2.30    spl10_80 <=> sP3(sK9(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).
% 15.24/2.30  fof(f689,plain,(
% 15.24/2.30    spl10_41 <=> sP4(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5)))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).
% 15.24/2.30  fof(f1719,plain,(
% 15.24/2.30    sP3(sK9(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | r2_hidden(sK9(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))),k1_tarski(k1_tarski(sK5))) | spl10_41),
% 15.24/2.30    inference(resolution,[],[f691,f69])).
% 15.24/2.30  fof(f69,plain,(
% 15.24/2.30    ( ! [X2,X0,X3,X1] : (sP4(X0,X1,X2,X3) | sP3(sK9(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK9(X0,X1,X2,X3),X3)) )),
% 15.24/2.30    inference(cnf_transformation,[],[f41])).
% 15.24/2.30  fof(f691,plain,(
% 15.24/2.30    ~sP4(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))) | spl10_41),
% 15.24/2.30    inference(avatar_component_clause,[],[f689])).
% 15.24/2.30  fof(f1715,plain,(
% 15.24/2.30    spl10_77 | ~spl10_34 | ~spl10_74),
% 15.24/2.30    inference(avatar_split_clause,[],[f1714,f1635,f615,f1699])).
% 15.24/2.30  fof(f1699,plain,(
% 15.24/2.30    spl10_77 <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5)))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).
% 15.24/2.30  fof(f1714,plain,(
% 15.24/2.30    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5))) | (~spl10_34 | ~spl10_74)),
% 15.24/2.30    inference(forward_demodulation,[],[f1694,f1637])).
% 15.24/2.30  fof(f1711,plain,(
% 15.24/2.30    spl10_77 | ~spl10_34 | ~spl10_74),
% 15.24/2.30    inference(avatar_split_clause,[],[f1710,f1635,f615,f1699])).
% 15.24/2.30  fof(f1710,plain,(
% 15.24/2.30    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5))) | (~spl10_34 | ~spl10_74)),
% 15.24/2.30    inference(forward_demodulation,[],[f1687,f1637])).
% 15.24/2.30  fof(f1709,plain,(
% 15.24/2.30    ~spl10_78 | spl10_19 | ~spl10_34 | ~spl10_74),
% 15.24/2.30    inference(avatar_split_clause,[],[f1704,f1635,f615,f370,f1706])).
% 15.24/2.30  fof(f1706,plain,(
% 15.24/2.30    spl10_78 <=> sP2(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).
% 15.24/2.30  fof(f1704,plain,(
% 15.24/2.30    ~sP2(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5)) | (spl10_19 | ~spl10_34 | ~spl10_74)),
% 15.24/2.30    inference(forward_demodulation,[],[f1688,f1637])).
% 15.24/2.30  fof(f1688,plain,(
% 15.24/2.30    ~sP2(k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),k1_tarski(sK5),k1_tarski(sK5)) | (spl10_19 | ~spl10_34)),
% 15.24/2.30    inference(unit_resulting_resolution,[],[f371,f617,f58])).
% 15.24/2.30  fof(f1702,plain,(
% 15.24/2.30    spl10_77 | ~spl10_34 | ~spl10_74),
% 15.24/2.30    inference(avatar_split_clause,[],[f1697,f1635,f615,f1699])).
% 15.24/2.30  fof(f1697,plain,(
% 15.24/2.30    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5))) | (~spl10_34 | ~spl10_74)),
% 15.24/2.30    inference(forward_demodulation,[],[f1690,f1637])).
% 15.24/2.30  fof(f1650,plain,(
% 15.24/2.30    spl10_74 | ~spl10_53),
% 15.24/2.30    inference(avatar_split_clause,[],[f1633,f1208,f1635])).
% 15.24/2.30  fof(f1208,plain,(
% 15.24/2.30    spl10_53 <=> sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).
% 15.24/2.30  fof(f1633,plain,(
% 15.24/2.30    k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))) | ~spl10_53),
% 15.24/2.30    inference(resolution,[],[f1209,f65])).
% 15.24/2.30  fof(f65,plain,(
% 15.24/2.30    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | k4_xboole_0(X0,X1) = X2) )),
% 15.24/2.30    inference(cnf_transformation,[],[f37])).
% 15.24/2.30  fof(f1209,plain,(
% 15.24/2.30    sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) | ~spl10_53),
% 15.24/2.30    inference(avatar_component_clause,[],[f1208])).
% 15.24/2.30  fof(f1649,plain,(
% 15.24/2.30    spl10_76 | spl10_4 | ~spl10_53),
% 15.24/2.30    inference(avatar_split_clause,[],[f1625,f1208,f119,f1646])).
% 15.24/2.30  fof(f1646,plain,(
% 15.24/2.30    spl10_76 <=> r2_hidden(sK5,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).
% 15.24/2.30  fof(f1625,plain,(
% 15.24/2.30    r2_hidden(sK5,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) | (spl10_4 | ~spl10_53)),
% 15.24/2.30    inference(unit_resulting_resolution,[],[f727,f1209,f58])).
% 15.24/2.30  fof(f727,plain,(
% 15.24/2.30    ( ! [X0] : (sP1(sK7,sK5,k2_tarski(sK5,X0))) ) | spl10_4),
% 15.24/2.30    inference(unit_resulting_resolution,[],[f121,f246,f63])).
% 15.24/2.30  fof(f246,plain,(
% 15.24/2.30    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 15.24/2.30    inference(unit_resulting_resolution,[],[f84,f102,f68])).
% 15.24/2.30  fof(f1644,plain,(
% 15.24/2.30    ~spl10_75 | spl10_21 | ~spl10_53),
% 15.24/2.30    inference(avatar_split_clause,[],[f1627,f1208,f402,f1640])).
% 15.24/2.30  fof(f1640,plain,(
% 15.24/2.30    spl10_75 <=> r2_hidden(sK6,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).
% 15.24/2.30  fof(f1627,plain,(
% 15.24/2.30    ~r2_hidden(sK6,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) | (spl10_21 | ~spl10_53)),
% 15.24/2.30    inference(unit_resulting_resolution,[],[f404,f1209,f57])).
% 15.24/2.30  fof(f1643,plain,(
% 15.24/2.30    ~spl10_75 | ~spl10_7 | ~spl10_53),
% 15.24/2.30    inference(avatar_split_clause,[],[f1628,f1208,f148,f1640])).
% 15.24/2.30  fof(f1628,plain,(
% 15.24/2.30    ~r2_hidden(sK6,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) | (~spl10_7 | ~spl10_53)),
% 15.24/2.30    inference(unit_resulting_resolution,[],[f518,f1209,f57])).
% 15.24/2.30  fof(f518,plain,(
% 15.24/2.30    ( ! [X0] : (~sP1(sK7,sK6,X0)) ) | ~spl10_7),
% 15.24/2.30    inference(unit_resulting_resolution,[],[f150,f62])).
% 15.24/2.30  fof(f62,plain,(
% 15.24/2.30    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 15.24/2.30    inference(cnf_transformation,[],[f36])).
% 15.24/2.30  fof(f150,plain,(
% 15.24/2.30    r2_hidden(sK6,sK7) | ~spl10_7),
% 15.24/2.30    inference(avatar_component_clause,[],[f148])).
% 15.24/2.30  fof(f1638,plain,(
% 15.24/2.30    spl10_74 | ~spl10_53),
% 15.24/2.30    inference(avatar_split_clause,[],[f1630,f1208,f1635])).
% 15.24/2.30  fof(f1630,plain,(
% 15.24/2.30    k4_xboole_0(k2_tarski(sK5,sK6),sK7) = k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))) | ~spl10_53),
% 15.24/2.30    inference(unit_resulting_resolution,[],[f1209,f65])).
% 15.24/2.30  fof(f1622,plain,(
% 15.24/2.30    spl10_72 | spl10_73 | spl10_53),
% 15.24/2.30    inference(avatar_split_clause,[],[f1613,f1208,f1619,f1615])).
% 15.24/2.30  fof(f1615,plain,(
% 15.24/2.30    spl10_72 <=> r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))),k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).
% 15.24/2.30  fof(f1619,plain,(
% 15.24/2.30    spl10_73 <=> sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))),k2_tarski(sK5,sK6))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).
% 15.24/2.30  fof(f1613,plain,(
% 15.24/2.30    sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))),k2_tarski(sK5,sK6)) | r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))),k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) | spl10_53),
% 15.24/2.30    inference(resolution,[],[f1210,f59])).
% 15.24/2.30  fof(f59,plain,(
% 15.24/2.30    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | sP1(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2)) )),
% 15.24/2.30    inference(cnf_transformation,[],[f33])).
% 15.24/2.30  fof(f1210,plain,(
% 15.24/2.30    ~sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) | spl10_53),
% 15.24/2.30    inference(avatar_component_clause,[],[f1208])).
% 15.24/2.30  fof(f1610,plain,(
% 15.24/2.30    spl10_70 | spl10_71 | spl10_38),
% 15.24/2.30    inference(avatar_split_clause,[],[f1601,f635,f1607,f1603])).
% 15.24/2.30  fof(f1603,plain,(
% 15.24/2.30    spl10_70 <=> r2_hidden(sK9(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).
% 15.24/2.30  fof(f1607,plain,(
% 15.24/2.30    spl10_71 <=> sP3(sK9(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).
% 15.24/2.30  fof(f635,plain,(
% 15.24/2.30    spl10_38 <=> sP4(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 15.24/2.30  fof(f1601,plain,(
% 15.24/2.30    sP3(sK9(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5)) | r2_hidden(sK9(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) | spl10_38),
% 15.24/2.30    inference(resolution,[],[f637,f69])).
% 15.24/2.30  fof(f637,plain,(
% 15.24/2.30    ~sP4(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) | spl10_38),
% 15.24/2.30    inference(avatar_component_clause,[],[f635])).
% 15.24/2.30  fof(f1599,plain,(
% 15.24/2.30    spl10_69 | ~spl10_7 | ~spl10_30),
% 15.24/2.30    inference(avatar_split_clause,[],[f1572,f576,f148,f1596])).
% 15.24/2.30  fof(f1596,plain,(
% 15.24/2.30    spl10_69 <=> sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK6,k4_xboole_0(k2_tarski(sK5,sK6),sK7))),
% 15.24/2.30    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).
% 15.24/2.30  fof(f1572,plain,(
% 15.24/2.30    sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK6,k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | (~spl10_7 | ~spl10_30)),
% 15.24/2.30    inference(unit_resulting_resolution,[],[f547,f578,f48])).
% 15.24/2.30  fof(f48,plain,(
% 15.24/2.30    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X0,X2) | r2_hidden(X1,X2)) )),
% 15.24/2.30    inference(cnf_transformation,[],[f26])).
% 15.24/2.30  fof(f26,plain,(
% 15.24/2.30    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (X0 != X1 & ~r2_hidden(X0,X2)) | r2_hidden(X1,X2)) & (((X0 = X1 | r2_hidden(X0,X2)) & ~r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 15.24/2.30    inference(rectify,[],[f25])).
% 15.24/2.30  fof(f25,plain,(
% 15.24/2.30    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | ~sP0(X1,X0,X2)))),
% 15.24/2.31    inference(flattening,[],[f24])).
% 15.24/2.31  fof(f24,plain,(
% 15.24/2.31    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | ~sP0(X1,X0,X2)))),
% 15.24/2.31    inference(nnf_transformation,[],[f16])).
% 15.24/2.31  fof(f16,plain,(
% 15.24/2.31    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 15.24/2.31    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 15.24/2.31  fof(f547,plain,(
% 15.24/2.31    ( ! [X0] : (~r2_hidden(sK6,k4_xboole_0(X0,sK7))) ) | ~spl10_7),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f81,f518,f57])).
% 15.24/2.31  fof(f1594,plain,(
% 15.24/2.31    spl10_68 | spl10_19 | ~spl10_30),
% 15.24/2.31    inference(avatar_split_clause,[],[f1576,f576,f370,f1591])).
% 15.24/2.31  fof(f1591,plain,(
% 15.24/2.31    spl10_68 <=> sP1(k1_tarski(sK5),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).
% 15.24/2.31  fof(f1576,plain,(
% 15.24/2.31    sP1(k1_tarski(sK5),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | (spl10_19 | ~spl10_30)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f371,f578,f63])).
% 15.24/2.31  fof(f1589,plain,(
% 15.24/2.31    spl10_67 | spl10_29 | ~spl10_30),
% 15.24/2.31    inference(avatar_split_clause,[],[f1577,f576,f571,f1586])).
% 15.24/2.31  fof(f1586,plain,(
% 15.24/2.31    spl10_67 <=> sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_67])])).
% 15.24/2.31  fof(f1577,plain,(
% 15.24/2.31    sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | (spl10_29 | ~spl10_30)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f573,f578,f63])).
% 15.24/2.31  fof(f1584,plain,(
% 15.24/2.31    ~spl10_66 | spl10_26 | ~spl10_30),
% 15.24/2.31    inference(avatar_split_clause,[],[f1578,f576,f474,f1581])).
% 15.24/2.31  fof(f1581,plain,(
% 15.24/2.31    spl10_66 <=> sP4(sK5,sK5,sK5,k4_xboole_0(k2_tarski(sK5,sK6),sK7))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).
% 15.24/2.31  fof(f474,plain,(
% 15.24/2.31    spl10_26 <=> sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK5,sK5)),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 15.24/2.31  fof(f1578,plain,(
% 15.24/2.31    ~sP4(sK5,sK5,sK5,k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | (spl10_26 | ~spl10_30)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f476,f578,f67])).
% 15.24/2.31  fof(f476,plain,(
% 15.24/2.31    ~sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK5,sK5) | spl10_26),
% 15.24/2.31    inference(avatar_component_clause,[],[f474])).
% 15.24/2.31  fof(f1503,plain,(
% 15.24/2.31    spl10_65 | spl10_4 | ~spl10_42),
% 15.24/2.31    inference(avatar_split_clause,[],[f1482,f786,f119,f1500])).
% 15.24/2.31  fof(f1500,plain,(
% 15.24/2.31    spl10_65 <=> sP0(sK6,sK5,k4_xboole_0(sK7,k1_tarski(sK5)))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).
% 15.24/2.31  fof(f1482,plain,(
% 15.24/2.31    sP0(sK6,sK5,k4_xboole_0(sK7,k1_tarski(sK5))) | (spl10_4 | ~spl10_42)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f346,f788,f48])).
% 15.24/2.31  fof(f346,plain,(
% 15.24/2.31    ( ! [X0] : (~r2_hidden(sK5,k4_xboole_0(sK7,X0))) ) | spl10_4),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f81,f304,f57])).
% 15.24/2.31  fof(f304,plain,(
% 15.24/2.31    ( ! [X0] : (~sP1(X0,sK5,sK7)) ) | spl10_4),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f121,f61])).
% 15.24/2.31  fof(f1498,plain,(
% 15.24/2.31    spl10_64 | spl10_10 | ~spl10_42),
% 15.24/2.31    inference(avatar_split_clause,[],[f1489,f786,f214,f1495])).
% 15.24/2.31  fof(f1495,plain,(
% 15.24/2.31    spl10_64 <=> sP1(k1_tarski(sK5),sK6,k4_xboole_0(sK7,k1_tarski(sK5)))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).
% 15.24/2.31  fof(f1489,plain,(
% 15.24/2.31    sP1(k1_tarski(sK5),sK6,k4_xboole_0(sK7,k1_tarski(sK5))) | (spl10_10 | ~spl10_42)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f216,f788,f63])).
% 15.24/2.31  fof(f1472,plain,(
% 15.24/2.31    spl10_62 | ~spl10_28),
% 15.24/2.31    inference(avatar_split_clause,[],[f1455,f566,f1463])).
% 15.24/2.31  fof(f1463,plain,(
% 15.24/2.31    spl10_62 <=> sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK6,sK5,sK5)),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).
% 15.24/2.31  fof(f1455,plain,(
% 15.24/2.31    sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK6,sK5,sK5) | ~spl10_28),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f568,f235])).
% 15.24/2.31  fof(f1471,plain,(
% 15.24/2.31    spl10_63 | spl10_19 | ~spl10_28),
% 15.24/2.31    inference(avatar_split_clause,[],[f1458,f566,f370,f1468])).
% 15.24/2.31  fof(f1468,plain,(
% 15.24/2.31    spl10_63 <=> sP1(k1_tarski(sK5),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_63])])).
% 15.24/2.31  fof(f1458,plain,(
% 15.24/2.31    sP1(k1_tarski(sK5),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | (spl10_19 | ~spl10_28)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f371,f568,f63])).
% 15.24/2.31  fof(f1466,plain,(
% 15.24/2.31    spl10_62 | ~spl10_28),
% 15.24/2.31    inference(avatar_split_clause,[],[f1460,f566,f1463])).
% 15.24/2.31  fof(f1460,plain,(
% 15.24/2.31    sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK6,sK5,sK5) | ~spl10_28),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f102,f568,f67])).
% 15.24/2.31  fof(f1437,plain,(
% 15.24/2.31    ~spl10_61 | spl10_26),
% 15.24/2.31    inference(avatar_split_clause,[],[f1421,f474,f1434])).
% 15.24/2.31  fof(f1434,plain,(
% 15.24/2.31    spl10_61 <=> sP4(sK5,sK5,sK5,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).
% 15.24/2.31  fof(f1421,plain,(
% 15.24/2.31    ~sP4(sK5,sK5,sK5,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) | spl10_26),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f249,f476,f67])).
% 15.24/2.31  fof(f1342,plain,(
% 15.24/2.31    spl10_28 | ~spl10_60),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f1341])).
% 15.24/2.31  fof(f1341,plain,(
% 15.24/2.31    $false | (spl10_28 | ~spl10_60)),
% 15.24/2.31    inference(subsumption_resolution,[],[f1340,f246])).
% 15.24/2.31  fof(f1340,plain,(
% 15.24/2.31    ~r2_hidden(sK5,k2_tarski(sK5,sK6)) | (spl10_28 | ~spl10_60)),
% 15.24/2.31    inference(forward_demodulation,[],[f567,f1318])).
% 15.24/2.31  fof(f1318,plain,(
% 15.24/2.31    sK5 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) | ~spl10_60),
% 15.24/2.31    inference(avatar_component_clause,[],[f1316])).
% 15.24/2.31  fof(f567,plain,(
% 15.24/2.31    ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | spl10_28),
% 15.24/2.31    inference(avatar_component_clause,[],[f566])).
% 15.24/2.31  fof(f1339,plain,(
% 15.24/2.31    spl10_4 | spl10_20 | ~spl10_60),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f1338])).
% 15.24/2.31  fof(f1338,plain,(
% 15.24/2.31    $false | (spl10_4 | spl10_20 | ~spl10_60)),
% 15.24/2.31    inference(subsumption_resolution,[],[f1337,f246])).
% 15.24/2.31  fof(f1337,plain,(
% 15.24/2.31    ~r2_hidden(sK5,k2_tarski(sK5,sK6)) | (spl10_4 | spl10_20 | ~spl10_60)),
% 15.24/2.31    inference(forward_demodulation,[],[f1336,f1318])).
% 15.24/2.31  fof(f1336,plain,(
% 15.24/2.31    ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | (spl10_4 | spl10_20 | ~spl10_60)),
% 15.24/2.31    inference(subsumption_resolution,[],[f1335,f121])).
% 15.24/2.31  fof(f1335,plain,(
% 15.24/2.31    r2_hidden(sK5,sK7) | ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | (spl10_20 | ~spl10_60)),
% 15.24/2.31    inference(forward_demodulation,[],[f1206,f1318])).
% 15.24/2.31  fof(f1206,plain,(
% 15.24/2.31    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7) | ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | spl10_20),
% 15.24/2.31    inference(resolution,[],[f375,f63])).
% 15.24/2.31  fof(f375,plain,(
% 15.24/2.31    ~sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | spl10_20),
% 15.24/2.31    inference(avatar_component_clause,[],[f374])).
% 15.24/2.31  fof(f374,plain,(
% 15.24/2.31    spl10_20 <=> sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 15.24/2.31  fof(f1334,plain,(
% 15.24/2.31    spl10_3 | spl10_4 | ~spl10_19 | ~spl10_60),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f1333])).
% 15.24/2.31  fof(f1333,plain,(
% 15.24/2.31    $false | (spl10_3 | spl10_4 | ~spl10_19 | ~spl10_60)),
% 15.24/2.31    inference(subsumption_resolution,[],[f1332,f246])).
% 15.24/2.31  fof(f1332,plain,(
% 15.24/2.31    ~r2_hidden(sK5,k2_tarski(sK5,sK6)) | (spl10_3 | spl10_4 | ~spl10_19 | ~spl10_60)),
% 15.24/2.31    inference(forward_demodulation,[],[f1331,f1318])).
% 15.24/2.31  fof(f1331,plain,(
% 15.24/2.31    ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | (spl10_3 | spl10_4 | ~spl10_19 | ~spl10_60)),
% 15.24/2.31    inference(subsumption_resolution,[],[f1330,f121])).
% 15.24/2.31  fof(f1330,plain,(
% 15.24/2.31    r2_hidden(sK5,sK7) | ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | (spl10_3 | ~spl10_19 | ~spl10_60)),
% 15.24/2.31    inference(forward_demodulation,[],[f1323,f1318])).
% 15.24/2.31  fof(f1323,plain,(
% 15.24/2.31    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7) | ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | (spl10_3 | ~spl10_19)),
% 15.24/2.31    inference(subsumption_resolution,[],[f1177,f99])).
% 15.24/2.31  fof(f99,plain,(
% 15.24/2.31    ~sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) | spl10_3),
% 15.24/2.31    inference(avatar_component_clause,[],[f98])).
% 15.24/2.31  fof(f98,plain,(
% 15.24/2.31    spl10_3 <=> sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 15.24/2.31  fof(f1177,plain,(
% 15.24/2.31    sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) | r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7) | ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | ~spl10_19),
% 15.24/2.31    inference(resolution,[],[f372,f419])).
% 15.24/2.31  fof(f419,plain,(
% 15.24/2.31    ( ! [X2,X0,X1] : (~r2_hidden(sK8(X0,X1,X2),X2) | sP2(X0,X1,X2) | r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(sK8(X0,X1,X2),X0)) )),
% 15.24/2.31    inference(resolution,[],[f60,f63])).
% 15.24/2.31  fof(f60,plain,(
% 15.24/2.31    ( ! [X2,X0,X1] : (~sP1(X1,sK8(X0,X1,X2),X0) | sP2(X0,X1,X2) | ~r2_hidden(sK8(X0,X1,X2),X2)) )),
% 15.24/2.31    inference(cnf_transformation,[],[f33])).
% 15.24/2.31  fof(f372,plain,(
% 15.24/2.31    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5)) | ~spl10_19),
% 15.24/2.31    inference(avatar_component_clause,[],[f370])).
% 15.24/2.31  fof(f1325,plain,(
% 15.24/2.31    spl10_29 | spl10_3 | ~spl10_19 | ~spl10_28),
% 15.24/2.31    inference(avatar_split_clause,[],[f1324,f566,f370,f98,f571])).
% 15.24/2.31  fof(f1324,plain,(
% 15.24/2.31    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7) | (spl10_3 | ~spl10_19 | ~spl10_28)),
% 15.24/2.31    inference(subsumption_resolution,[],[f1323,f568])).
% 15.24/2.31  fof(f1322,plain,(
% 15.24/2.31    spl10_29 | spl10_20 | ~spl10_28),
% 15.24/2.31    inference(avatar_split_clause,[],[f1321,f566,f374,f571])).
% 15.24/2.31  fof(f1321,plain,(
% 15.24/2.31    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7) | (spl10_20 | ~spl10_28)),
% 15.24/2.31    inference(subsumption_resolution,[],[f1206,f568])).
% 15.24/2.31  fof(f1319,plain,(
% 15.24/2.31    spl10_60 | ~spl10_26),
% 15.24/2.31    inference(avatar_split_clause,[],[f1306,f474,f1316])).
% 15.24/2.31  fof(f1306,plain,(
% 15.24/2.31    sK5 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) | ~spl10_26),
% 15.24/2.31    inference(duplicate_literal_removal,[],[f1303])).
% 15.24/2.31  fof(f1303,plain,(
% 15.24/2.31    sK5 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) | sK5 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) | sK5 = sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) | ~spl10_26),
% 15.24/2.31    inference(resolution,[],[f475,f71])).
% 15.24/2.31  fof(f475,plain,(
% 15.24/2.31    sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK5,sK5) | ~spl10_26),
% 15.24/2.31    inference(avatar_component_clause,[],[f474])).
% 15.24/2.31  fof(f1292,plain,(
% 15.24/2.31    spl10_59 | spl10_40),
% 15.24/2.31    inference(avatar_split_clause,[],[f1265,f679,f1289])).
% 15.24/2.31  fof(f1289,plain,(
% 15.24/2.31    spl10_59 <=> sP0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).
% 15.24/2.31  fof(f1265,plain,(
% 15.24/2.31    sP0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) | spl10_40),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f249,f681,f48])).
% 15.24/2.31  fof(f1287,plain,(
% 15.24/2.31    spl10_58 | spl10_40),
% 15.24/2.31    inference(avatar_split_clause,[],[f1267,f679,f1284])).
% 15.24/2.31  fof(f1284,plain,(
% 15.24/2.31    spl10_58 <=> sP1(k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)),k1_tarski(sK5),k1_tarski(k1_tarski(sK5)))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).
% 15.24/2.31  fof(f1267,plain,(
% 15.24/2.31    sP1(k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)),k1_tarski(sK5),k1_tarski(k1_tarski(sK5))) | spl10_40),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f249,f681,f63])).
% 15.24/2.31  fof(f1282,plain,(
% 15.24/2.31    spl10_57 | spl10_40),
% 15.24/2.31    inference(avatar_split_clause,[],[f1277,f679,f1279])).
% 15.24/2.31  fof(f1279,plain,(
% 15.24/2.31    spl10_57 <=> sP0(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).
% 15.24/2.31  fof(f1277,plain,(
% 15.24/2.31    sP0(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) | spl10_40),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f681,f80])).
% 15.24/2.31  fof(f80,plain,(
% 15.24/2.31    ( ! [X2,X1] : (sP0(X1,X1,X2) | r2_hidden(X1,X2)) )),
% 15.24/2.31    inference(equality_resolution,[],[f49])).
% 15.24/2.31  % (9595)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 15.24/2.31  fof(f49,plain,(
% 15.24/2.31    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | X0 != X1 | r2_hidden(X1,X2)) )),
% 15.24/2.31    inference(cnf_transformation,[],[f26])).
% 15.24/2.31  fof(f1262,plain,(
% 15.24/2.31    spl10_56 | ~spl10_36),
% 15.24/2.31    inference(avatar_split_clause,[],[f1253,f625,f1257])).
% 15.24/2.31  fof(f1257,plain,(
% 15.24/2.31    spl10_56 <=> r2_hidden(sK5,k4_xboole_0(k1_tarski(sK5),k1_tarski(sK6)))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).
% 15.24/2.31  fof(f1253,plain,(
% 15.24/2.31    r2_hidden(sK5,k4_xboole_0(k1_tarski(sK5),k1_tarski(sK6))) | ~spl10_36),
% 15.24/2.31    inference(resolution,[],[f627,f218])).
% 15.24/2.31  fof(f1261,plain,(
% 15.24/2.31    spl10_56 | ~spl10_36),
% 15.24/2.31    inference(avatar_split_clause,[],[f1245,f625,f1257])).
% 15.24/2.31  fof(f1245,plain,(
% 15.24/2.31    r2_hidden(sK5,k4_xboole_0(k1_tarski(sK5),k1_tarski(sK6))) | ~spl10_36),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f627,f218])).
% 15.24/2.31  fof(f1260,plain,(
% 15.24/2.31    spl10_56 | ~spl10_36),
% 15.24/2.31    inference(avatar_split_clause,[],[f1249,f625,f1257])).
% 15.24/2.31  fof(f1249,plain,(
% 15.24/2.31    r2_hidden(sK5,k4_xboole_0(k1_tarski(sK5),k1_tarski(sK6))) | ~spl10_36),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f81,f627,f58])).
% 15.24/2.31  fof(f1244,plain,(
% 15.24/2.31    spl10_55 | spl10_4 | ~spl10_29),
% 15.24/2.31    inference(avatar_split_clause,[],[f1236,f571,f119,f1241])).
% 15.24/2.31  fof(f1241,plain,(
% 15.24/2.31    spl10_55 <=> sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK7)),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).
% 15.24/2.31  fof(f1236,plain,(
% 15.24/2.31    sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK7) | (spl10_4 | ~spl10_29)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f121,f572,f48])).
% 15.24/2.31  fof(f572,plain,(
% 15.24/2.31    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7) | ~spl10_29),
% 15.24/2.31    inference(avatar_component_clause,[],[f571])).
% 15.24/2.31  fof(f1234,plain,(
% 15.24/2.31    spl10_54 | ~spl10_35),
% 15.24/2.31    inference(avatar_split_clause,[],[f1225,f620,f1229])).
% 15.24/2.31  fof(f1229,plain,(
% 15.24/2.31    spl10_54 <=> r2_hidden(sK6,k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).
% 15.24/2.31  fof(f620,plain,(
% 15.24/2.31    spl10_35 <=> sP1(k1_tarski(sK5),sK6,k1_tarski(sK6))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).
% 15.24/2.31  fof(f1225,plain,(
% 15.24/2.31    r2_hidden(sK6,k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))) | ~spl10_35),
% 15.24/2.31    inference(resolution,[],[f622,f218])).
% 15.24/2.31  fof(f622,plain,(
% 15.24/2.31    sP1(k1_tarski(sK5),sK6,k1_tarski(sK6)) | ~spl10_35),
% 15.24/2.31    inference(avatar_component_clause,[],[f620])).
% 15.24/2.31  fof(f1233,plain,(
% 15.24/2.31    spl10_54 | ~spl10_35),
% 15.24/2.31    inference(avatar_split_clause,[],[f1218,f620,f1229])).
% 15.24/2.31  fof(f1218,plain,(
% 15.24/2.31    r2_hidden(sK6,k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))) | ~spl10_35),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f622,f218])).
% 15.24/2.31  fof(f1232,plain,(
% 15.24/2.31    spl10_54 | ~spl10_35),
% 15.24/2.31    inference(avatar_split_clause,[],[f1221,f620,f1229])).
% 15.24/2.31  fof(f1221,plain,(
% 15.24/2.31    r2_hidden(sK6,k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))) | ~spl10_35),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f81,f622,f58])).
% 15.24/2.31  fof(f1217,plain,(
% 15.24/2.31    ~spl10_30 | spl10_20),
% 15.24/2.31    inference(avatar_split_clause,[],[f1195,f374,f576])).
% 15.24/2.31  fof(f1195,plain,(
% 15.24/2.31    ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | spl10_20),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f81,f375,f57])).
% 15.24/2.31  fof(f1216,plain,(
% 15.24/2.31    ~spl10_30 | spl10_20),
% 15.24/2.31    inference(avatar_split_clause,[],[f1194,f374,f576])).
% 15.24/2.31  fof(f1194,plain,(
% 15.24/2.31    ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | spl10_20),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f375,f206])).
% 15.24/2.31  fof(f1215,plain,(
% 15.24/2.31    spl10_20 | ~spl10_30),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f1214])).
% 15.24/2.31  fof(f1214,plain,(
% 15.24/2.31    $false | (spl10_20 | ~spl10_30)),
% 15.24/2.31    inference(subsumption_resolution,[],[f1194,f578])).
% 15.24/2.31  fof(f1213,plain,(
% 15.24/2.31    spl10_20 | ~spl10_30),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f1212])).
% 15.24/2.31  fof(f1212,plain,(
% 15.24/2.31    $false | (spl10_20 | ~spl10_30)),
% 15.24/2.31    inference(subsumption_resolution,[],[f1195,f578])).
% 15.24/2.31  fof(f1211,plain,(
% 15.24/2.31    ~spl10_53 | spl10_20),
% 15.24/2.31    inference(avatar_split_clause,[],[f1197,f374,f1208])).
% 15.24/2.31  fof(f1197,plain,(
% 15.24/2.31    ~sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) | spl10_20),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f249,f375,f57])).
% 15.24/2.31  fof(f1188,plain,(
% 15.24/2.31    spl10_52 | spl10_10 | ~spl10_19),
% 15.24/2.31    inference(avatar_split_clause,[],[f1174,f370,f214,f1185])).
% 15.24/2.31  fof(f1185,plain,(
% 15.24/2.31    spl10_52 <=> sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK6,k1_tarski(sK5))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).
% 15.24/2.31  fof(f1174,plain,(
% 15.24/2.31    sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK6,k1_tarski(sK5)) | (spl10_10 | ~spl10_19)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f216,f372,f48])).
% 15.24/2.31  fof(f1183,plain,(
% 15.24/2.31    spl10_26 | ~spl10_19),
% 15.24/2.31    inference(avatar_split_clause,[],[f1176,f370,f474])).
% 15.24/2.31  fof(f1176,plain,(
% 15.24/2.31    sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK5,sK5) | ~spl10_19),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f103,f372,f67])).
% 15.24/2.31  fof(f1182,plain,(
% 15.24/2.31    spl10_26 | ~spl10_19),
% 15.24/2.31    inference(avatar_split_clause,[],[f1172,f370,f474])).
% 15.24/2.31  fof(f1172,plain,(
% 15.24/2.31    sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK5,sK5) | ~spl10_19),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f372,f236])).
% 15.24/2.31  fof(f236,plain,(
% 15.24/2.31    ( ! [X8,X7] : (sP3(X7,X8,X8,X8) | ~r2_hidden(X7,k1_tarski(X8))) )),
% 15.24/2.31    inference(resolution,[],[f67,f103])).
% 15.24/2.31  fof(f1181,plain,(
% 15.24/2.31    ~spl10_19 | spl10_26),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f1180])).
% 15.24/2.31  fof(f1180,plain,(
% 15.24/2.31    $false | (~spl10_19 | spl10_26)),
% 15.24/2.31    inference(subsumption_resolution,[],[f1172,f476])).
% 15.24/2.31  fof(f1179,plain,(
% 15.24/2.31    ~spl10_19 | spl10_26),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f1178])).
% 15.24/2.31  fof(f1178,plain,(
% 15.24/2.31    $false | (~spl10_19 | spl10_26)),
% 15.24/2.31    inference(subsumption_resolution,[],[f1176,f476])).
% 15.24/2.31  fof(f1169,plain,(
% 15.24/2.31    spl10_19 | spl10_20 | spl10_3),
% 15.24/2.31    inference(avatar_split_clause,[],[f552,f98,f374,f370])).
% 15.24/2.31  fof(f552,plain,(
% 15.24/2.31    sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5)) | spl10_3),
% 15.24/2.31    inference(resolution,[],[f99,f59])).
% 15.24/2.31  fof(f1168,plain,(
% 15.24/2.31    spl10_51 | ~spl10_7 | spl10_29),
% 15.24/2.31    inference(avatar_split_clause,[],[f1141,f571,f148,f1165])).
% 15.24/2.31  fof(f1165,plain,(
% 15.24/2.31    spl10_51 <=> sP0(sK6,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7)),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).
% 15.24/2.31  fof(f1141,plain,(
% 15.24/2.31    sP0(sK6,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7) | (~spl10_7 | spl10_29)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f150,f573,f48])).
% 15.24/2.31  fof(f1163,plain,(
% 15.24/2.31    spl10_50 | spl10_29),
% 15.24/2.31    inference(avatar_split_clause,[],[f1144,f571,f1160])).
% 15.24/2.31  fof(f1160,plain,(
% 15.24/2.31    spl10_50 <=> sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5))))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).
% 15.24/2.31  fof(f1144,plain,(
% 15.24/2.31    sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) | spl10_29),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f249,f573,f63])).
% 15.24/2.31  fof(f1158,plain,(
% 15.24/2.31    spl10_49 | spl10_29),
% 15.24/2.31    inference(avatar_split_clause,[],[f1153,f571,f1155])).
% 15.24/2.31  fof(f1155,plain,(
% 15.24/2.31    spl10_49 <=> sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7)),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).
% 15.24/2.31  fof(f1153,plain,(
% 15.24/2.31    sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7) | spl10_29),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f573,f80])).
% 15.24/2.31  fof(f1139,plain,(
% 15.24/2.31    spl10_48 | spl10_27),
% 15.24/2.31    inference(avatar_split_clause,[],[f1112,f507,f1136])).
% 15.24/2.31  fof(f1136,plain,(
% 15.24/2.31    spl10_48 <=> sP0(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5)))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).
% 15.24/2.31  fof(f1112,plain,(
% 15.24/2.31    sP0(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))) | spl10_27),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f249,f509,f48])).
% 15.24/2.31  fof(f1134,plain,(
% 15.24/2.31    spl10_47 | spl10_27),
% 15.24/2.31    inference(avatar_split_clause,[],[f1114,f507,f1131])).
% 15.24/2.31  fof(f1131,plain,(
% 15.24/2.31    spl10_47 <=> sP1(k1_tarski(k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7)))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).
% 15.24/2.31  fof(f1114,plain,(
% 15.24/2.31    sP1(k1_tarski(k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) | spl10_27),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f249,f509,f63])).
% 15.24/2.31  fof(f1129,plain,(
% 15.24/2.31    spl10_46 | spl10_27),
% 15.24/2.31    inference(avatar_split_clause,[],[f1124,f507,f1126])).
% 15.24/2.31  fof(f1126,plain,(
% 15.24/2.31    spl10_46 <=> sP0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5)))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).
% 15.24/2.31  fof(f1124,plain,(
% 15.24/2.31    sP0(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))) | spl10_27),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f509,f80])).
% 15.24/2.31  fof(f1001,plain,(
% 15.24/2.31    spl10_45 | spl10_4 | ~spl10_39),
% 15.24/2.31    inference(avatar_split_clause,[],[f980,f650,f119,f998])).
% 15.24/2.31  fof(f980,plain,(
% 15.24/2.31    sP1(sK7,sK5,k4_xboole_0(k1_tarski(sK5),sK7)) | (spl10_4 | ~spl10_39)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f121,f652,f63])).
% 15.24/2.31  fof(f996,plain,(
% 15.24/2.31    spl10_44 | spl10_22 | ~spl10_39),
% 15.24/2.31    inference(avatar_split_clause,[],[f981,f650,f430,f993])).
% 15.24/2.31  fof(f993,plain,(
% 15.24/2.31    spl10_44 <=> sP1(k1_tarski(sK6),sK5,k4_xboole_0(k1_tarski(sK5),sK7))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).
% 15.24/2.31  fof(f981,plain,(
% 15.24/2.31    sP1(k1_tarski(sK6),sK5,k4_xboole_0(k1_tarski(sK5),sK7)) | (spl10_22 | ~spl10_39)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f432,f652,f63])).
% 15.24/2.31  fof(f991,plain,(
% 15.24/2.31    spl10_43 | ~spl10_7 | ~spl10_39),
% 15.24/2.31    inference(avatar_split_clause,[],[f983,f650,f148,f988])).
% 15.24/2.31  fof(f988,plain,(
% 15.24/2.31    spl10_43 <=> sP0(sK5,sK6,k4_xboole_0(k1_tarski(sK5),sK7))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).
% 15.24/2.31  fof(f983,plain,(
% 15.24/2.31    sP0(sK5,sK6,k4_xboole_0(k1_tarski(sK5),sK7)) | (~spl10_7 | ~spl10_39)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f547,f652,f48])).
% 15.24/2.31  fof(f789,plain,(
% 15.24/2.31    spl10_42 | ~spl10_15),
% 15.24/2.31    inference(avatar_split_clause,[],[f780,f289,f786])).
% 15.24/2.31  fof(f780,plain,(
% 15.24/2.31    r2_hidden(sK6,k4_xboole_0(sK7,k1_tarski(sK5))) | ~spl10_15),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f81,f291,f58])).
% 15.24/2.31  fof(f692,plain,(
% 15.24/2.31    ~spl10_41 | spl10_18),
% 15.24/2.31    inference(avatar_split_clause,[],[f674,f336,f689])).
% 15.24/2.31  fof(f674,plain,(
% 15.24/2.31    ~sP4(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))) | spl10_18),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f249,f338,f67])).
% 15.24/2.31  fof(f338,plain,(
% 15.24/2.31    ~sP3(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | spl10_18),
% 15.24/2.31    inference(avatar_component_clause,[],[f336])).
% 15.24/2.31  fof(f687,plain,(
% 15.24/2.31    ~spl10_40 | spl10_18),
% 15.24/2.31    inference(avatar_split_clause,[],[f686,f336,f679])).
% 15.24/2.31  fof(f686,plain,(
% 15.24/2.31    ~r2_hidden(k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) | spl10_18),
% 15.24/2.31    inference(forward_demodulation,[],[f685,f52])).
% 15.24/2.31  fof(f685,plain,(
% 15.24/2.31    ~r2_hidden(k1_tarski(sK5),k2_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7))) | spl10_18),
% 15.24/2.31    inference(forward_demodulation,[],[f675,f54])).
% 15.24/2.31  fof(f675,plain,(
% 15.24/2.31    ~r2_hidden(k1_tarski(sK5),k1_enumset1(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7))) | spl10_18),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f85,f338,f67])).
% 15.24/2.31  fof(f684,plain,(
% 15.24/2.31    ~spl10_40 | spl10_18),
% 15.24/2.31    inference(avatar_split_clause,[],[f683,f336,f679])).
% 15.24/2.31  fof(f683,plain,(
% 15.24/2.31    ~r2_hidden(k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) | spl10_18),
% 15.24/2.31    inference(forward_demodulation,[],[f676,f52])).
% 15.24/2.31  fof(f676,plain,(
% 15.24/2.31    ~r2_hidden(k1_tarski(sK5),k2_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7))) | spl10_18),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f102,f338,f67])).
% 15.24/2.31  fof(f682,plain,(
% 15.24/2.31    ~spl10_40 | spl10_18),
% 15.24/2.31    inference(avatar_split_clause,[],[f677,f336,f679])).
% 15.24/2.31  fof(f677,plain,(
% 15.24/2.31    ~r2_hidden(k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) | spl10_18),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f103,f338,f67])).
% 15.24/2.31  fof(f653,plain,(
% 15.24/2.31    spl10_39 | ~spl10_37),
% 15.24/2.31    inference(avatar_split_clause,[],[f644,f630,f650])).
% 15.24/2.31  fof(f644,plain,(
% 15.24/2.31    r2_hidden(sK5,k4_xboole_0(k1_tarski(sK5),sK7)) | ~spl10_37),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f81,f632,f58])).
% 15.24/2.31  fof(f641,plain,(
% 15.24/2.31    ~spl10_19 | spl10_3 | ~spl10_20),
% 15.24/2.31    inference(avatar_split_clause,[],[f557,f374,f98,f370])).
% 15.24/2.31  fof(f557,plain,(
% 15.24/2.31    ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5)) | (spl10_3 | ~spl10_20)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f99,f376,f60])).
% 15.24/2.31  fof(f376,plain,(
% 15.24/2.31    sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | ~spl10_20),
% 15.24/2.31    inference(avatar_component_clause,[],[f374])).
% 15.24/2.31  fof(f640,plain,(
% 15.24/2.31    ~spl10_19 | spl10_3 | ~spl10_20),
% 15.24/2.31    inference(avatar_split_clause,[],[f639,f374,f98,f370])).
% 15.24/2.31  fof(f639,plain,(
% 15.24/2.31    ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5)) | (spl10_3 | ~spl10_20)),
% 15.24/2.31    inference(subsumption_resolution,[],[f562,f99])).
% 15.24/2.31  fof(f562,plain,(
% 15.24/2.31    sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) | ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5)) | ~spl10_20),
% 15.24/2.31    inference(resolution,[],[f376,f60])).
% 15.24/2.31  fof(f638,plain,(
% 15.24/2.31    ~spl10_38 | spl10_17),
% 15.24/2.31    inference(avatar_split_clause,[],[f585,f329,f635])).
% 15.24/2.31  fof(f585,plain,(
% 15.24/2.31    ~sP4(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(k4_xboole_0(k2_tarski(sK5,sK6),sK7))) | spl10_17),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f331,f249,f67])).
% 15.24/2.31  fof(f331,plain,(
% 15.24/2.31    ~sP3(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5)) | spl10_17),
% 15.24/2.31    inference(avatar_component_clause,[],[f329])).
% 15.24/2.31  fof(f633,plain,(
% 15.24/2.31    spl10_37 | spl10_4),
% 15.24/2.31    inference(avatar_split_clause,[],[f589,f119,f630])).
% 15.24/2.31  fof(f589,plain,(
% 15.24/2.31    sP1(sK7,sK5,k1_tarski(sK5)) | spl10_4),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f121,f249,f63])).
% 15.24/2.31  fof(f628,plain,(
% 15.24/2.31    spl10_36 | spl10_22),
% 15.24/2.31    inference(avatar_split_clause,[],[f590,f430,f625])).
% 15.24/2.31  fof(f590,plain,(
% 15.24/2.31    sP1(k1_tarski(sK6),sK5,k1_tarski(sK5)) | spl10_22),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f432,f249,f63])).
% 15.24/2.31  fof(f623,plain,(
% 15.24/2.31    spl10_35 | spl10_10),
% 15.24/2.31    inference(avatar_split_clause,[],[f591,f214,f620])).
% 15.24/2.31  fof(f591,plain,(
% 15.24/2.31    sP1(k1_tarski(sK5),sK6,k1_tarski(sK6)) | spl10_10),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f216,f249,f63])).
% 15.24/2.31  fof(f618,plain,(
% 15.24/2.31    spl10_34 | spl10_19),
% 15.24/2.31    inference(avatar_split_clause,[],[f592,f370,f615])).
% 15.24/2.31  fof(f592,plain,(
% 15.24/2.31    sP1(k1_tarski(sK5),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)))) | spl10_19),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f371,f249,f63])).
% 15.24/2.31  fof(f613,plain,(
% 15.24/2.31    spl10_33 | spl10_22),
% 15.24/2.31    inference(avatar_split_clause,[],[f594,f430,f610])).
% 15.24/2.31  fof(f610,plain,(
% 15.24/2.31    spl10_33 <=> sP0(sK6,sK5,k1_tarski(sK6))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).
% 15.24/2.31  fof(f594,plain,(
% 15.24/2.31    sP0(sK6,sK5,k1_tarski(sK6)) | spl10_22),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f432,f249,f48])).
% 15.24/2.31  fof(f608,plain,(
% 15.24/2.31    spl10_32 | spl10_10),
% 15.24/2.31    inference(avatar_split_clause,[],[f595,f214,f605])).
% 15.24/2.31  fof(f605,plain,(
% 15.24/2.31    spl10_32 <=> sP0(sK5,sK6,k1_tarski(sK5))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).
% 15.24/2.31  fof(f595,plain,(
% 15.24/2.31    sP0(sK5,sK6,k1_tarski(sK5)) | spl10_10),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f216,f249,f48])).
% 15.24/2.31  fof(f603,plain,(
% 15.24/2.31    spl10_31 | spl10_19),
% 15.24/2.31    inference(avatar_split_clause,[],[f596,f370,f600])).
% 15.24/2.31  fof(f600,plain,(
% 15.24/2.31    spl10_31 <=> sP0(sK5,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 15.24/2.31  fof(f596,plain,(
% 15.24/2.31    sP0(sK5,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5)) | spl10_19),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f371,f249,f48])).
% 15.24/2.31  fof(f581,plain,(
% 15.24/2.31    spl10_28 | ~spl10_20),
% 15.24/2.31    inference(avatar_split_clause,[],[f564,f374,f566])).
% 15.24/2.31  fof(f564,plain,(
% 15.24/2.31    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | ~spl10_20),
% 15.24/2.31    inference(resolution,[],[f376,f61])).
% 15.24/2.31  fof(f580,plain,(
% 15.24/2.31    ~spl10_29 | ~spl10_20),
% 15.24/2.31    inference(avatar_split_clause,[],[f563,f374,f571])).
% 15.24/2.31  fof(f563,plain,(
% 15.24/2.31    ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7) | ~spl10_20),
% 15.24/2.31    inference(resolution,[],[f376,f62])).
% 15.24/2.31  fof(f579,plain,(
% 15.24/2.31    spl10_30 | ~spl10_20),
% 15.24/2.31    inference(avatar_split_clause,[],[f558,f374,f576])).
% 15.24/2.31  fof(f558,plain,(
% 15.24/2.31    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | ~spl10_20),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f81,f376,f58])).
% 15.24/2.31  fof(f574,plain,(
% 15.24/2.31    ~spl10_29 | ~spl10_20),
% 15.24/2.31    inference(avatar_split_clause,[],[f560,f374,f571])).
% 15.24/2.31  fof(f560,plain,(
% 15.24/2.31    ~r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK7) | ~spl10_20),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f376,f62])).
% 15.24/2.31  fof(f569,plain,(
% 15.24/2.31    spl10_28 | ~spl10_20),
% 15.24/2.31    inference(avatar_split_clause,[],[f561,f374,f566])).
% 15.24/2.31  fof(f561,plain,(
% 15.24/2.31    r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | ~spl10_20),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f376,f61])).
% 15.24/2.31  fof(f514,plain,(
% 15.24/2.31    ~spl10_7 | ~spl10_9),
% 15.24/2.31    inference(avatar_split_clause,[],[f389,f162,f148])).
% 15.24/2.31  fof(f162,plain,(
% 15.24/2.31    spl10_9 <=> sP0(sK6,sK6,sK7)),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 15.24/2.31  fof(f389,plain,(
% 15.24/2.31    ~r2_hidden(sK6,sK7) | ~spl10_9),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f164,f46])).
% 15.24/2.31  fof(f46,plain,(
% 15.24/2.31    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X2)) )),
% 15.24/2.31    inference(cnf_transformation,[],[f26])).
% 15.24/2.31  fof(f164,plain,(
% 15.24/2.31    sP0(sK6,sK6,sK7) | ~spl10_9),
% 15.24/2.31    inference(avatar_component_clause,[],[f162])).
% 15.24/2.31  fof(f513,plain,(
% 15.24/2.31    ~spl10_7 | ~spl10_9),
% 15.24/2.31    inference(avatar_split_clause,[],[f391,f162,f148])).
% 15.24/2.31  fof(f391,plain,(
% 15.24/2.31    ~r2_hidden(sK6,sK7) | ~spl10_9),
% 15.24/2.31    inference(resolution,[],[f164,f46])).
% 15.24/2.31  fof(f512,plain,(
% 15.24/2.31    ~spl10_27 | spl10_17),
% 15.24/2.31    inference(avatar_split_clause,[],[f490,f329,f507])).
% 15.24/2.31  fof(f490,plain,(
% 15.24/2.31    ~r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))) | spl10_17),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f103,f331,f67])).
% 15.24/2.31  fof(f511,plain,(
% 15.24/2.31    ~spl10_27 | spl10_17),
% 15.24/2.31    inference(avatar_split_clause,[],[f495,f329,f507])).
% 15.24/2.31  fof(f495,plain,(
% 15.24/2.31    ~r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))) | spl10_17),
% 15.24/2.31    inference(forward_demodulation,[],[f489,f52])).
% 15.24/2.31  fof(f489,plain,(
% 15.24/2.31    ~r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k2_tarski(k1_tarski(sK5),k1_tarski(sK5))) | spl10_17),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f102,f331,f67])).
% 15.24/2.31  fof(f510,plain,(
% 15.24/2.31    ~spl10_27 | spl10_17),
% 15.24/2.31    inference(avatar_split_clause,[],[f500,f329,f507])).
% 15.24/2.31  fof(f500,plain,(
% 15.24/2.31    ~r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(k1_tarski(sK5))) | spl10_17),
% 15.24/2.31    inference(forward_demodulation,[],[f499,f52])).
% 15.24/2.31  fof(f499,plain,(
% 15.24/2.31    ~r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k2_tarski(k1_tarski(sK5),k1_tarski(sK5))) | spl10_17),
% 15.24/2.31    inference(forward_demodulation,[],[f488,f54])).
% 15.24/2.31  fof(f488,plain,(
% 15.24/2.31    ~r2_hidden(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_enumset1(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5))) | spl10_17),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f85,f331,f67])).
% 15.24/2.31  fof(f505,plain,(
% 15.24/2.31    ~spl10_1 | spl10_17),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f504])).
% 15.24/2.31  fof(f504,plain,(
% 15.24/2.31    $false | (~spl10_1 | spl10_17)),
% 15.24/2.31    inference(subsumption_resolution,[],[f491,f82])).
% 15.24/2.31  fof(f491,plain,(
% 15.24/2.31    ~sP3(k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5)) | (~spl10_1 | spl10_17)),
% 15.24/2.31    inference(superposition,[],[f331,f88])).
% 15.24/2.31  fof(f88,plain,(
% 15.24/2.31    k1_tarski(sK5) = k4_xboole_0(k2_tarski(sK5,sK6),sK7) | ~spl10_1),
% 15.24/2.31    inference(avatar_component_clause,[],[f87])).
% 15.24/2.31  fof(f87,plain,(
% 15.24/2.31    spl10_1 <=> k1_tarski(sK5) = k4_xboole_0(k2_tarski(sK5,sK6),sK7)),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 15.24/2.31  fof(f503,plain,(
% 15.24/2.31    ~spl10_1 | spl10_17),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f502])).
% 15.24/2.31  fof(f502,plain,(
% 15.24/2.31    $false | (~spl10_1 | spl10_17)),
% 15.24/2.31    inference(subsumption_resolution,[],[f501,f249])).
% 15.24/2.31  fof(f501,plain,(
% 15.24/2.31    ~r2_hidden(k1_tarski(sK5),k1_tarski(k1_tarski(sK5))) | (~spl10_1 | spl10_17)),
% 15.24/2.31    inference(forward_demodulation,[],[f500,f88])).
% 15.24/2.31  fof(f498,plain,(
% 15.24/2.31    ~spl10_1 | spl10_17),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f497])).
% 15.24/2.31  fof(f497,plain,(
% 15.24/2.31    $false | (~spl10_1 | spl10_17)),
% 15.24/2.31    inference(subsumption_resolution,[],[f496,f249])).
% 15.24/2.31  fof(f496,plain,(
% 15.24/2.31    ~r2_hidden(k1_tarski(sK5),k1_tarski(k1_tarski(sK5))) | (~spl10_1 | spl10_17)),
% 15.24/2.31    inference(forward_demodulation,[],[f495,f88])).
% 15.24/2.31  fof(f494,plain,(
% 15.24/2.31    ~spl10_1 | spl10_17),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f493])).
% 15.24/2.31  fof(f493,plain,(
% 15.24/2.31    $false | (~spl10_1 | spl10_17)),
% 15.24/2.31    inference(subsumption_resolution,[],[f492,f249])).
% 15.24/2.31  fof(f492,plain,(
% 15.24/2.31    ~r2_hidden(k1_tarski(sK5),k1_tarski(k1_tarski(sK5))) | (~spl10_1 | spl10_17)),
% 15.24/2.31    inference(forward_demodulation,[],[f490,f88])).
% 15.24/2.31  fof(f477,plain,(
% 15.24/2.31    ~spl10_26 | spl10_19),
% 15.24/2.31    inference(avatar_split_clause,[],[f463,f370,f474])).
% 15.24/2.31  fof(f463,plain,(
% 15.24/2.31    ~sP3(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK5,sK5,sK5) | spl10_19),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f103,f371,f68])).
% 15.24/2.31  fof(f472,plain,(
% 15.24/2.31    spl10_25 | spl10_19),
% 15.24/2.31    inference(avatar_split_clause,[],[f467,f370,f469])).
% 15.24/2.31  fof(f469,plain,(
% 15.24/2.31    spl10_25 <=> sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 15.24/2.31  fof(f467,plain,(
% 15.24/2.31    sP0(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5)) | spl10_19),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f371,f80])).
% 15.24/2.31  fof(f459,plain,(
% 15.24/2.31    ~spl10_24 | spl10_6 | spl10_22),
% 15.24/2.31    inference(avatar_split_clause,[],[f442,f430,f144,f456])).
% 15.24/2.31  fof(f456,plain,(
% 15.24/2.31    spl10_24 <=> sP0(sK5,sK6,k1_tarski(sK6))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 15.24/2.31  fof(f144,plain,(
% 15.24/2.31    spl10_6 <=> sK5 = sK6),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 15.24/2.31  fof(f442,plain,(
% 15.24/2.31    ~sP0(sK5,sK6,k1_tarski(sK6)) | (spl10_6 | spl10_22)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f145,f432,f47])).
% 15.24/2.31  fof(f47,plain,(
% 15.24/2.31    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X0,X2) | X0 = X1) )),
% 15.24/2.31    inference(cnf_transformation,[],[f26])).
% 15.24/2.31  fof(f145,plain,(
% 15.24/2.31    sK5 != sK6 | spl10_6),
% 15.24/2.31    inference(avatar_component_clause,[],[f144])).
% 15.24/2.31  fof(f454,plain,(
% 15.24/2.31    spl10_23 | spl10_22),
% 15.24/2.31    inference(avatar_split_clause,[],[f449,f430,f451])).
% 15.24/2.31  fof(f451,plain,(
% 15.24/2.31    spl10_23 <=> sP0(sK5,sK5,k1_tarski(sK6))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 15.24/2.31  fof(f449,plain,(
% 15.24/2.31    sP0(sK5,sK5,k1_tarski(sK6)) | spl10_22),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f432,f80])).
% 15.24/2.31  fof(f438,plain,(
% 15.24/2.31    ~spl10_22 | spl10_13),
% 15.24/2.31    inference(avatar_split_clause,[],[f437,f270,f430])).
% 15.24/2.31  fof(f270,plain,(
% 15.24/2.31    spl10_13 <=> sP3(sK5,sK6,sK6,sK6)),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 15.24/2.31  fof(f437,plain,(
% 15.24/2.31    ~r2_hidden(sK5,k1_tarski(sK6)) | spl10_13),
% 15.24/2.31    inference(forward_demodulation,[],[f436,f52])).
% 15.24/2.31  fof(f436,plain,(
% 15.24/2.31    ~r2_hidden(sK5,k2_tarski(sK6,sK6)) | spl10_13),
% 15.24/2.31    inference(forward_demodulation,[],[f426,f54])).
% 15.24/2.31  fof(f426,plain,(
% 15.24/2.31    ~r2_hidden(sK5,k1_enumset1(sK6,sK6,sK6)) | spl10_13),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f85,f272,f67])).
% 15.24/2.31  fof(f272,plain,(
% 15.24/2.31    ~sP3(sK5,sK6,sK6,sK6) | spl10_13),
% 15.24/2.31    inference(avatar_component_clause,[],[f270])).
% 15.24/2.31  fof(f435,plain,(
% 15.24/2.31    ~spl10_22 | spl10_13),
% 15.24/2.31    inference(avatar_split_clause,[],[f434,f270,f430])).
% 15.24/2.31  fof(f434,plain,(
% 15.24/2.31    ~r2_hidden(sK5,k1_tarski(sK6)) | spl10_13),
% 15.24/2.31    inference(forward_demodulation,[],[f427,f52])).
% 15.24/2.31  fof(f427,plain,(
% 15.24/2.31    ~r2_hidden(sK5,k2_tarski(sK6,sK6)) | spl10_13),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f102,f272,f67])).
% 15.24/2.31  fof(f433,plain,(
% 15.24/2.31    ~spl10_22 | spl10_13),
% 15.24/2.31    inference(avatar_split_clause,[],[f428,f270,f430])).
% 15.24/2.31  fof(f428,plain,(
% 15.24/2.31    ~r2_hidden(sK5,k1_tarski(sK6)) | spl10_13),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f103,f272,f67])).
% 15.24/2.31  fof(f418,plain,(
% 15.24/2.31    spl10_11),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f417])).
% 15.24/2.31  fof(f417,plain,(
% 15.24/2.31    $false | spl10_11),
% 15.24/2.31    inference(subsumption_resolution,[],[f413,f82])).
% 15.24/2.31  fof(f413,plain,(
% 15.24/2.31    ~sP3(sK5,sK5,sK5,sK5) | spl10_11),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f103,f232,f68])).
% 15.24/2.31  fof(f232,plain,(
% 15.24/2.31    ~r2_hidden(sK5,k1_tarski(sK5)) | spl10_11),
% 15.24/2.31    inference(avatar_component_clause,[],[f230])).
% 15.24/2.31  fof(f230,plain,(
% 15.24/2.31    spl10_11 <=> r2_hidden(sK5,k1_tarski(sK5))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 15.24/2.31  fof(f416,plain,(
% 15.24/2.31    spl10_11),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f414])).
% 15.24/2.31  fof(f414,plain,(
% 15.24/2.31    $false | spl10_11),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f82,f103,f232,f68])).
% 15.24/2.31  fof(f405,plain,(
% 15.24/2.31    ~spl10_21 | ~spl10_3 | spl10_10),
% 15.24/2.31    inference(avatar_split_clause,[],[f396,f214,f98,f402])).
% 15.24/2.31  fof(f396,plain,(
% 15.24/2.31    ~sP1(sK7,sK6,k2_tarski(sK5,sK6)) | (~spl10_3 | spl10_10)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f216,f100,f58])).
% 15.24/2.31  fof(f100,plain,(
% 15.24/2.31    sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) | ~spl10_3),
% 15.24/2.31    inference(avatar_component_clause,[],[f98])).
% 15.24/2.31  fof(f378,plain,(
% 15.24/2.31    ~spl10_3 | spl10_1),
% 15.24/2.31    inference(avatar_split_clause,[],[f318,f87,f98])).
% 15.24/2.31  fof(f318,plain,(
% 15.24/2.31    ~sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) | spl10_1),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f89,f65])).
% 15.24/2.31  fof(f89,plain,(
% 15.24/2.31    k1_tarski(sK5) != k4_xboole_0(k2_tarski(sK5,sK6),sK7) | spl10_1),
% 15.24/2.31    inference(avatar_component_clause,[],[f87])).
% 15.24/2.31  fof(f377,plain,(
% 15.24/2.31    spl10_19 | spl10_20 | spl10_3),
% 15.24/2.31    inference(avatar_split_clause,[],[f368,f98,f374,f370])).
% 15.24/2.31  fof(f368,plain,(
% 15.24/2.31    sP1(sK7,sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k2_tarski(sK5,sK6)) | r2_hidden(sK8(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)),k1_tarski(sK5)) | spl10_3),
% 15.24/2.31    inference(resolution,[],[f59,f99])).
% 15.24/2.31  fof(f355,plain,(
% 15.24/2.31    ~spl10_10 | spl10_12),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f354])).
% 15.24/2.31  fof(f354,plain,(
% 15.24/2.31    $false | (~spl10_10 | spl10_12)),
% 15.24/2.31    inference(subsumption_resolution,[],[f349,f267])).
% 15.24/2.31  fof(f267,plain,(
% 15.24/2.31    ~sP3(sK6,sK5,sK5,sK5) | spl10_12),
% 15.24/2.31    inference(avatar_component_clause,[],[f265])).
% 15.24/2.31  fof(f265,plain,(
% 15.24/2.31    spl10_12 <=> sP3(sK6,sK5,sK5,sK5)),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 15.24/2.31  fof(f349,plain,(
% 15.24/2.31    sP3(sK6,sK5,sK5,sK5) | ~spl10_10),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f103,f215,f67])).
% 15.24/2.31  fof(f215,plain,(
% 15.24/2.31    r2_hidden(sK6,k1_tarski(sK5)) | ~spl10_10),
% 15.24/2.31    inference(avatar_component_clause,[],[f214])).
% 15.24/2.31  fof(f341,plain,(
% 15.24/2.31    ~spl10_18 | spl10_1),
% 15.24/2.31    inference(avatar_split_clause,[],[f309,f87,f336])).
% 15.24/2.31  fof(f309,plain,(
% 15.24/2.31    ~sP3(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | spl10_1),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f89,f89,f89,f71])).
% 15.24/2.31  fof(f340,plain,(
% 15.24/2.31    ~spl10_18 | spl10_1),
% 15.24/2.31    inference(avatar_split_clause,[],[f312,f87,f336])).
% 15.24/2.31  fof(f312,plain,(
% 15.24/2.31    ~sP3(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | spl10_1),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f89,f89,f89,f71])).
% 15.24/2.31  fof(f339,plain,(
% 15.24/2.31    ~spl10_18 | spl10_1),
% 15.24/2.31    inference(avatar_split_clause,[],[f315,f87,f336])).
% 15.24/2.31  fof(f315,plain,(
% 15.24/2.31    ~sP3(k1_tarski(sK5),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7),k4_xboole_0(k2_tarski(sK5,sK6),sK7)) | spl10_1),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f89,f89,f89,f71])).
% 15.24/2.31  fof(f334,plain,(
% 15.24/2.31    ~spl10_17 | spl10_1),
% 15.24/2.31    inference(avatar_split_clause,[],[f319,f87,f329])).
% 15.24/2.31  fof(f319,plain,(
% 15.24/2.31    ~sP3(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5)) | spl10_1),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f89,f89,f89,f71])).
% 15.24/2.31  fof(f333,plain,(
% 15.24/2.31    ~spl10_17 | spl10_1),
% 15.24/2.31    inference(avatar_split_clause,[],[f322,f87,f329])).
% 15.24/2.31  fof(f322,plain,(
% 15.24/2.31    ~sP3(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5)) | spl10_1),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f89,f89,f89,f71])).
% 15.24/2.31  fof(f332,plain,(
% 15.24/2.31    ~spl10_17 | spl10_1),
% 15.24/2.31    inference(avatar_split_clause,[],[f325,f87,f329])).
% 15.24/2.31  fof(f325,plain,(
% 15.24/2.31    ~sP3(k4_xboole_0(k2_tarski(sK5,sK6),sK7),k1_tarski(sK5),k1_tarski(sK5),k1_tarski(sK5)) | spl10_1),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f89,f89,f89,f71])).
% 15.24/2.31  fof(f297,plain,(
% 15.24/2.31    ~spl10_16 | spl10_6 | spl10_10),
% 15.24/2.31    inference(avatar_split_clause,[],[f274,f214,f144,f294])).
% 15.24/2.31  fof(f294,plain,(
% 15.24/2.31    spl10_16 <=> sP0(sK6,sK5,k1_tarski(sK5))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 15.24/2.31  fof(f274,plain,(
% 15.24/2.31    ~sP0(sK6,sK5,k1_tarski(sK5)) | (spl10_6 | spl10_10)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f145,f216,f47])).
% 15.24/2.31  fof(f292,plain,(
% 15.24/2.31    spl10_15 | ~spl10_7 | spl10_10),
% 15.24/2.31    inference(avatar_split_clause,[],[f277,f214,f148,f289])).
% 15.24/2.31  fof(f277,plain,(
% 15.24/2.31    sP1(k1_tarski(sK5),sK6,sK7) | (~spl10_7 | spl10_10)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f150,f216,f63])).
% 15.24/2.31  fof(f287,plain,(
% 15.24/2.31    spl10_14 | spl10_10),
% 15.24/2.31    inference(avatar_split_clause,[],[f282,f214,f284])).
% 15.24/2.31  fof(f284,plain,(
% 15.24/2.31    spl10_14 <=> sP0(sK6,sK6,k1_tarski(sK5))),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 15.24/2.31  fof(f282,plain,(
% 15.24/2.31    sP0(sK6,sK6,k1_tarski(sK5)) | spl10_10),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f216,f80])).
% 15.24/2.31  fof(f273,plain,(
% 15.24/2.31    ~spl10_13 | spl10_6),
% 15.24/2.31    inference(avatar_split_clause,[],[f253,f144,f270])).
% 15.24/2.31  fof(f253,plain,(
% 15.24/2.31    ~sP3(sK5,sK6,sK6,sK6) | spl10_6),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f145,f145,f145,f71])).
% 15.24/2.31  fof(f268,plain,(
% 15.24/2.31    ~spl10_12 | spl10_6),
% 15.24/2.31    inference(avatar_split_clause,[],[f254,f144,f265])).
% 15.24/2.31  fof(f254,plain,(
% 15.24/2.31    ~sP3(sK6,sK5,sK5,sK5) | spl10_6),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f145,f145,f145,f71])).
% 15.24/2.31  fof(f233,plain,(
% 15.24/2.31    ~spl10_11 | ~spl10_3 | ~spl10_4),
% 15.24/2.31    inference(avatar_split_clause,[],[f225,f119,f98,f230])).
% 15.24/2.31  fof(f225,plain,(
% 15.24/2.31    ~r2_hidden(sK5,k1_tarski(sK5)) | (~spl10_3 | ~spl10_4)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f100,f194,f57])).
% 15.24/2.31  fof(f194,plain,(
% 15.24/2.31    ( ! [X0] : (~sP1(sK7,sK5,X0)) ) | ~spl10_4),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f120,f62])).
% 15.24/2.31  fof(f120,plain,(
% 15.24/2.31    r2_hidden(sK5,sK7) | ~spl10_4),
% 15.24/2.31    inference(avatar_component_clause,[],[f119])).
% 15.24/2.31  fof(f217,plain,(
% 15.24/2.31    ~spl10_10 | ~spl10_3 | ~spl10_7),
% 15.24/2.31    inference(avatar_split_clause,[],[f209,f148,f98,f214])).
% 15.24/2.31  fof(f209,plain,(
% 15.24/2.31    ~r2_hidden(sK6,k1_tarski(sK5)) | (~spl10_3 | ~spl10_7)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f100,f167,f57])).
% 15.24/2.31  fof(f167,plain,(
% 15.24/2.31    ( ! [X0] : (~sP1(sK7,sK6,X0)) ) | ~spl10_7),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f150,f62])).
% 15.24/2.31  fof(f192,plain,(
% 15.24/2.31    ~spl10_4 | ~spl10_5),
% 15.24/2.31    inference(avatar_split_clause,[],[f132,f128,f119])).
% 15.24/2.31  fof(f128,plain,(
% 15.24/2.31    spl10_5 <=> sP0(sK5,sK5,sK7)),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 15.24/2.31  fof(f132,plain,(
% 15.24/2.31    ~r2_hidden(sK5,sK7) | ~spl10_5),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f130,f46])).
% 15.24/2.31  fof(f130,plain,(
% 15.24/2.31    sP0(sK5,sK5,sK7) | ~spl10_5),
% 15.24/2.31    inference(avatar_component_clause,[],[f128])).
% 15.24/2.31  fof(f191,plain,(
% 15.24/2.31    ~spl10_4 | ~spl10_5),
% 15.24/2.31    inference(avatar_split_clause,[],[f133,f128,f119])).
% 15.24/2.31  fof(f133,plain,(
% 15.24/2.31    ~r2_hidden(sK5,sK7) | ~spl10_5),
% 15.24/2.31    inference(resolution,[],[f130,f46])).
% 15.24/2.31  fof(f190,plain,(
% 15.24/2.31    spl10_4 | spl10_2 | ~spl10_7),
% 15.24/2.31    inference(avatar_split_clause,[],[f173,f148,f91,f119])).
% 15.24/2.31  fof(f91,plain,(
% 15.24/2.31    spl10_2 <=> sP0(sK6,sK5,sK7)),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 15.24/2.31  fof(f173,plain,(
% 15.24/2.31    r2_hidden(sK5,sK7) | (spl10_2 | ~spl10_7)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f150,f93,f48])).
% 15.24/2.31  fof(f93,plain,(
% 15.24/2.31    ~sP0(sK6,sK5,sK7) | spl10_2),
% 15.24/2.31    inference(avatar_component_clause,[],[f91])).
% 15.24/2.31  fof(f189,plain,(
% 15.24/2.31    spl10_4 | spl10_2 | ~spl10_7),
% 15.24/2.31    inference(avatar_split_clause,[],[f186,f148,f91,f119])).
% 15.24/2.31  fof(f186,plain,(
% 15.24/2.31    r2_hidden(sK5,sK7) | (spl10_2 | ~spl10_7)),
% 15.24/2.31    inference(subsumption_resolution,[],[f177,f150])).
% 15.24/2.31  fof(f177,plain,(
% 15.24/2.31    ~r2_hidden(sK6,sK7) | r2_hidden(sK5,sK7) | spl10_2),
% 15.24/2.31    inference(resolution,[],[f48,f93])).
% 15.24/2.31  fof(f188,plain,(
% 15.24/2.31    spl10_2 | spl10_4 | ~spl10_7),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f187])).
% 15.24/2.31  fof(f187,plain,(
% 15.24/2.31    $false | (spl10_2 | spl10_4 | ~spl10_7)),
% 15.24/2.31    inference(subsumption_resolution,[],[f186,f121])).
% 15.24/2.31  fof(f185,plain,(
% 15.24/2.31    spl10_2 | spl10_4 | ~spl10_7),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f184])).
% 15.24/2.31  fof(f184,plain,(
% 15.24/2.31    $false | (spl10_2 | spl10_4 | ~spl10_7)),
% 15.24/2.31    inference(subsumption_resolution,[],[f171,f93])).
% 15.24/2.31  fof(f171,plain,(
% 15.24/2.31    sP0(sK6,sK5,sK7) | (spl10_4 | ~spl10_7)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f121,f150,f48])).
% 15.24/2.31  fof(f183,plain,(
% 15.24/2.31    spl10_2 | spl10_4 | ~spl10_7),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f182])).
% 15.24/2.31  fof(f182,plain,(
% 15.24/2.31    $false | (spl10_2 | spl10_4 | ~spl10_7)),
% 15.24/2.31    inference(subsumption_resolution,[],[f172,f150])).
% 15.24/2.31  fof(f172,plain,(
% 15.24/2.31    ~r2_hidden(sK6,sK7) | (spl10_2 | spl10_4)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f121,f93,f48])).
% 15.24/2.31  fof(f181,plain,(
% 15.24/2.31    spl10_2 | spl10_4 | ~spl10_7),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f180])).
% 15.24/2.31  fof(f180,plain,(
% 15.24/2.31    $false | (spl10_2 | spl10_4 | ~spl10_7)),
% 15.24/2.31    inference(subsumption_resolution,[],[f173,f121])).
% 15.24/2.31  fof(f179,plain,(
% 15.24/2.31    spl10_2 | spl10_4 | ~spl10_7),
% 15.24/2.31    inference(avatar_contradiction_clause,[],[f174])).
% 15.24/2.31  fof(f174,plain,(
% 15.24/2.31    $false | (spl10_2 | spl10_4 | ~spl10_7)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f121,f150,f93,f48])).
% 15.24/2.31  fof(f165,plain,(
% 15.24/2.31    spl10_9 | spl10_7),
% 15.24/2.31    inference(avatar_split_clause,[],[f159,f148,f162])).
% 15.24/2.31  fof(f159,plain,(
% 15.24/2.31    sP0(sK6,sK6,sK7) | spl10_7),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f149,f80])).
% 15.24/2.31  fof(f149,plain,(
% 15.24/2.31    ~r2_hidden(sK6,sK7) | spl10_7),
% 15.24/2.31    inference(avatar_component_clause,[],[f148])).
% 15.24/2.31  fof(f157,plain,(
% 15.24/2.31    ~spl10_8 | spl10_4 | spl10_6),
% 15.24/2.31    inference(avatar_split_clause,[],[f152,f144,f119,f154])).
% 15.24/2.31  fof(f154,plain,(
% 15.24/2.31    spl10_8 <=> sP0(sK5,sK6,sK7)),
% 15.24/2.31    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 15.24/2.31  fof(f152,plain,(
% 15.24/2.31    ~sP0(sK5,sK6,sK7) | (spl10_4 | spl10_6)),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f121,f145,f47])).
% 15.24/2.31  fof(f151,plain,(
% 15.24/2.31    spl10_6 | spl10_7 | ~spl10_2),
% 15.24/2.31    inference(avatar_split_clause,[],[f139,f91,f148,f144])).
% 15.24/2.31  fof(f139,plain,(
% 15.24/2.31    r2_hidden(sK6,sK7) | sK5 = sK6 | ~spl10_2),
% 15.24/2.31    inference(resolution,[],[f47,f92])).
% 15.24/2.31  fof(f92,plain,(
% 15.24/2.31    sP0(sK6,sK5,sK7) | ~spl10_2),
% 15.24/2.31    inference(avatar_component_clause,[],[f91])).
% 15.24/2.31  fof(f131,plain,(
% 15.24/2.31    spl10_5 | spl10_4),
% 15.24/2.31    inference(avatar_split_clause,[],[f125,f119,f128])).
% 15.24/2.31  fof(f125,plain,(
% 15.24/2.31    sP0(sK5,sK5,sK7) | spl10_4),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f121,f80])).
% 15.24/2.31  fof(f123,plain,(
% 15.24/2.31    ~spl10_4 | ~spl10_2),
% 15.24/2.31    inference(avatar_split_clause,[],[f117,f91,f119])).
% 15.24/2.31  fof(f117,plain,(
% 15.24/2.31    ~r2_hidden(sK5,sK7) | ~spl10_2),
% 15.24/2.31    inference(resolution,[],[f46,f92])).
% 15.24/2.31  fof(f122,plain,(
% 15.24/2.31    ~spl10_4 | ~spl10_2),
% 15.24/2.31    inference(avatar_split_clause,[],[f116,f91,f119])).
% 15.24/2.31  fof(f116,plain,(
% 15.24/2.31    ~r2_hidden(sK5,sK7) | ~spl10_2),
% 15.24/2.31    inference(unit_resulting_resolution,[],[f92,f46])).
% 15.24/2.31  fof(f101,plain,(
% 15.24/2.31    spl10_3 | ~spl10_1),
% 15.24/2.31    inference(avatar_split_clause,[],[f96,f87,f98])).
% 15.24/2.31  fof(f96,plain,(
% 15.24/2.31    sP2(k2_tarski(sK5,sK6),sK7,k1_tarski(sK5)) | ~spl10_1),
% 15.24/2.31    inference(superposition,[],[f81,f88])).
% 15.24/2.31  fof(f95,plain,(
% 15.24/2.31    spl10_1 | spl10_2),
% 15.24/2.31    inference(avatar_split_clause,[],[f50,f91,f87])).
% 15.24/2.31  fof(f50,plain,(
% 15.24/2.31    sP0(sK6,sK5,sK7) | k1_tarski(sK5) = k4_xboole_0(k2_tarski(sK5,sK6),sK7)),
% 15.24/2.31    inference(cnf_transformation,[],[f29])).
% 15.24/2.31  fof(f29,plain,(
% 15.24/2.31    (~sP0(sK6,sK5,sK7) | k1_tarski(sK5) != k4_xboole_0(k2_tarski(sK5,sK6),sK7)) & (sP0(sK6,sK5,sK7) | k1_tarski(sK5) = k4_xboole_0(k2_tarski(sK5,sK6),sK7))),
% 15.24/2.31    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f27,f28])).
% 15.24/2.31  fof(f28,plain,(
% 15.24/2.31    ? [X0,X1,X2] : ((~sP0(X1,X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (sP0(X1,X0,X2) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~sP0(sK6,sK5,sK7) | k1_tarski(sK5) != k4_xboole_0(k2_tarski(sK5,sK6),sK7)) & (sP0(sK6,sK5,sK7) | k1_tarski(sK5) = k4_xboole_0(k2_tarski(sK5,sK6),sK7)))),
% 15.24/2.31    introduced(choice_axiom,[])).
% 15.24/2.31  % (9595)Refutation not found, incomplete strategy% (9595)------------------------------
% 15.24/2.31  % (9595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.24/2.31  % (9595)Termination reason: Refutation not found, incomplete strategy
% 15.24/2.31  
% 15.24/2.31  fof(f27,plain,(
% 15.24/2.31    ? [X0,X1,X2] : ((~sP0(X1,X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) & (sP0(X1,X0,X2) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 15.24/2.31    inference(nnf_transformation,[],[f17])).
% 15.24/2.31  % (9595)Memory used [KB]: 6140
% 15.24/2.31  % (9595)Time elapsed: 0.095 s
% 15.24/2.31  % (9595)------------------------------
% 15.24/2.31  % (9595)------------------------------
% 15.24/2.31  fof(f17,plain,(
% 15.24/2.31    ? [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> sP0(X1,X0,X2))),
% 15.24/2.31    inference(definition_folding,[],[f14,f16])).
% 15.24/2.31  fof(f14,plain,(
% 15.24/2.31    ? [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 15.24/2.31    inference(ennf_transformation,[],[f13])).
% 15.24/2.31  fof(f13,negated_conjecture,(
% 15.24/2.31    ~! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 15.24/2.31    inference(negated_conjecture,[],[f12])).
% 15.24/2.31  fof(f12,conjecture,(
% 15.24/2.31    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 15.24/2.31    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_zfmisc_1)).
% 15.24/2.31  fof(f94,plain,(
% 15.24/2.31    ~spl10_1 | ~spl10_2),
% 15.24/2.31    inference(avatar_split_clause,[],[f51,f91,f87])).
% 15.24/2.31  fof(f51,plain,(
% 15.24/2.31    ~sP0(sK6,sK5,sK7) | k1_tarski(sK5) != k4_xboole_0(k2_tarski(sK5,sK6),sK7)),
% 15.24/2.31    inference(cnf_transformation,[],[f29])).
% 15.24/2.31  % SZS output end Proof for theBenchmark
% 15.24/2.31  % (9588)------------------------------
% 15.24/2.31  % (9588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.24/2.31  % (9588)Termination reason: Refutation
% 15.24/2.31  
% 15.24/2.31  % (9588)Memory used [KB]: 7675
% 15.24/2.31  % (9588)Time elapsed: 0.489 s
% 15.24/2.31  % (9588)------------------------------
% 15.24/2.31  % (9588)------------------------------
% 15.24/2.31  % (9308)Success in time 1.954 s
%------------------------------------------------------------------------------
