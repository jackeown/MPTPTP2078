%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0812+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:49 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 140 expanded)
%              Number of leaves         :   14 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  279 ( 613 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1614,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1414,f1419,f1424,f1429,f1466,f1549,f1554,f1574,f1608])).

fof(f1608,plain,
    ( ~ spl25_1
    | ~ spl25_2
    | ~ spl25_3
    | spl25_4
    | ~ spl25_9
    | ~ spl25_10
    | ~ spl25_11 ),
    inference(avatar_contradiction_clause,[],[f1607])).

fof(f1607,plain,
    ( $false
    | ~ spl25_1
    | ~ spl25_2
    | ~ spl25_3
    | spl25_4
    | ~ spl25_9
    | ~ spl25_10
    | ~ spl25_11 ),
    inference(subsumption_resolution,[],[f1606,f1413])).

fof(f1413,plain,
    ( v1_relat_1(sK1)
    | ~ spl25_1 ),
    inference(avatar_component_clause,[],[f1411])).

fof(f1411,plain,
    ( spl25_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_1])])).

fof(f1606,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl25_2
    | ~ spl25_3
    | spl25_4
    | ~ spl25_9
    | ~ spl25_10
    | ~ spl25_11 ),
    inference(subsumption_resolution,[],[f1605,f1418])).

fof(f1418,plain,
    ( v1_relat_1(sK2)
    | ~ spl25_2 ),
    inference(avatar_component_clause,[],[f1416])).

fof(f1416,plain,
    ( spl25_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_2])])).

fof(f1605,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl25_3
    | spl25_4
    | ~ spl25_9
    | ~ spl25_10
    | ~ spl25_11 ),
    inference(subsumption_resolution,[],[f1604,f1548])).

fof(f1548,plain,
    ( v1_relat_1(sK23(sK1,sK2))
    | ~ spl25_9 ),
    inference(avatar_component_clause,[],[f1546])).

fof(f1546,plain,
    ( spl25_9
  <=> v1_relat_1(sK23(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_9])])).

fof(f1604,plain,
    ( ~ v1_relat_1(sK23(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl25_3
    | spl25_4
    | ~ spl25_10
    | ~ spl25_11 ),
    inference(subsumption_resolution,[],[f1603,f1553])).

fof(f1553,plain,
    ( v1_funct_1(sK23(sK1,sK2))
    | ~ spl25_10 ),
    inference(avatar_component_clause,[],[f1551])).

fof(f1551,plain,
    ( spl25_10
  <=> v1_funct_1(sK23(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_10])])).

fof(f1603,plain,
    ( ~ v1_funct_1(sK23(sK1,sK2))
    | ~ v1_relat_1(sK23(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl25_3
    | spl25_4
    | ~ spl25_11 ),
    inference(subsumption_resolution,[],[f1602,f1423])).

fof(f1423,plain,
    ( v2_wellord1(sK1)
    | ~ spl25_3 ),
    inference(avatar_component_clause,[],[f1421])).

fof(f1421,plain,
    ( spl25_3
  <=> v2_wellord1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_3])])).

fof(f1602,plain,
    ( ~ v2_wellord1(sK1)
    | ~ v1_funct_1(sK23(sK1,sK2))
    | ~ v1_relat_1(sK23(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | spl25_4
    | ~ spl25_11 ),
    inference(subsumption_resolution,[],[f1579,f1428])).

fof(f1428,plain,
    ( ~ v2_wellord1(sK2)
    | spl25_4 ),
    inference(avatar_component_clause,[],[f1426])).

fof(f1426,plain,
    ( spl25_4
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_4])])).

fof(f1579,plain,
    ( v2_wellord1(sK2)
    | ~ v2_wellord1(sK1)
    | ~ v1_funct_1(sK23(sK1,sK2))
    | ~ v1_relat_1(sK23(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl25_11 ),
    inference(resolution,[],[f1573,f1364])).

fof(f1364,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | v2_wellord1(X1)
      | ~ v2_wellord1(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1247])).

fof(f1247,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_wellord1(X1)
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v2_wellord1(X0)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1246])).

fof(f1246,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_wellord1(X1)
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v2_wellord1(X0)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1196])).

fof(f1196,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => v2_wellord1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_wellord1)).

fof(f1573,plain,
    ( r3_wellord1(sK1,sK2,sK23(sK1,sK2))
    | ~ spl25_11 ),
    inference(avatar_component_clause,[],[f1571])).

fof(f1571,plain,
    ( spl25_11
  <=> r3_wellord1(sK1,sK2,sK23(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_11])])).

fof(f1574,plain,
    ( spl25_11
    | ~ spl25_1
    | ~ spl25_2
    | ~ spl25_5 ),
    inference(avatar_split_clause,[],[f1479,f1463,f1416,f1411,f1571])).

fof(f1463,plain,
    ( spl25_5
  <=> r4_wellord1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_5])])).

fof(f1479,plain,
    ( r3_wellord1(sK1,sK2,sK23(sK1,sK2))
    | ~ spl25_1
    | ~ spl25_2
    | ~ spl25_5 ),
    inference(subsumption_resolution,[],[f1478,f1413])).

fof(f1478,plain,
    ( r3_wellord1(sK1,sK2,sK23(sK1,sK2))
    | ~ v1_relat_1(sK1)
    | ~ spl25_2
    | ~ spl25_5 ),
    inference(subsumption_resolution,[],[f1470,f1418])).

fof(f1470,plain,
    ( r3_wellord1(sK1,sK2,sK23(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl25_5 ),
    inference(resolution,[],[f1465,f1399])).

fof(f1399,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,X1)
      | r3_wellord1(X0,X1,sK23(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1325])).

fof(f1325,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ( r3_wellord1(X0,X1,sK23(X0,X1))
                & v1_funct_1(sK23(X0,X1))
                & v1_relat_1(sK23(X0,X1)) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f1323,f1324])).

fof(f1324,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r3_wellord1(X0,X1,X3)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( r3_wellord1(X0,X1,sK23(X0,X1))
        & v1_funct_1(sK23(X0,X1))
        & v1_relat_1(sK23(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1323,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ? [X3] :
                  ( r3_wellord1(X0,X1,X3)
                  & v1_funct_1(X3)
                  & v1_relat_1(X3) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1322])).

fof(f1322,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ? [X2] :
                  ( r3_wellord1(X0,X1,X2)
                  & v1_funct_1(X2)
                  & v1_relat_1(X2) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1268])).

fof(f1268,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1138])).

fof(f1138,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).

fof(f1465,plain,
    ( r4_wellord1(sK1,sK2)
    | ~ spl25_5 ),
    inference(avatar_component_clause,[],[f1463])).

fof(f1554,plain,
    ( spl25_10
    | ~ spl25_1
    | ~ spl25_2
    | ~ spl25_5 ),
    inference(avatar_split_clause,[],[f1477,f1463,f1416,f1411,f1551])).

fof(f1477,plain,
    ( v1_funct_1(sK23(sK1,sK2))
    | ~ spl25_1
    | ~ spl25_2
    | ~ spl25_5 ),
    inference(subsumption_resolution,[],[f1476,f1413])).

fof(f1476,plain,
    ( v1_funct_1(sK23(sK1,sK2))
    | ~ v1_relat_1(sK1)
    | ~ spl25_2
    | ~ spl25_5 ),
    inference(subsumption_resolution,[],[f1469,f1418])).

fof(f1469,plain,
    ( v1_funct_1(sK23(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl25_5 ),
    inference(resolution,[],[f1465,f1398])).

fof(f1398,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,X1)
      | v1_funct_1(sK23(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1325])).

fof(f1549,plain,
    ( spl25_9
    | ~ spl25_1
    | ~ spl25_2
    | ~ spl25_5 ),
    inference(avatar_split_clause,[],[f1475,f1463,f1416,f1411,f1546])).

fof(f1475,plain,
    ( v1_relat_1(sK23(sK1,sK2))
    | ~ spl25_1
    | ~ spl25_2
    | ~ spl25_5 ),
    inference(subsumption_resolution,[],[f1474,f1413])).

fof(f1474,plain,
    ( v1_relat_1(sK23(sK1,sK2))
    | ~ v1_relat_1(sK1)
    | ~ spl25_2
    | ~ spl25_5 ),
    inference(subsumption_resolution,[],[f1468,f1418])).

fof(f1468,plain,
    ( v1_relat_1(sK23(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl25_5 ),
    inference(resolution,[],[f1465,f1397])).

fof(f1397,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,X1)
      | v1_relat_1(sK23(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1325])).

fof(f1466,plain,(
    spl25_5 ),
    inference(avatar_split_clause,[],[f1330,f1463])).

fof(f1330,plain,(
    r4_wellord1(sK1,sK2) ),
    inference(cnf_transformation,[],[f1278])).

fof(f1278,plain,
    ( ~ v2_wellord1(sK2)
    & v2_wellord1(sK1)
    & r4_wellord1(sK1,sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f1217,f1277,f1276])).

fof(f1276,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_wellord1(X1)
            & v2_wellord1(X0)
            & r4_wellord1(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(sK1)
          & r4_wellord1(sK1,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1277,plain,
    ( ? [X1] :
        ( ~ v2_wellord1(X1)
        & v2_wellord1(sK1)
        & r4_wellord1(sK1,X1)
        & v1_relat_1(X1) )
   => ( ~ v2_wellord1(sK2)
      & v2_wellord1(sK1)
      & r4_wellord1(sK1,sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f1217,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1216])).

fof(f1216,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1208])).

fof(f1208,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( v2_wellord1(X0)
                & r4_wellord1(X0,X1) )
             => v2_wellord1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1207])).

fof(f1207,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( v2_wellord1(X0)
              & r4_wellord1(X0,X1) )
           => v2_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_wellord1)).

fof(f1429,plain,(
    ~ spl25_4 ),
    inference(avatar_split_clause,[],[f1332,f1426])).

fof(f1332,plain,(
    ~ v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f1278])).

fof(f1424,plain,(
    spl25_3 ),
    inference(avatar_split_clause,[],[f1331,f1421])).

fof(f1331,plain,(
    v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f1278])).

fof(f1419,plain,(
    spl25_2 ),
    inference(avatar_split_clause,[],[f1329,f1416])).

fof(f1329,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1278])).

fof(f1414,plain,(
    spl25_1 ),
    inference(avatar_split_clause,[],[f1328,f1411])).

fof(f1328,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1278])).
%------------------------------------------------------------------------------
