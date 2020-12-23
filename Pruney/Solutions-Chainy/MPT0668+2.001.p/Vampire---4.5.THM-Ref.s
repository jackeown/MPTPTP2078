%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  273 ( 865 expanded)
%              Number of leaves         :   57 ( 390 expanded)
%              Depth                    :   13
%              Number of atoms          : 1160 (6156 expanded)
%              Number of equality atoms :  129 ( 953 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1357,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f71,f73,f77,f78,f79,f84,f88,f92,f96,f100,f104,f108,f112,f120,f125,f134,f142,f146,f157,f180,f191,f206,f213,f218,f231,f246,f258,f590,f861,f865,f867,f871,f888,f893,f895,f916,f938,f942,f962,f1052,f1057,f1060,f1077,f1090,f1091,f1225,f1232,f1235,f1236,f1239,f1293,f1294,f1295,f1301,f1302,f1312,f1338,f1351,f1354,f1356])).

fof(f1356,plain,
    ( ~ spl7_17
    | ~ spl7_35 ),
    inference(avatar_contradiction_clause,[],[f1355])).

fof(f1355,plain,
    ( $false
    | ~ spl7_17
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f261,f133])).

fof(f133,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK4,X0),sK2)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl7_17
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK4,X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f261,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK2)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl7_35
  <=> r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f1354,plain,
    ( ~ spl7_12
    | ~ spl7_11
    | spl7_36
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f1330,f260,f264,f98,f102])).

fof(f102,plain,
    ( spl7_12
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f98,plain,
    ( spl7_11
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f264,plain,
    ( spl7_36
  <=> k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f1330,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_35 ),
    inference(resolution,[],[f261,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f1351,plain,
    ( ~ spl7_2
    | ~ spl7_19
    | ~ spl7_21
    | spl7_168 ),
    inference(avatar_split_clause,[],[f1348,f1336,f155,f144,f57])).

fof(f57,plain,
    ( spl7_2
  <=> r2_hidden(sK4,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f144,plain,
    ( spl7_19
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f155,plain,
    ( spl7_21
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f1336,plain,
    ( spl7_168
  <=> r2_hidden(k1_funct_1(sK1,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_168])])).

fof(f1348,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK1))
    | ~ spl7_19
    | ~ spl7_21
    | spl7_168 ),
    inference(resolution,[],[f192,f1337])).

fof(f1337,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK4),sK0)
    | spl7_168 ),
    inference(avatar_component_clause,[],[f1336])).

fof(f192,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK1,X0),sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(resolution,[],[f156,f145])).

fof(f145,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK1)
        | ~ r2_hidden(X1,k1_relat_1(sK1)) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f144])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X1,sK0) )
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f155])).

fof(f1338,plain,
    ( ~ spl7_168
    | spl7_4
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f1331,f264,f63,f1336])).

fof(f63,plain,
    ( spl7_4
  <=> r2_hidden(k1_funct_1(sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1331,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK4),sK0)
    | spl7_4
    | ~ spl7_36 ),
    inference(superposition,[],[f64,f265])).

fof(f265,plain,
    ( k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4)
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f264])).

fof(f64,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f1312,plain,
    ( spl7_35
    | ~ spl7_2
    | ~ spl7_19
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f1310,f189,f144,f57,f260])).

fof(f189,plain,
    ( spl7_26
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(k4_tarski(X0,X1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f1310,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK2)
    | ~ spl7_2
    | ~ spl7_19
    | ~ spl7_26 ),
    inference(resolution,[],[f69,f193])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK2) )
    | ~ spl7_19
    | ~ spl7_26 ),
    inference(resolution,[],[f190,f145])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(k4_tarski(X0,X1),sK2) )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f189])).

fof(f69,plain,
    ( r2_hidden(sK4,k1_relat_1(sK1))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f1302,plain,
    ( k1_funct_1(sK1,sK5(sK0,sK2,sK1)) != k1_funct_1(sK2,sK5(sK0,sK2,sK1))
    | r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK1,sK5(sK0,sK2,sK1))),sK2)
    | ~ r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK2,sK5(sK0,sK2,sK1))),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1301,plain,
    ( ~ spl7_12
    | ~ spl7_11
    | spl7_120
    | ~ spl7_112 ),
    inference(avatar_split_clause,[],[f1300,f856,f890,f98,f102])).

fof(f890,plain,
    ( spl7_120
  <=> sK6(sK0,sK2,sK1) = k1_funct_1(sK2,sK5(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f856,plain,
    ( spl7_112
  <=> r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f1300,plain,
    ( sK6(sK0,sK2,sK1) = k1_funct_1(sK2,sK5(sK0,sK2,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_112 ),
    inference(resolution,[],[f872,f47])).

fof(f872,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK2)
    | ~ spl7_112 ),
    inference(avatar_component_clause,[],[f856])).

fof(f1295,plain,
    ( spl7_114
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_150 ),
    inference(avatar_split_clause,[],[f1243,f1088,f144,f118,f863])).

fof(f863,plain,
    ( spl7_114
  <=> k1_funct_1(sK1,sK5(sK0,sK2,sK1)) = k1_funct_1(sK2,sK5(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).

fof(f118,plain,
    ( spl7_15
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f1088,plain,
    ( spl7_150
  <=> r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_150])])).

fof(f1243,plain,
    ( k1_funct_1(sK1,sK5(sK0,sK2,sK1)) = k1_funct_1(sK2,sK5(sK0,sK2,sK1))
    | ~ spl7_15
    | ~ spl7_19
    | ~ spl7_150 ),
    inference(resolution,[],[f1221,f175])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) )
    | ~ spl7_15
    | ~ spl7_19 ),
    inference(resolution,[],[f119,f145])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f118])).

fof(f1221,plain,
    ( r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK1))
    | ~ spl7_150 ),
    inference(avatar_component_clause,[],[f1088])).

fof(f1294,plain,
    ( spl7_115
    | ~ spl7_10
    | ~ spl7_18
    | ~ spl7_150 ),
    inference(avatar_split_clause,[],[f1244,f1088,f140,f94,f869])).

fof(f869,plain,
    ( spl7_115
  <=> r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK2,sK5(sK0,sK2,sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).

fof(f94,plain,
    ( spl7_10
  <=> ! [X6] :
        ( r2_hidden(X6,k1_relat_1(sK2))
        | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f140,plain,
    ( spl7_18
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f1244,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK2,sK5(sK0,sK2,sK1))),sK2)
    | ~ spl7_10
    | ~ spl7_18
    | ~ spl7_150 ),
    inference(resolution,[],[f1221,f161])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) )
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(resolution,[],[f95,f141])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f140])).

fof(f95,plain,
    ( ! [X6] :
        ( r2_hidden(X6,k1_relat_1(sK2))
        | ~ r2_hidden(X6,k1_relat_1(sK1)) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f1293,plain,
    ( spl7_111
    | spl7_1
    | ~ spl7_12
    | ~ spl7_14
    | spl7_112 ),
    inference(avatar_split_clause,[],[f1292,f856,f110,f102,f54,f841])).

fof(f841,plain,
    ( spl7_111
  <=> r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_111])])).

fof(f54,plain,
    ( spl7_1
  <=> sK1 = k8_relat_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f110,plain,
    ( spl7_14
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f1292,plain,
    ( sK1 = k8_relat_1(sK0,sK2)
    | r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1)
    | ~ spl7_12
    | ~ spl7_14
    | spl7_112 ),
    inference(resolution,[],[f857,f578])).

fof(f578,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK5(X0,sK2,sK1),sK6(X0,sK2,sK1)),sK2)
        | sK1 = k8_relat_1(X0,sK2)
        | r2_hidden(k4_tarski(sK5(X0,sK2,sK1),sK6(X0,sK2,sK1)),sK1) )
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(resolution,[],[f309,f103])).

fof(f103,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f102])).

fof(f309,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X3)
        | r2_hidden(k4_tarski(sK5(X2,X3,sK1),sK6(X2,X3,sK1)),sK1)
        | sK1 = k8_relat_1(X2,X3)
        | r2_hidden(k4_tarski(sK5(X2,X3,sK1),sK6(X2,X3,sK1)),X3) )
    | ~ spl7_14 ),
    inference(resolution,[],[f44,f111])).

fof(f111,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | k8_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK6(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
                    & r2_hidden(sK6(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(f857,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK2)
    | spl7_112 ),
    inference(avatar_component_clause,[],[f856])).

fof(f1239,plain,
    ( ~ spl7_12
    | ~ spl7_11
    | spl7_119
    | ~ spl7_112
    | ~ spl7_114 ),
    inference(avatar_split_clause,[],[f1238,f863,f856,f886,f98,f102])).

fof(f886,plain,
    ( spl7_119
  <=> sK6(sK0,sK2,sK1) = k1_funct_1(sK1,sK5(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).

fof(f1238,plain,
    ( sK6(sK0,sK2,sK1) = k1_funct_1(sK1,sK5(sK0,sK2,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_112
    | ~ spl7_114 ),
    inference(forward_demodulation,[],[f899,f864])).

fof(f864,plain,
    ( k1_funct_1(sK1,sK5(sK0,sK2,sK1)) = k1_funct_1(sK2,sK5(sK0,sK2,sK1))
    | ~ spl7_114 ),
    inference(avatar_component_clause,[],[f863])).

fof(f899,plain,
    ( sK6(sK0,sK2,sK1) = k1_funct_1(sK2,sK5(sK0,sK2,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_112 ),
    inference(resolution,[],[f872,f47])).

fof(f1236,plain,
    ( ~ spl7_112
    | ~ spl7_160 ),
    inference(avatar_contradiction_clause,[],[f1234])).

fof(f1234,plain,
    ( $false
    | ~ spl7_112
    | ~ spl7_160 ),
    inference(subsumption_resolution,[],[f872,f1231])).

fof(f1231,plain,
    ( ! [X1] : ~ r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),X1),sK2)
    | ~ spl7_160 ),
    inference(avatar_component_clause,[],[f1230])).

fof(f1230,plain,
    ( spl7_160
  <=> ! [X1] : ~ r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),X1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_160])])).

fof(f1235,plain,
    ( ~ spl7_115
    | ~ spl7_160 ),
    inference(avatar_contradiction_clause,[],[f1233])).

fof(f1233,plain,
    ( $false
    | ~ spl7_115
    | ~ spl7_160 ),
    inference(subsumption_resolution,[],[f870,f1231])).

fof(f870,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK2,sK5(sK0,sK2,sK1))),sK2)
    | ~ spl7_115 ),
    inference(avatar_component_clause,[],[f869])).

fof(f1232,plain,
    ( ~ spl7_12
    | ~ spl7_11
    | spl7_160
    | spl7_159 ),
    inference(avatar_split_clause,[],[f1228,f1223,f1230,f98,f102])).

fof(f1223,plain,
    ( spl7_159
  <=> r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_159])])).

fof(f1228,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),X1),sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | spl7_159 ),
    inference(resolution,[],[f1224,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1224,plain,
    ( ~ r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK2))
    | spl7_159 ),
    inference(avatar_component_clause,[],[f1223])).

fof(f1225,plain,
    ( spl7_150
    | ~ spl7_159
    | ~ spl7_113
    | ~ spl7_8
    | ~ spl7_120 ),
    inference(avatar_split_clause,[],[f1219,f890,f86,f859,f1223,f1088])).

fof(f859,plain,
    ( spl7_113
  <=> r2_hidden(sK6(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).

fof(f86,plain,
    ( spl7_8
  <=> ! [X6] :
        ( r2_hidden(X6,k1_relat_1(sK1))
        | ~ r2_hidden(X6,k1_relat_1(sK2))
        | ~ r2_hidden(k1_funct_1(sK2,X6),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1219,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK1),sK0)
    | ~ r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK2))
    | r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK1))
    | ~ spl7_8
    | ~ spl7_120 ),
    inference(superposition,[],[f87,f891])).

fof(f891,plain,
    ( sK6(sK0,sK2,sK1) = k1_funct_1(sK2,sK5(sK0,sK2,sK1))
    | ~ spl7_120 ),
    inference(avatar_component_clause,[],[f890])).

fof(f87,plain,
    ( ! [X6] :
        ( ~ r2_hidden(k1_funct_1(sK2,X6),sK0)
        | ~ r2_hidden(X6,k1_relat_1(sK2))
        | r2_hidden(X6,k1_relat_1(sK1)) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f1091,plain,
    ( spl7_111
    | spl7_1
    | ~ spl7_12
    | ~ spl7_14
    | spl7_113 ),
    inference(avatar_split_clause,[],[f896,f859,f110,f102,f54,f841])).

fof(f896,plain,
    ( sK1 = k8_relat_1(sK0,sK2)
    | r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1)
    | ~ spl7_12
    | ~ spl7_14
    | spl7_113 ),
    inference(resolution,[],[f860,f310])).

fof(f310,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(X0,sK2,sK1),X0)
        | sK1 = k8_relat_1(X0,sK2)
        | r2_hidden(k4_tarski(sK5(X0,sK2,sK1),sK6(X0,sK2,sK1)),sK1) )
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(resolution,[],[f287,f103])).

fof(f287,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X3)
        | r2_hidden(k4_tarski(sK5(X2,X3,sK1),sK6(X2,X3,sK1)),sK1)
        | sK1 = k8_relat_1(X2,X3)
        | r2_hidden(sK6(X2,X3,sK1),X2) )
    | ~ spl7_14 ),
    inference(resolution,[],[f43,f111])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | k8_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f860,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK1),sK0)
    | spl7_113 ),
    inference(avatar_component_clause,[],[f859])).

fof(f1090,plain,
    ( ~ spl7_150
    | spl7_111
    | ~ spl7_19
    | ~ spl7_119 ),
    inference(avatar_split_clause,[],[f900,f886,f144,f841,f1088])).

fof(f900,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1)
    | ~ r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK1))
    | ~ spl7_19
    | ~ spl7_119 ),
    inference(superposition,[],[f145,f887])).

fof(f887,plain,
    ( sK6(sK0,sK2,sK1) = k1_funct_1(sK1,sK5(sK0,sK2,sK1))
    | ~ spl7_119 ),
    inference(avatar_component_clause,[],[f886])).

fof(f1077,plain,
    ( spl7_21
    | ~ spl7_14
    | ~ spl7_123 ),
    inference(avatar_split_clause,[],[f1074,f932,f110,f155])).

fof(f932,plain,
    ( spl7_123
  <=> sK1 = k8_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_123])])).

fof(f1074,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(X4,X5),sK1)
        | r2_hidden(X5,sK0) )
    | ~ spl7_123 ),
    inference(duplicate_literal_removal,[],[f1073])).

fof(f1073,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(X4,X5),sK1)
        | r2_hidden(X5,sK0)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_123 ),
    inference(superposition,[],[f51,f933])).

fof(f933,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | ~ spl7_123 ),
    inference(avatar_component_clause,[],[f932])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(X6,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1060,plain,
    ( ~ spl7_121
    | ~ spl7_146 ),
    inference(avatar_contradiction_clause,[],[f1058])).

fof(f1058,plain,
    ( $false
    | ~ spl7_121
    | ~ spl7_146 ),
    inference(subsumption_resolution,[],[f915,f1056])).

fof(f1056,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK5(sK0,sK1,sK1),X0),sK1)
    | ~ spl7_146 ),
    inference(avatar_component_clause,[],[f1055])).

fof(f1055,plain,
    ( spl7_146
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK5(sK0,sK1,sK1),X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_146])])).

fof(f915,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK1,sK1),sK6(sK0,sK1,sK1)),sK1)
    | ~ spl7_121 ),
    inference(avatar_component_clause,[],[f914])).

fof(f914,plain,
    ( spl7_121
  <=> r2_hidden(k4_tarski(sK5(sK0,sK1,sK1),sK6(sK0,sK1,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_121])])).

fof(f1057,plain,
    ( ~ spl7_14
    | ~ spl7_13
    | spl7_146
    | spl7_145 ),
    inference(avatar_split_clause,[],[f1053,f1049,f1055,f106,f110])).

fof(f106,plain,
    ( spl7_13
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f1049,plain,
    ( spl7_145
  <=> r2_hidden(sK5(sK0,sK1,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_145])])).

fof(f1053,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK5(sK0,sK1,sK1),X0),sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | spl7_145 ),
    inference(resolution,[],[f1050,f46])).

fof(f1050,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK1),k1_relat_1(sK1))
    | spl7_145 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f1052,plain,
    ( ~ spl7_145
    | spl7_124
    | ~ spl7_9
    | ~ spl7_82
    | ~ spl7_125 ),
    inference(avatar_split_clause,[],[f1047,f940,f563,f90,f936,f1049])).

fof(f936,plain,
    ( spl7_124
  <=> r2_hidden(sK6(sK0,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f90,plain,
    ( spl7_9
  <=> ! [X6] :
        ( r2_hidden(k1_funct_1(sK2,X6),sK0)
        | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f563,plain,
    ( spl7_82
  <=> sK6(sK0,sK1,sK1) = k1_funct_1(sK1,sK5(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f940,plain,
    ( spl7_125
  <=> k1_funct_1(sK1,sK5(sK0,sK1,sK1)) = k1_funct_1(sK2,sK5(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_125])])).

fof(f1047,plain,
    ( r2_hidden(sK6(sK0,sK1,sK1),sK0)
    | ~ r2_hidden(sK5(sK0,sK1,sK1),k1_relat_1(sK1))
    | ~ spl7_9
    | ~ spl7_82
    | ~ spl7_125 ),
    inference(forward_demodulation,[],[f1044,f564])).

fof(f564,plain,
    ( sK6(sK0,sK1,sK1) = k1_funct_1(sK1,sK5(sK0,sK1,sK1))
    | ~ spl7_82 ),
    inference(avatar_component_clause,[],[f563])).

fof(f1044,plain,
    ( r2_hidden(k1_funct_1(sK1,sK5(sK0,sK1,sK1)),sK0)
    | ~ r2_hidden(sK5(sK0,sK1,sK1),k1_relat_1(sK1))
    | ~ spl7_9
    | ~ spl7_125 ),
    inference(superposition,[],[f91,f941])).

fof(f941,plain,
    ( k1_funct_1(sK1,sK5(sK0,sK1,sK1)) = k1_funct_1(sK2,sK5(sK0,sK1,sK1))
    | ~ spl7_125 ),
    inference(avatar_component_clause,[],[f940])).

fof(f91,plain,
    ( ! [X6] :
        ( r2_hidden(k1_funct_1(sK2,X6),sK0)
        | ~ r2_hidden(X6,k1_relat_1(sK1)) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f90])).

fof(f962,plain,
    ( ~ spl7_14
    | ~ spl7_13
    | spl7_82
    | ~ spl7_121 ),
    inference(avatar_split_clause,[],[f930,f914,f563,f106,f110])).

fof(f930,plain,
    ( sK6(sK0,sK1,sK1) = k1_funct_1(sK1,sK5(sK0,sK1,sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_121 ),
    inference(resolution,[],[f915,f47])).

fof(f942,plain,
    ( spl7_125
    | ~ spl7_15
    | ~ spl7_121 ),
    inference(avatar_split_clause,[],[f922,f914,f118,f940])).

fof(f922,plain,
    ( k1_funct_1(sK1,sK5(sK0,sK1,sK1)) = k1_funct_1(sK2,sK5(sK0,sK1,sK1))
    | ~ spl7_15
    | ~ spl7_121 ),
    inference(resolution,[],[f915,f119])).

fof(f938,plain,
    ( ~ spl7_14
    | spl7_123
    | ~ spl7_121
    | ~ spl7_124
    | ~ spl7_14
    | ~ spl7_121 ),
    inference(avatar_split_clause,[],[f921,f914,f110,f936,f914,f932,f110])).

fof(f921,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK5(sK0,sK1,sK1),sK6(sK0,sK1,sK1)),sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_14
    | ~ spl7_121 ),
    inference(resolution,[],[f915,f422])).

fof(f422,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(sK5(X2,X3,sK1),sK6(X2,X3,sK1)),sK1)
        | ~ r2_hidden(sK6(X2,X3,sK1),X2)
        | ~ r2_hidden(k4_tarski(sK5(X2,X3,sK1),sK6(X2,X3,sK1)),X3)
        | sK1 = k8_relat_1(X2,X3)
        | ~ v1_relat_1(X3) )
    | ~ spl7_14 ),
    inference(resolution,[],[f45,f111])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)
      | k8_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f916,plain,
    ( spl7_121
    | ~ spl7_84
    | ~ spl7_111
    | spl7_113 ),
    inference(avatar_split_clause,[],[f905,f859,f841,f588,f914])).

fof(f588,plain,
    ( spl7_84
  <=> ! [X9,X7,X8] :
        ( ~ r2_hidden(k4_tarski(X8,X9),sK1)
        | r2_hidden(k4_tarski(sK5(X7,sK1,sK1),sK6(X7,sK1,sK1)),sK1)
        | r2_hidden(X9,X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f905,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK1,sK1),sK6(sK0,sK1,sK1)),sK1)
    | ~ spl7_84
    | ~ spl7_111
    | spl7_113 ),
    inference(resolution,[],[f851,f860])).

fof(f851,plain,
    ( ! [X1] :
        ( r2_hidden(sK6(sK0,sK2,sK1),X1)
        | r2_hidden(k4_tarski(sK5(X1,sK1,sK1),sK6(X1,sK1,sK1)),sK1) )
    | ~ spl7_84
    | ~ spl7_111 ),
    inference(resolution,[],[f842,f589])).

fof(f589,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_hidden(k4_tarski(X8,X9),sK1)
        | r2_hidden(k4_tarski(sK5(X7,sK1,sK1),sK6(X7,sK1,sK1)),sK1)
        | r2_hidden(X9,X7) )
    | ~ spl7_84 ),
    inference(avatar_component_clause,[],[f588])).

fof(f842,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1)
    | ~ spl7_111 ),
    inference(avatar_component_clause,[],[f841])).

fof(f895,plain,
    ( spl7_120
    | ~ spl7_114
    | ~ spl7_119 ),
    inference(avatar_split_clause,[],[f894,f886,f863,f890])).

fof(f894,plain,
    ( sK6(sK0,sK2,sK1) = k1_funct_1(sK2,sK5(sK0,sK2,sK1))
    | ~ spl7_114
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f864,f887])).

fof(f893,plain,
    ( spl7_112
    | ~ spl7_116
    | ~ spl7_119 ),
    inference(avatar_split_clause,[],[f892,f886,f875,f856])).

fof(f875,plain,
    ( spl7_116
  <=> r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK1,sK5(sK0,sK2,sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).

fof(f892,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK2)
    | ~ spl7_116
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f876,f887])).

fof(f876,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK1,sK5(sK0,sK2,sK1))),sK2)
    | ~ spl7_116 ),
    inference(avatar_component_clause,[],[f875])).

fof(f888,plain,
    ( ~ spl7_14
    | ~ spl7_13
    | spl7_119
    | ~ spl7_111 ),
    inference(avatar_split_clause,[],[f854,f841,f886,f106,f110])).

fof(f854,plain,
    ( sK6(sK0,sK2,sK1) = k1_funct_1(sK1,sK5(sK0,sK2,sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl7_111 ),
    inference(resolution,[],[f842,f47])).

fof(f871,plain,
    ( spl7_115
    | ~ spl7_25
    | ~ spl7_111 ),
    inference(avatar_split_clause,[],[f847,f841,f178,f869])).

fof(f178,plain,
    ( spl7_25
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f847,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK2,sK5(sK0,sK2,sK1))),sK2)
    | ~ spl7_25
    | ~ spl7_111 ),
    inference(resolution,[],[f842,f179])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f178])).

fof(f867,plain,
    ( spl7_113
    | ~ spl7_21
    | ~ spl7_111 ),
    inference(avatar_split_clause,[],[f846,f841,f155,f859])).

fof(f846,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),sK0)
    | ~ spl7_21
    | ~ spl7_111 ),
    inference(resolution,[],[f842,f156])).

fof(f865,plain,
    ( spl7_114
    | ~ spl7_15
    | ~ spl7_111 ),
    inference(avatar_split_clause,[],[f845,f841,f118,f863])).

fof(f845,plain,
    ( k1_funct_1(sK1,sK5(sK0,sK2,sK1)) = k1_funct_1(sK2,sK5(sK0,sK2,sK1))
    | ~ spl7_15
    | ~ spl7_111 ),
    inference(resolution,[],[f842,f119])).

fof(f861,plain,
    ( ~ spl7_12
    | spl7_1
    | ~ spl7_112
    | ~ spl7_113
    | ~ spl7_14
    | ~ spl7_111 ),
    inference(avatar_split_clause,[],[f844,f841,f110,f859,f856,f54,f102])).

fof(f844,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK2)
    | sK1 = k8_relat_1(sK0,sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_14
    | ~ spl7_111 ),
    inference(resolution,[],[f842,f422])).

fof(f590,plain,
    ( spl7_84
    | ~ spl7_14
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f584,f110,f110,f588])).

fof(f584,plain,
    ( ! [X8,X7,X9] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(X8,X9),sK1)
        | r2_hidden(X9,X7)
        | r2_hidden(k4_tarski(sK5(X7,sK1,sK1),sK6(X7,sK1,sK1)),sK1) )
    | ~ spl7_14 ),
    inference(duplicate_literal_removal,[],[f583])).

fof(f583,plain,
    ( ! [X8,X7,X9] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(X8,X9),sK1)
        | r2_hidden(X9,X7)
        | ~ v1_relat_1(sK1)
        | r2_hidden(k4_tarski(sK5(X7,sK1,sK1),sK6(X7,sK1,sK1)),sK1) )
    | ~ spl7_14 ),
    inference(superposition,[],[f51,f580])).

fof(f580,plain,
    ( ! [X1] :
        ( sK1 = k8_relat_1(X1,sK1)
        | r2_hidden(k4_tarski(sK5(X1,sK1,sK1),sK6(X1,sK1,sK1)),sK1) )
    | ~ spl7_14 ),
    inference(duplicate_literal_removal,[],[f579])).

fof(f579,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK5(X1,sK1,sK1),sK6(X1,sK1,sK1)),sK1)
        | sK1 = k8_relat_1(X1,sK1)
        | r2_hidden(k4_tarski(sK5(X1,sK1,sK1),sK6(X1,sK1,sK1)),sK1) )
    | ~ spl7_14 ),
    inference(resolution,[],[f309,f111])).

fof(f258,plain,
    ( ~ spl7_16
    | ~ spl7_34 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl7_16
    | ~ spl7_34 ),
    inference(resolution,[],[f245,f124])).

fof(f124,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK4,X0),sK1)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_16
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK4,X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f245,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK1)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl7_34
  <=> r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f246,plain,
    ( ~ spl7_4
    | spl7_34
    | ~ spl7_30
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f234,f229,f216,f244,f63])).

fof(f216,plain,
    ( spl7_30
  <=> r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f229,plain,
    ( spl7_31
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f234,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK1)
    | ~ r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | ~ spl7_30
    | ~ spl7_31 ),
    inference(resolution,[],[f230,f217])).

fof(f217,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK2)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f216])).

fof(f230,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f229])).

fof(f231,plain,
    ( ~ spl7_12
    | spl7_31
    | ~ spl7_14
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f227,f54,f110,f229,f102])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(X1,sK0)
        | r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(superposition,[],[f49,f80])).

fof(f80,plain,
    ( sK1 = k8_relat_1(sK0,sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f49,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(X6,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f218,plain,
    ( spl7_30
    | ~ spl7_3
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f214,f140,f60,f216])).

fof(f60,plain,
    ( spl7_3
  <=> r2_hidden(sK4,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f214,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK2)
    | ~ spl7_3
    | ~ spl7_18 ),
    inference(resolution,[],[f72,f141])).

fof(f72,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f213,plain,
    ( ~ spl7_12
    | ~ spl7_11
    | spl7_5
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f208,f204,f66,f98,f102])).

fof(f66,plain,
    ( spl7_5
  <=> k1_funct_1(sK2,sK3) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f204,plain,
    ( spl7_28
  <=> r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f208,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK1,sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_28 ),
    inference(resolution,[],[f205,f47])).

fof(f205,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK2)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f204])).

fof(f206,plain,
    ( spl7_28
    | ~ spl7_6
    | ~ spl7_19
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f198,f189,f144,f75,f204])).

fof(f75,plain,
    ( spl7_6
  <=> r2_hidden(sK3,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f198,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK2)
    | ~ spl7_6
    | ~ spl7_19
    | ~ spl7_26 ),
    inference(resolution,[],[f193,f76])).

fof(f76,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f191,plain,
    ( ~ spl7_12
    | spl7_26
    | ~ spl7_14
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f187,f54,f110,f189,f102])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(superposition,[],[f50,f80])).

fof(f50,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f180,plain,
    ( ~ spl7_14
    | ~ spl7_13
    | spl7_25
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f176,f140,f94,f178,f106,f110])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_10
    | ~ spl7_18 ),
    inference(resolution,[],[f161,f46])).

fof(f157,plain,
    ( ~ spl7_12
    | spl7_21
    | ~ spl7_14
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f153,f54,f110,f155,f102])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X1,sK0)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(superposition,[],[f51,f80])).

fof(f146,plain,
    ( ~ spl7_14
    | spl7_19
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f138,f106,f144,f110])).

fof(f138,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl7_13 ),
    inference(resolution,[],[f52,f107])).

fof(f107,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f106])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f142,plain,
    ( ~ spl7_12
    | spl7_18
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f137,f98,f140,f102])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_11 ),
    inference(resolution,[],[f52,f99])).

fof(f99,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f98])).

fof(f134,plain,
    ( ~ spl7_12
    | ~ spl7_11
    | spl7_17
    | spl7_3 ),
    inference(avatar_split_clause,[],[f127,f60,f132,f98,f102])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK4,X0),sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | spl7_3 ),
    inference(resolution,[],[f61,f46])).

fof(f61,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK2))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f125,plain,
    ( ~ spl7_14
    | ~ spl7_13
    | spl7_16
    | spl7_2 ),
    inference(avatar_split_clause,[],[f121,f57,f123,f106,f110])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK4,X0),sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | spl7_2 ),
    inference(resolution,[],[f58,f46])).

fof(f58,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK1))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f120,plain,
    ( ~ spl7_14
    | ~ spl7_13
    | spl7_15
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f114,f82,f118,f106,f110])).

fof(f82,plain,
    ( spl7_7
  <=> ! [X5] :
        ( k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5)
        | ~ r2_hidden(X5,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) )
    | ~ spl7_7 ),
    inference(resolution,[],[f46,f83])).

fof(f83,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k1_relat_1(sK1))
        | k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f112,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f26,f110])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ( k1_funct_1(sK2,sK3) != k1_funct_1(sK1,sK3)
        & r2_hidden(sK3,k1_relat_1(sK1)) )
      | ( ( ~ r2_hidden(k1_funct_1(sK2,sK4),sK0)
          | ~ r2_hidden(sK4,k1_relat_1(sK2))
          | ~ r2_hidden(sK4,k1_relat_1(sK1)) )
        & ( ( r2_hidden(k1_funct_1(sK2,sK4),sK0)
            & r2_hidden(sK4,k1_relat_1(sK2)) )
          | r2_hidden(sK4,k1_relat_1(sK1)) ) )
      | sK1 != k8_relat_1(sK0,sK2) )
    & ( ( ! [X5] :
            ( k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5)
            | ~ r2_hidden(X5,k1_relat_1(sK1)) )
        & ! [X6] :
            ( ( r2_hidden(X6,k1_relat_1(sK1))
              | ~ r2_hidden(k1_funct_1(sK2,X6),sK0)
              | ~ r2_hidden(X6,k1_relat_1(sK2)) )
            & ( ( r2_hidden(k1_funct_1(sK2,X6),sK0)
                & r2_hidden(X6,k1_relat_1(sK2)) )
              | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ) )
      | sK1 = k8_relat_1(sK0,sK2) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f17,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                  & r2_hidden(X3,k1_relat_1(X1)) )
              | ? [X4] :
                  ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2))
                    | ~ r2_hidden(X4,k1_relat_1(X1)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | r2_hidden(X4,k1_relat_1(X1)) ) )
              | k8_relat_1(X0,X2) != X1 )
            & ( ( ! [X5] :
                    ( k1_funct_1(X2,X5) = k1_funct_1(X1,X5)
                    | ~ r2_hidden(X5,k1_relat_1(X1)) )
                & ! [X6] :
                    ( ( r2_hidden(X6,k1_relat_1(X1))
                      | ~ r2_hidden(k1_funct_1(X2,X6),X0)
                      | ~ r2_hidden(X6,k1_relat_1(X2)) )
                    & ( ( r2_hidden(k1_funct_1(X2,X6),X0)
                        & r2_hidden(X6,k1_relat_1(X2)) )
                      | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
              | k8_relat_1(X0,X2) = X1 )
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X2,X3) != k1_funct_1(sK1,X3)
                & r2_hidden(X3,k1_relat_1(sK1)) )
            | ? [X4] :
                ( ( ~ r2_hidden(k1_funct_1(X2,X4),sK0)
                  | ~ r2_hidden(X4,k1_relat_1(X2))
                  | ~ r2_hidden(X4,k1_relat_1(sK1)) )
                & ( ( r2_hidden(k1_funct_1(X2,X4),sK0)
                    & r2_hidden(X4,k1_relat_1(X2)) )
                  | r2_hidden(X4,k1_relat_1(sK1)) ) )
            | sK1 != k8_relat_1(sK0,X2) )
          & ( ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(sK1,X5)
                  | ~ r2_hidden(X5,k1_relat_1(sK1)) )
              & ! [X6] :
                  ( ( r2_hidden(X6,k1_relat_1(sK1))
                    | ~ r2_hidden(k1_funct_1(X2,X6),sK0)
                    | ~ r2_hidden(X6,k1_relat_1(X2)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X6),sK0)
                      & r2_hidden(X6,k1_relat_1(X2)) )
                    | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ) )
            | sK1 = k8_relat_1(sK0,X2) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( k1_funct_1(X2,X3) != k1_funct_1(sK1,X3)
              & r2_hidden(X3,k1_relat_1(sK1)) )
          | ? [X4] :
              ( ( ~ r2_hidden(k1_funct_1(X2,X4),sK0)
                | ~ r2_hidden(X4,k1_relat_1(X2))
                | ~ r2_hidden(X4,k1_relat_1(sK1)) )
              & ( ( r2_hidden(k1_funct_1(X2,X4),sK0)
                  & r2_hidden(X4,k1_relat_1(X2)) )
                | r2_hidden(X4,k1_relat_1(sK1)) ) )
          | sK1 != k8_relat_1(sK0,X2) )
        & ( ( ! [X5] :
                ( k1_funct_1(X2,X5) = k1_funct_1(sK1,X5)
                | ~ r2_hidden(X5,k1_relat_1(sK1)) )
            & ! [X6] :
                ( ( r2_hidden(X6,k1_relat_1(sK1))
                  | ~ r2_hidden(k1_funct_1(X2,X6),sK0)
                  | ~ r2_hidden(X6,k1_relat_1(X2)) )
                & ( ( r2_hidden(k1_funct_1(X2,X6),sK0)
                    & r2_hidden(X6,k1_relat_1(X2)) )
                  | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ) )
          | sK1 = k8_relat_1(sK0,X2) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ? [X3] :
            ( k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3)
            & r2_hidden(X3,k1_relat_1(sK1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(sK2,X4),sK0)
              | ~ r2_hidden(X4,k1_relat_1(sK2))
              | ~ r2_hidden(X4,k1_relat_1(sK1)) )
            & ( ( r2_hidden(k1_funct_1(sK2,X4),sK0)
                & r2_hidden(X4,k1_relat_1(sK2)) )
              | r2_hidden(X4,k1_relat_1(sK1)) ) )
        | sK1 != k8_relat_1(sK0,sK2) )
      & ( ( ! [X5] :
              ( k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5)
              | ~ r2_hidden(X5,k1_relat_1(sK1)) )
          & ! [X6] :
              ( ( r2_hidden(X6,k1_relat_1(sK1))
                | ~ r2_hidden(k1_funct_1(sK2,X6),sK0)
                | ~ r2_hidden(X6,k1_relat_1(sK2)) )
              & ( ( r2_hidden(k1_funct_1(sK2,X6),sK0)
                  & r2_hidden(X6,k1_relat_1(sK2)) )
                | ~ r2_hidden(X6,k1_relat_1(sK1)) ) ) )
        | sK1 = k8_relat_1(sK0,sK2) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3)
        & r2_hidden(X3,k1_relat_1(sK1)) )
   => ( k1_funct_1(sK2,sK3) != k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,k1_relat_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X4] :
        ( ( ~ r2_hidden(k1_funct_1(sK2,X4),sK0)
          | ~ r2_hidden(X4,k1_relat_1(sK2))
          | ~ r2_hidden(X4,k1_relat_1(sK1)) )
        & ( ( r2_hidden(k1_funct_1(sK2,X4),sK0)
            & r2_hidden(X4,k1_relat_1(sK2)) )
          | r2_hidden(X4,k1_relat_1(sK1)) ) )
   => ( ( ~ r2_hidden(k1_funct_1(sK2,sK4),sK0)
        | ~ r2_hidden(sK4,k1_relat_1(sK2))
        | ~ r2_hidden(sK4,k1_relat_1(sK1)) )
      & ( ( r2_hidden(k1_funct_1(sK2,sK4),sK0)
          & r2_hidden(sK4,k1_relat_1(sK2)) )
        | r2_hidden(sK4,k1_relat_1(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                & r2_hidden(X3,k1_relat_1(X1)) )
            | ? [X4] :
                ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                  | ~ r2_hidden(X4,k1_relat_1(X2))
                  | ~ r2_hidden(X4,k1_relat_1(X1)) )
                & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) )
                  | r2_hidden(X4,k1_relat_1(X1)) ) )
            | k8_relat_1(X0,X2) != X1 )
          & ( ( ! [X5] :
                  ( k1_funct_1(X2,X5) = k1_funct_1(X1,X5)
                  | ~ r2_hidden(X5,k1_relat_1(X1)) )
              & ! [X6] :
                  ( ( r2_hidden(X6,k1_relat_1(X1))
                    | ~ r2_hidden(k1_funct_1(X2,X6),X0)
                    | ~ r2_hidden(X6,k1_relat_1(X2)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X6),X0)
                      & r2_hidden(X6,k1_relat_1(X2)) )
                    | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
            | k8_relat_1(X0,X2) = X1 )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                & r2_hidden(X3,k1_relat_1(X1)) )
            | ? [X4] :
                ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                  | ~ r2_hidden(X4,k1_relat_1(X2))
                  | ~ r2_hidden(X4,k1_relat_1(X1)) )
                & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) )
                  | r2_hidden(X4,k1_relat_1(X1)) ) )
            | k8_relat_1(X0,X2) != X1 )
          & ( ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( ( r2_hidden(X4,k1_relat_1(X1))
                    | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
            | k8_relat_1(X0,X2) = X1 )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
                & r2_hidden(X3,k1_relat_1(X1)) )
            | ? [X4] :
                ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
                  | ~ r2_hidden(X4,k1_relat_1(X2))
                  | ~ r2_hidden(X4,k1_relat_1(X1)) )
                & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) )
                  | r2_hidden(X4,k1_relat_1(X1)) ) )
            | k8_relat_1(X0,X2) != X1 )
          & ( ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( ( r2_hidden(X4,k1_relat_1(X1))
                    | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                    | ~ r2_hidden(X4,k1_relat_1(X2)) )
                  & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) )
                    | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
            | k8_relat_1(X0,X2) = X1 )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <~> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <~> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( k8_relat_1(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
                & ! [X4] :
                    ( r2_hidden(X4,k1_relat_1(X1))
                  <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( k8_relat_1(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
                & ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                  <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                      & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).

fof(f108,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f27,f106])).

fof(f27,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f104,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f28,f102])).

fof(f28,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f100,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f29,f98])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f96,plain,
    ( spl7_1
    | spl7_10 ),
    inference(avatar_split_clause,[],[f30,f94,f54])).

fof(f30,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_relat_1(sK2))
      | ~ r2_hidden(X6,k1_relat_1(sK1))
      | sK1 = k8_relat_1(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f92,plain,
    ( spl7_1
    | spl7_9 ),
    inference(avatar_split_clause,[],[f31,f90,f54])).

fof(f31,plain,(
    ! [X6] :
      ( r2_hidden(k1_funct_1(sK2,X6),sK0)
      | ~ r2_hidden(X6,k1_relat_1(sK1))
      | sK1 = k8_relat_1(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f88,plain,
    ( spl7_1
    | spl7_8 ),
    inference(avatar_split_clause,[],[f32,f86,f54])).

fof(f32,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_relat_1(sK1))
      | ~ r2_hidden(k1_funct_1(sK2,X6),sK0)
      | ~ r2_hidden(X6,k1_relat_1(sK2))
      | sK1 = k8_relat_1(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,
    ( spl7_1
    | spl7_7 ),
    inference(avatar_split_clause,[],[f33,f82,f54])).

fof(f33,plain,(
    ! [X5] :
      ( k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5)
      | ~ r2_hidden(X5,k1_relat_1(sK1))
      | sK1 = k8_relat_1(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_6 ),
    inference(avatar_split_clause,[],[f34,f75,f60,f57,f54])).

fof(f34,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK2))
    | r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_4
    | spl7_6 ),
    inference(avatar_split_clause,[],[f35,f75,f63,f57,f54])).

fof(f35,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_6 ),
    inference(avatar_split_clause,[],[f36,f75,f63,f60,f57,f54])).

fof(f36,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | ~ r2_hidden(sK4,k1_relat_1(sK2))
    | ~ r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f37,f66,f60,f57,f54])).

fof(f37,plain,
    ( k1_funct_1(sK2,sK3) != k1_funct_1(sK1,sK3)
    | r2_hidden(sK4,k1_relat_1(sK2))
    | r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f38,f66,f63,f57,f54])).

fof(f38,plain,
    ( k1_funct_1(sK2,sK3) != k1_funct_1(sK1,sK3)
    | r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f39,f66,f63,f60,f57,f54])).

fof(f39,plain,
    ( k1_funct_1(sK2,sK3) != k1_funct_1(sK1,sK3)
    | ~ r2_hidden(k1_funct_1(sK2,sK4),sK0)
    | ~ r2_hidden(sK4,k1_relat_1(sK2))
    | ~ r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:21:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.47  % (26215)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.47  % (26211)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (26209)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (26205)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (26227)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (26225)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.48  % (26227)Refutation not found, incomplete strategy% (26227)------------------------------
% 0.22/0.48  % (26227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (26227)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (26227)Memory used [KB]: 10618
% 0.22/0.48  % (26227)Time elapsed: 0.078 s
% 0.22/0.48  % (26227)------------------------------
% 0.22/0.48  % (26227)------------------------------
% 0.22/0.48  % (26220)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (26221)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (26223)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (26212)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (26213)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (26221)Refutation not found, incomplete strategy% (26221)------------------------------
% 0.22/0.49  % (26221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (26221)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (26221)Memory used [KB]: 10618
% 0.22/0.49  % (26221)Time elapsed: 0.007 s
% 0.22/0.49  % (26221)------------------------------
% 0.22/0.49  % (26221)------------------------------
% 0.22/0.49  % (26210)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (26216)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (26207)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (26217)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  % (26206)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (26206)Refutation not found, incomplete strategy% (26206)------------------------------
% 0.22/0.51  % (26206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26206)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26206)Memory used [KB]: 10618
% 0.22/0.51  % (26206)Time elapsed: 0.094 s
% 0.22/0.51  % (26206)------------------------------
% 0.22/0.51  % (26206)------------------------------
% 0.22/0.51  % (26218)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (26226)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (26218)Refutation not found, incomplete strategy% (26218)------------------------------
% 0.22/0.51  % (26218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26218)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26218)Memory used [KB]: 10618
% 0.22/0.51  % (26218)Time elapsed: 0.094 s
% 0.22/0.51  % (26218)------------------------------
% 0.22/0.51  % (26218)------------------------------
% 0.22/0.51  % (26219)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (26224)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (26222)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (26219)Refutation not found, incomplete strategy% (26219)------------------------------
% 0.22/0.52  % (26219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (26219)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (26219)Memory used [KB]: 6140
% 0.22/0.52  % (26219)Time elapsed: 0.108 s
% 0.22/0.52  % (26219)------------------------------
% 0.22/0.52  % (26219)------------------------------
% 0.22/0.52  % (26212)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f1357,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f68,f71,f73,f77,f78,f79,f84,f88,f92,f96,f100,f104,f108,f112,f120,f125,f134,f142,f146,f157,f180,f191,f206,f213,f218,f231,f246,f258,f590,f861,f865,f867,f871,f888,f893,f895,f916,f938,f942,f962,f1052,f1057,f1060,f1077,f1090,f1091,f1225,f1232,f1235,f1236,f1239,f1293,f1294,f1295,f1301,f1302,f1312,f1338,f1351,f1354,f1356])).
% 0.22/0.52  fof(f1356,plain,(
% 0.22/0.52    ~spl7_17 | ~spl7_35),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f1355])).
% 0.22/0.52  fof(f1355,plain,(
% 0.22/0.52    $false | (~spl7_17 | ~spl7_35)),
% 0.22/0.52    inference(subsumption_resolution,[],[f261,f133])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(sK4,X0),sK2)) ) | ~spl7_17),
% 0.22/0.52    inference(avatar_component_clause,[],[f132])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    spl7_17 <=> ! [X0] : ~r2_hidden(k4_tarski(sK4,X0),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.22/0.52  fof(f261,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK2) | ~spl7_35),
% 0.22/0.52    inference(avatar_component_clause,[],[f260])).
% 0.22/0.52  fof(f260,plain,(
% 0.22/0.52    spl7_35 <=> r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.22/0.52  fof(f1354,plain,(
% 0.22/0.52    ~spl7_12 | ~spl7_11 | spl7_36 | ~spl7_35),
% 0.22/0.52    inference(avatar_split_clause,[],[f1330,f260,f264,f98,f102])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    spl7_12 <=> v1_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    spl7_11 <=> v1_funct_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.52  fof(f264,plain,(
% 0.22/0.52    spl7_36 <=> k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.22/0.52  fof(f1330,plain,(
% 0.22/0.52    k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_35),
% 0.22/0.52    inference(resolution,[],[f261,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.52    inference(flattening,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.52  fof(f1351,plain,(
% 0.22/0.52    ~spl7_2 | ~spl7_19 | ~spl7_21 | spl7_168),
% 0.22/0.52    inference(avatar_split_clause,[],[f1348,f1336,f155,f144,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    spl7_2 <=> r2_hidden(sK4,k1_relat_1(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    spl7_19 <=> ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    spl7_21 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X1,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.22/0.52  fof(f1336,plain,(
% 0.22/0.52    spl7_168 <=> r2_hidden(k1_funct_1(sK1,sK4),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_168])])).
% 0.22/0.52  fof(f1348,plain,(
% 0.22/0.52    ~r2_hidden(sK4,k1_relat_1(sK1)) | (~spl7_19 | ~spl7_21 | spl7_168)),
% 0.22/0.52    inference(resolution,[],[f192,f1337])).
% 0.22/0.52  fof(f1337,plain,(
% 0.22/0.52    ~r2_hidden(k1_funct_1(sK1,sK4),sK0) | spl7_168),
% 0.22/0.52    inference(avatar_component_clause,[],[f1336])).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),sK0) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | (~spl7_19 | ~spl7_21)),
% 0.22/0.52    inference(resolution,[],[f156,f145])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    ( ! [X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK1) | ~r2_hidden(X1,k1_relat_1(sK1))) ) | ~spl7_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f144])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X1,sK0)) ) | ~spl7_21),
% 0.22/0.52    inference(avatar_component_clause,[],[f155])).
% 0.22/0.52  fof(f1338,plain,(
% 0.22/0.52    ~spl7_168 | spl7_4 | ~spl7_36),
% 0.22/0.52    inference(avatar_split_clause,[],[f1331,f264,f63,f1336])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    spl7_4 <=> r2_hidden(k1_funct_1(sK2,sK4),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.52  fof(f1331,plain,(
% 0.22/0.52    ~r2_hidden(k1_funct_1(sK1,sK4),sK0) | (spl7_4 | ~spl7_36)),
% 0.22/0.52    inference(superposition,[],[f64,f265])).
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4) | ~spl7_36),
% 0.22/0.52    inference(avatar_component_clause,[],[f264])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ~r2_hidden(k1_funct_1(sK2,sK4),sK0) | spl7_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f63])).
% 0.22/0.52  fof(f1312,plain,(
% 0.22/0.52    spl7_35 | ~spl7_2 | ~spl7_19 | ~spl7_26),
% 0.22/0.52    inference(avatar_split_clause,[],[f1310,f189,f144,f57,f260])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    spl7_26 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(k4_tarski(X0,X1),sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.52  fof(f1310,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK2) | (~spl7_2 | ~spl7_19 | ~spl7_26)),
% 0.22/0.52    inference(resolution,[],[f69,f193])).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK2)) ) | (~spl7_19 | ~spl7_26)),
% 0.22/0.52    inference(resolution,[],[f190,f145])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(k4_tarski(X0,X1),sK2)) ) | ~spl7_26),
% 0.22/0.52    inference(avatar_component_clause,[],[f189])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    r2_hidden(sK4,k1_relat_1(sK1)) | ~spl7_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f57])).
% 0.22/0.52  fof(f1302,plain,(
% 0.22/0.52    k1_funct_1(sK1,sK5(sK0,sK2,sK1)) != k1_funct_1(sK2,sK5(sK0,sK2,sK1)) | r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK1,sK5(sK0,sK2,sK1))),sK2) | ~r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK2,sK5(sK0,sK2,sK1))),sK2)),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f1301,plain,(
% 0.22/0.52    ~spl7_12 | ~spl7_11 | spl7_120 | ~spl7_112),
% 0.22/0.52    inference(avatar_split_clause,[],[f1300,f856,f890,f98,f102])).
% 0.22/0.52  fof(f890,plain,(
% 0.22/0.52    spl7_120 <=> sK6(sK0,sK2,sK1) = k1_funct_1(sK2,sK5(sK0,sK2,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).
% 0.22/0.52  fof(f856,plain,(
% 0.22/0.52    spl7_112 <=> r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).
% 0.22/0.52  fof(f1300,plain,(
% 0.22/0.52    sK6(sK0,sK2,sK1) = k1_funct_1(sK2,sK5(sK0,sK2,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_112),
% 0.22/0.52    inference(resolution,[],[f872,f47])).
% 0.22/0.52  fof(f872,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK2) | ~spl7_112),
% 0.22/0.52    inference(avatar_component_clause,[],[f856])).
% 0.22/0.52  fof(f1295,plain,(
% 0.22/0.52    spl7_114 | ~spl7_15 | ~spl7_19 | ~spl7_150),
% 0.22/0.52    inference(avatar_split_clause,[],[f1243,f1088,f144,f118,f863])).
% 0.22/0.52  fof(f863,plain,(
% 0.22/0.52    spl7_114 <=> k1_funct_1(sK1,sK5(sK0,sK2,sK1)) = k1_funct_1(sK2,sK5(sK0,sK2,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    spl7_15 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.52  fof(f1088,plain,(
% 0.22/0.52    spl7_150 <=> r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_150])])).
% 0.22/0.52  fof(f1243,plain,(
% 0.22/0.52    k1_funct_1(sK1,sK5(sK0,sK2,sK1)) = k1_funct_1(sK2,sK5(sK0,sK2,sK1)) | (~spl7_15 | ~spl7_19 | ~spl7_150)),
% 0.22/0.52    inference(resolution,[],[f1221,f175])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)) ) | (~spl7_15 | ~spl7_19)),
% 0.22/0.52    inference(resolution,[],[f119,f145])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)) ) | ~spl7_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f118])).
% 0.22/0.52  fof(f1221,plain,(
% 0.22/0.52    r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK1)) | ~spl7_150),
% 0.22/0.52    inference(avatar_component_clause,[],[f1088])).
% 0.22/0.52  fof(f1294,plain,(
% 0.22/0.52    spl7_115 | ~spl7_10 | ~spl7_18 | ~spl7_150),
% 0.22/0.52    inference(avatar_split_clause,[],[f1244,f1088,f140,f94,f869])).
% 0.22/0.52  fof(f869,plain,(
% 0.22/0.52    spl7_115 <=> r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK2,sK5(sK0,sK2,sK1))),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    spl7_10 <=> ! [X6] : (r2_hidden(X6,k1_relat_1(sK2)) | ~r2_hidden(X6,k1_relat_1(sK1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    spl7_18 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.52  fof(f1244,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK2,sK5(sK0,sK2,sK1))),sK2) | (~spl7_10 | ~spl7_18 | ~spl7_150)),
% 0.22/0.52    inference(resolution,[],[f1221,f161])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)) ) | (~spl7_10 | ~spl7_18)),
% 0.22/0.52    inference(resolution,[],[f95,f141])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)) ) | ~spl7_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f140])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ( ! [X6] : (r2_hidden(X6,k1_relat_1(sK2)) | ~r2_hidden(X6,k1_relat_1(sK1))) ) | ~spl7_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f94])).
% 0.22/0.52  fof(f1293,plain,(
% 0.22/0.52    spl7_111 | spl7_1 | ~spl7_12 | ~spl7_14 | spl7_112),
% 0.22/0.52    inference(avatar_split_clause,[],[f1292,f856,f110,f102,f54,f841])).
% 0.22/0.52  fof(f841,plain,(
% 0.22/0.52    spl7_111 <=> r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_111])])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    spl7_1 <=> sK1 = k8_relat_1(sK0,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    spl7_14 <=> v1_relat_1(sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.52  fof(f1292,plain,(
% 0.22/0.52    sK1 = k8_relat_1(sK0,sK2) | r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1) | (~spl7_12 | ~spl7_14 | spl7_112)),
% 0.22/0.52    inference(resolution,[],[f857,f578])).
% 0.22/0.52  fof(f578,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(k4_tarski(sK5(X0,sK2,sK1),sK6(X0,sK2,sK1)),sK2) | sK1 = k8_relat_1(X0,sK2) | r2_hidden(k4_tarski(sK5(X0,sK2,sK1),sK6(X0,sK2,sK1)),sK1)) ) | (~spl7_12 | ~spl7_14)),
% 0.22/0.52    inference(resolution,[],[f309,f103])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    v1_relat_1(sK2) | ~spl7_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f102])).
% 0.22/0.52  fof(f309,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~v1_relat_1(X3) | r2_hidden(k4_tarski(sK5(X2,X3,sK1),sK6(X2,X3,sK1)),sK1) | sK1 = k8_relat_1(X2,X3) | r2_hidden(k4_tarski(sK5(X2,X3,sK1),sK6(X2,X3,sK1)),X3)) ) | ~spl7_14),
% 0.22/0.52    inference(resolution,[],[f44,f111])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    v1_relat_1(sK1) | ~spl7_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f110])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) | k8_relat_1(X0,X1) = X2 | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f21,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(rectify,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0))) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).
% 0.22/0.52  fof(f857,plain,(
% 0.22/0.52    ~r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK2) | spl7_112),
% 0.22/0.52    inference(avatar_component_clause,[],[f856])).
% 0.22/0.52  fof(f1239,plain,(
% 0.22/0.52    ~spl7_12 | ~spl7_11 | spl7_119 | ~spl7_112 | ~spl7_114),
% 0.22/0.52    inference(avatar_split_clause,[],[f1238,f863,f856,f886,f98,f102])).
% 0.22/0.52  fof(f886,plain,(
% 0.22/0.52    spl7_119 <=> sK6(sK0,sK2,sK1) = k1_funct_1(sK1,sK5(sK0,sK2,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).
% 0.22/0.52  fof(f1238,plain,(
% 0.22/0.52    sK6(sK0,sK2,sK1) = k1_funct_1(sK1,sK5(sK0,sK2,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_112 | ~spl7_114)),
% 0.22/0.52    inference(forward_demodulation,[],[f899,f864])).
% 0.22/0.52  fof(f864,plain,(
% 0.22/0.52    k1_funct_1(sK1,sK5(sK0,sK2,sK1)) = k1_funct_1(sK2,sK5(sK0,sK2,sK1)) | ~spl7_114),
% 0.22/0.52    inference(avatar_component_clause,[],[f863])).
% 0.22/0.52  fof(f899,plain,(
% 0.22/0.52    sK6(sK0,sK2,sK1) = k1_funct_1(sK2,sK5(sK0,sK2,sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_112),
% 0.22/0.52    inference(resolution,[],[f872,f47])).
% 0.22/0.52  fof(f1236,plain,(
% 0.22/0.52    ~spl7_112 | ~spl7_160),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f1234])).
% 0.22/0.52  fof(f1234,plain,(
% 0.22/0.52    $false | (~spl7_112 | ~spl7_160)),
% 0.22/0.52    inference(subsumption_resolution,[],[f872,f1231])).
% 0.22/0.52  fof(f1231,plain,(
% 0.22/0.52    ( ! [X1] : (~r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),X1),sK2)) ) | ~spl7_160),
% 0.22/0.52    inference(avatar_component_clause,[],[f1230])).
% 0.22/0.52  fof(f1230,plain,(
% 0.22/0.52    spl7_160 <=> ! [X1] : ~r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),X1),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_160])])).
% 0.22/0.52  fof(f1235,plain,(
% 0.22/0.52    ~spl7_115 | ~spl7_160),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f1233])).
% 0.22/0.52  fof(f1233,plain,(
% 0.22/0.52    $false | (~spl7_115 | ~spl7_160)),
% 0.22/0.52    inference(subsumption_resolution,[],[f870,f1231])).
% 0.22/0.52  fof(f870,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK2,sK5(sK0,sK2,sK1))),sK2) | ~spl7_115),
% 0.22/0.52    inference(avatar_component_clause,[],[f869])).
% 0.22/0.52  fof(f1232,plain,(
% 0.22/0.52    ~spl7_12 | ~spl7_11 | spl7_160 | spl7_159),
% 0.22/0.52    inference(avatar_split_clause,[],[f1228,f1223,f1230,f98,f102])).
% 0.22/0.52  fof(f1223,plain,(
% 0.22/0.52    spl7_159 <=> r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_159])])).
% 0.22/0.52  fof(f1228,plain,(
% 0.22/0.52    ( ! [X1] : (~r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),X1),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | spl7_159),
% 0.22/0.52    inference(resolution,[],[f1224,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f1224,plain,(
% 0.22/0.52    ~r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK2)) | spl7_159),
% 0.22/0.52    inference(avatar_component_clause,[],[f1223])).
% 0.22/0.52  fof(f1225,plain,(
% 0.22/0.52    spl7_150 | ~spl7_159 | ~spl7_113 | ~spl7_8 | ~spl7_120),
% 0.22/0.52    inference(avatar_split_clause,[],[f1219,f890,f86,f859,f1223,f1088])).
% 0.22/0.52  fof(f859,plain,(
% 0.22/0.52    spl7_113 <=> r2_hidden(sK6(sK0,sK2,sK1),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    spl7_8 <=> ! [X6] : (r2_hidden(X6,k1_relat_1(sK1)) | ~r2_hidden(X6,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,X6),sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.52  fof(f1219,plain,(
% 0.22/0.52    ~r2_hidden(sK6(sK0,sK2,sK1),sK0) | ~r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK2)) | r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK1)) | (~spl7_8 | ~spl7_120)),
% 0.22/0.52    inference(superposition,[],[f87,f891])).
% 0.22/0.52  fof(f891,plain,(
% 0.22/0.52    sK6(sK0,sK2,sK1) = k1_funct_1(sK2,sK5(sK0,sK2,sK1)) | ~spl7_120),
% 0.22/0.52    inference(avatar_component_clause,[],[f890])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ( ! [X6] : (~r2_hidden(k1_funct_1(sK2,X6),sK0) | ~r2_hidden(X6,k1_relat_1(sK2)) | r2_hidden(X6,k1_relat_1(sK1))) ) | ~spl7_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f86])).
% 0.22/0.52  fof(f1091,plain,(
% 0.22/0.52    spl7_111 | spl7_1 | ~spl7_12 | ~spl7_14 | spl7_113),
% 0.22/0.52    inference(avatar_split_clause,[],[f896,f859,f110,f102,f54,f841])).
% 0.22/0.52  fof(f896,plain,(
% 0.22/0.52    sK1 = k8_relat_1(sK0,sK2) | r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1) | (~spl7_12 | ~spl7_14 | spl7_113)),
% 0.22/0.52    inference(resolution,[],[f860,f310])).
% 0.22/0.52  fof(f310,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK6(X0,sK2,sK1),X0) | sK1 = k8_relat_1(X0,sK2) | r2_hidden(k4_tarski(sK5(X0,sK2,sK1),sK6(X0,sK2,sK1)),sK1)) ) | (~spl7_12 | ~spl7_14)),
% 0.22/0.52    inference(resolution,[],[f287,f103])).
% 0.22/0.52  fof(f287,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~v1_relat_1(X3) | r2_hidden(k4_tarski(sK5(X2,X3,sK1),sK6(X2,X3,sK1)),sK1) | sK1 = k8_relat_1(X2,X3) | r2_hidden(sK6(X2,X3,sK1),X2)) ) | ~spl7_14),
% 0.22/0.52    inference(resolution,[],[f43,f111])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) | k8_relat_1(X0,X1) = X2 | ~v1_relat_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f860,plain,(
% 0.22/0.52    ~r2_hidden(sK6(sK0,sK2,sK1),sK0) | spl7_113),
% 0.22/0.52    inference(avatar_component_clause,[],[f859])).
% 0.22/0.52  fof(f1090,plain,(
% 0.22/0.52    ~spl7_150 | spl7_111 | ~spl7_19 | ~spl7_119),
% 0.22/0.52    inference(avatar_split_clause,[],[f900,f886,f144,f841,f1088])).
% 0.22/0.52  fof(f900,plain,(
% 0.22/0.52    r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1) | ~r2_hidden(sK5(sK0,sK2,sK1),k1_relat_1(sK1)) | (~spl7_19 | ~spl7_119)),
% 0.22/0.52    inference(superposition,[],[f145,f887])).
% 0.22/0.52  fof(f887,plain,(
% 0.22/0.52    sK6(sK0,sK2,sK1) = k1_funct_1(sK1,sK5(sK0,sK2,sK1)) | ~spl7_119),
% 0.22/0.52    inference(avatar_component_clause,[],[f886])).
% 0.22/0.52  fof(f1077,plain,(
% 0.22/0.52    spl7_21 | ~spl7_14 | ~spl7_123),
% 0.22/0.52    inference(avatar_split_clause,[],[f1074,f932,f110,f155])).
% 0.22/0.52  fof(f932,plain,(
% 0.22/0.52    spl7_123 <=> sK1 = k8_relat_1(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_123])])).
% 0.22/0.52  fof(f1074,plain,(
% 0.22/0.52    ( ! [X4,X5] : (~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X4,X5),sK1) | r2_hidden(X5,sK0)) ) | ~spl7_123),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f1073])).
% 0.22/0.52  fof(f1073,plain,(
% 0.22/0.52    ( ! [X4,X5] : (~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X4,X5),sK1) | r2_hidden(X5,sK0) | ~v1_relat_1(sK1)) ) | ~spl7_123),
% 0.22/0.52    inference(superposition,[],[f51,f933])).
% 0.22/0.53  fof(f933,plain,(
% 0.22/0.53    sK1 = k8_relat_1(sK0,sK1) | ~spl7_123),
% 0.22/0.53    inference(avatar_component_clause,[],[f932])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X6,X0,X5,X1] : (~v1_relat_1(k8_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | r2_hidden(X6,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X6,X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f1060,plain,(
% 0.22/0.53    ~spl7_121 | ~spl7_146),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f1058])).
% 0.22/0.53  fof(f1058,plain,(
% 0.22/0.53    $false | (~spl7_121 | ~spl7_146)),
% 0.22/0.53    inference(subsumption_resolution,[],[f915,f1056])).
% 0.22/0.53  fof(f1056,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(k4_tarski(sK5(sK0,sK1,sK1),X0),sK1)) ) | ~spl7_146),
% 0.22/0.53    inference(avatar_component_clause,[],[f1055])).
% 0.22/0.53  fof(f1055,plain,(
% 0.22/0.53    spl7_146 <=> ! [X0] : ~r2_hidden(k4_tarski(sK5(sK0,sK1,sK1),X0),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_146])])).
% 0.22/0.53  fof(f915,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK5(sK0,sK1,sK1),sK6(sK0,sK1,sK1)),sK1) | ~spl7_121),
% 0.22/0.53    inference(avatar_component_clause,[],[f914])).
% 0.22/0.53  fof(f914,plain,(
% 0.22/0.53    spl7_121 <=> r2_hidden(k4_tarski(sK5(sK0,sK1,sK1),sK6(sK0,sK1,sK1)),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_121])])).
% 0.22/0.53  fof(f1057,plain,(
% 0.22/0.53    ~spl7_14 | ~spl7_13 | spl7_146 | spl7_145),
% 0.22/0.53    inference(avatar_split_clause,[],[f1053,f1049,f1055,f106,f110])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    spl7_13 <=> v1_funct_1(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.53  fof(f1049,plain,(
% 0.22/0.53    spl7_145 <=> r2_hidden(sK5(sK0,sK1,sK1),k1_relat_1(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_145])])).
% 0.22/0.53  fof(f1053,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(k4_tarski(sK5(sK0,sK1,sK1),X0),sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | spl7_145),
% 0.22/0.53    inference(resolution,[],[f1050,f46])).
% 0.22/0.53  fof(f1050,plain,(
% 0.22/0.53    ~r2_hidden(sK5(sK0,sK1,sK1),k1_relat_1(sK1)) | spl7_145),
% 0.22/0.53    inference(avatar_component_clause,[],[f1049])).
% 0.22/0.53  fof(f1052,plain,(
% 0.22/0.53    ~spl7_145 | spl7_124 | ~spl7_9 | ~spl7_82 | ~spl7_125),
% 0.22/0.53    inference(avatar_split_clause,[],[f1047,f940,f563,f90,f936,f1049])).
% 0.22/0.53  fof(f936,plain,(
% 0.22/0.53    spl7_124 <=> r2_hidden(sK6(sK0,sK1,sK1),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    spl7_9 <=> ! [X6] : (r2_hidden(k1_funct_1(sK2,X6),sK0) | ~r2_hidden(X6,k1_relat_1(sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.53  fof(f563,plain,(
% 0.22/0.53    spl7_82 <=> sK6(sK0,sK1,sK1) = k1_funct_1(sK1,sK5(sK0,sK1,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).
% 0.22/0.53  fof(f940,plain,(
% 0.22/0.53    spl7_125 <=> k1_funct_1(sK1,sK5(sK0,sK1,sK1)) = k1_funct_1(sK2,sK5(sK0,sK1,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_125])])).
% 0.22/0.53  fof(f1047,plain,(
% 0.22/0.53    r2_hidden(sK6(sK0,sK1,sK1),sK0) | ~r2_hidden(sK5(sK0,sK1,sK1),k1_relat_1(sK1)) | (~spl7_9 | ~spl7_82 | ~spl7_125)),
% 0.22/0.53    inference(forward_demodulation,[],[f1044,f564])).
% 0.22/0.53  fof(f564,plain,(
% 0.22/0.53    sK6(sK0,sK1,sK1) = k1_funct_1(sK1,sK5(sK0,sK1,sK1)) | ~spl7_82),
% 0.22/0.53    inference(avatar_component_clause,[],[f563])).
% 0.22/0.53  fof(f1044,plain,(
% 0.22/0.53    r2_hidden(k1_funct_1(sK1,sK5(sK0,sK1,sK1)),sK0) | ~r2_hidden(sK5(sK0,sK1,sK1),k1_relat_1(sK1)) | (~spl7_9 | ~spl7_125)),
% 0.22/0.53    inference(superposition,[],[f91,f941])).
% 0.22/0.53  fof(f941,plain,(
% 0.22/0.53    k1_funct_1(sK1,sK5(sK0,sK1,sK1)) = k1_funct_1(sK2,sK5(sK0,sK1,sK1)) | ~spl7_125),
% 0.22/0.53    inference(avatar_component_clause,[],[f940])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ( ! [X6] : (r2_hidden(k1_funct_1(sK2,X6),sK0) | ~r2_hidden(X6,k1_relat_1(sK1))) ) | ~spl7_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f90])).
% 0.22/0.53  fof(f962,plain,(
% 0.22/0.53    ~spl7_14 | ~spl7_13 | spl7_82 | ~spl7_121),
% 0.22/0.53    inference(avatar_split_clause,[],[f930,f914,f563,f106,f110])).
% 0.22/0.53  fof(f930,plain,(
% 0.22/0.53    sK6(sK0,sK1,sK1) = k1_funct_1(sK1,sK5(sK0,sK1,sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl7_121),
% 0.22/0.53    inference(resolution,[],[f915,f47])).
% 0.22/0.53  fof(f942,plain,(
% 0.22/0.53    spl7_125 | ~spl7_15 | ~spl7_121),
% 0.22/0.53    inference(avatar_split_clause,[],[f922,f914,f118,f940])).
% 0.22/0.53  fof(f922,plain,(
% 0.22/0.53    k1_funct_1(sK1,sK5(sK0,sK1,sK1)) = k1_funct_1(sK2,sK5(sK0,sK1,sK1)) | (~spl7_15 | ~spl7_121)),
% 0.22/0.53    inference(resolution,[],[f915,f119])).
% 0.22/0.53  fof(f938,plain,(
% 0.22/0.53    ~spl7_14 | spl7_123 | ~spl7_121 | ~spl7_124 | ~spl7_14 | ~spl7_121),
% 0.22/0.53    inference(avatar_split_clause,[],[f921,f914,f110,f936,f914,f932,f110])).
% 0.22/0.53  fof(f921,plain,(
% 0.22/0.53    ~r2_hidden(sK6(sK0,sK1,sK1),sK0) | ~r2_hidden(k4_tarski(sK5(sK0,sK1,sK1),sK6(sK0,sK1,sK1)),sK1) | sK1 = k8_relat_1(sK0,sK1) | ~v1_relat_1(sK1) | (~spl7_14 | ~spl7_121)),
% 0.22/0.53    inference(resolution,[],[f915,f422])).
% 0.22/0.53  fof(f422,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~r2_hidden(k4_tarski(sK5(X2,X3,sK1),sK6(X2,X3,sK1)),sK1) | ~r2_hidden(sK6(X2,X3,sK1),X2) | ~r2_hidden(k4_tarski(sK5(X2,X3,sK1),sK6(X2,X3,sK1)),X3) | sK1 = k8_relat_1(X2,X3) | ~v1_relat_1(X3)) ) | ~spl7_14),
% 0.22/0.53    inference(resolution,[],[f45,f111])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) | k8_relat_1(X0,X1) = X2 | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f916,plain,(
% 0.22/0.53    spl7_121 | ~spl7_84 | ~spl7_111 | spl7_113),
% 0.22/0.53    inference(avatar_split_clause,[],[f905,f859,f841,f588,f914])).
% 0.22/0.53  fof(f588,plain,(
% 0.22/0.53    spl7_84 <=> ! [X9,X7,X8] : (~r2_hidden(k4_tarski(X8,X9),sK1) | r2_hidden(k4_tarski(sK5(X7,sK1,sK1),sK6(X7,sK1,sK1)),sK1) | r2_hidden(X9,X7))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).
% 0.22/0.53  fof(f905,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK5(sK0,sK1,sK1),sK6(sK0,sK1,sK1)),sK1) | (~spl7_84 | ~spl7_111 | spl7_113)),
% 0.22/0.53    inference(resolution,[],[f851,f860])).
% 0.22/0.53  fof(f851,plain,(
% 0.22/0.53    ( ! [X1] : (r2_hidden(sK6(sK0,sK2,sK1),X1) | r2_hidden(k4_tarski(sK5(X1,sK1,sK1),sK6(X1,sK1,sK1)),sK1)) ) | (~spl7_84 | ~spl7_111)),
% 0.22/0.53    inference(resolution,[],[f842,f589])).
% 0.22/0.53  fof(f589,plain,(
% 0.22/0.53    ( ! [X8,X7,X9] : (~r2_hidden(k4_tarski(X8,X9),sK1) | r2_hidden(k4_tarski(sK5(X7,sK1,sK1),sK6(X7,sK1,sK1)),sK1) | r2_hidden(X9,X7)) ) | ~spl7_84),
% 0.22/0.53    inference(avatar_component_clause,[],[f588])).
% 0.22/0.53  fof(f842,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK1) | ~spl7_111),
% 0.22/0.53    inference(avatar_component_clause,[],[f841])).
% 0.22/0.53  fof(f895,plain,(
% 0.22/0.53    spl7_120 | ~spl7_114 | ~spl7_119),
% 0.22/0.53    inference(avatar_split_clause,[],[f894,f886,f863,f890])).
% 0.22/0.53  fof(f894,plain,(
% 0.22/0.53    sK6(sK0,sK2,sK1) = k1_funct_1(sK2,sK5(sK0,sK2,sK1)) | (~spl7_114 | ~spl7_119)),
% 0.22/0.53    inference(forward_demodulation,[],[f864,f887])).
% 0.22/0.53  fof(f893,plain,(
% 0.22/0.53    spl7_112 | ~spl7_116 | ~spl7_119),
% 0.22/0.53    inference(avatar_split_clause,[],[f892,f886,f875,f856])).
% 0.22/0.53  fof(f875,plain,(
% 0.22/0.53    spl7_116 <=> r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK1,sK5(sK0,sK2,sK1))),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).
% 0.22/0.53  fof(f892,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK2) | (~spl7_116 | ~spl7_119)),
% 0.22/0.53    inference(forward_demodulation,[],[f876,f887])).
% 0.22/0.53  fof(f876,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK1,sK5(sK0,sK2,sK1))),sK2) | ~spl7_116),
% 0.22/0.53    inference(avatar_component_clause,[],[f875])).
% 0.22/0.53  fof(f888,plain,(
% 0.22/0.53    ~spl7_14 | ~spl7_13 | spl7_119 | ~spl7_111),
% 0.22/0.53    inference(avatar_split_clause,[],[f854,f841,f886,f106,f110])).
% 0.22/0.53  fof(f854,plain,(
% 0.22/0.53    sK6(sK0,sK2,sK1) = k1_funct_1(sK1,sK5(sK0,sK2,sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl7_111),
% 0.22/0.53    inference(resolution,[],[f842,f47])).
% 0.22/0.53  fof(f871,plain,(
% 0.22/0.53    spl7_115 | ~spl7_25 | ~spl7_111),
% 0.22/0.53    inference(avatar_split_clause,[],[f847,f841,f178,f869])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    spl7_25 <=> ! [X1,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) | ~r2_hidden(k4_tarski(X0,X1),sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.22/0.53  fof(f847,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),k1_funct_1(sK2,sK5(sK0,sK2,sK1))),sK2) | (~spl7_25 | ~spl7_111)),
% 0.22/0.53    inference(resolution,[],[f842,f179])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)) ) | ~spl7_25),
% 0.22/0.53    inference(avatar_component_clause,[],[f178])).
% 0.22/0.53  fof(f867,plain,(
% 0.22/0.53    spl7_113 | ~spl7_21 | ~spl7_111),
% 0.22/0.53    inference(avatar_split_clause,[],[f846,f841,f155,f859])).
% 0.22/0.53  fof(f846,plain,(
% 0.22/0.53    r2_hidden(sK6(sK0,sK2,sK1),sK0) | (~spl7_21 | ~spl7_111)),
% 0.22/0.53    inference(resolution,[],[f842,f156])).
% 0.22/0.53  fof(f865,plain,(
% 0.22/0.53    spl7_114 | ~spl7_15 | ~spl7_111),
% 0.22/0.53    inference(avatar_split_clause,[],[f845,f841,f118,f863])).
% 0.22/0.53  fof(f845,plain,(
% 0.22/0.53    k1_funct_1(sK1,sK5(sK0,sK2,sK1)) = k1_funct_1(sK2,sK5(sK0,sK2,sK1)) | (~spl7_15 | ~spl7_111)),
% 0.22/0.53    inference(resolution,[],[f842,f119])).
% 0.22/0.53  fof(f861,plain,(
% 0.22/0.53    ~spl7_12 | spl7_1 | ~spl7_112 | ~spl7_113 | ~spl7_14 | ~spl7_111),
% 0.22/0.53    inference(avatar_split_clause,[],[f844,f841,f110,f859,f856,f54,f102])).
% 0.22/0.53  fof(f844,plain,(
% 0.22/0.53    ~r2_hidden(sK6(sK0,sK2,sK1),sK0) | ~r2_hidden(k4_tarski(sK5(sK0,sK2,sK1),sK6(sK0,sK2,sK1)),sK2) | sK1 = k8_relat_1(sK0,sK2) | ~v1_relat_1(sK2) | (~spl7_14 | ~spl7_111)),
% 0.22/0.53    inference(resolution,[],[f842,f422])).
% 0.22/0.53  fof(f590,plain,(
% 0.22/0.53    spl7_84 | ~spl7_14 | ~spl7_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f584,f110,f110,f588])).
% 0.22/0.53  fof(f584,plain,(
% 0.22/0.53    ( ! [X8,X7,X9] : (~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X8,X9),sK1) | r2_hidden(X9,X7) | r2_hidden(k4_tarski(sK5(X7,sK1,sK1),sK6(X7,sK1,sK1)),sK1)) ) | ~spl7_14),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f583])).
% 0.22/0.53  fof(f583,plain,(
% 0.22/0.53    ( ! [X8,X7,X9] : (~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X8,X9),sK1) | r2_hidden(X9,X7) | ~v1_relat_1(sK1) | r2_hidden(k4_tarski(sK5(X7,sK1,sK1),sK6(X7,sK1,sK1)),sK1)) ) | ~spl7_14),
% 0.22/0.53    inference(superposition,[],[f51,f580])).
% 0.22/0.53  fof(f580,plain,(
% 0.22/0.53    ( ! [X1] : (sK1 = k8_relat_1(X1,sK1) | r2_hidden(k4_tarski(sK5(X1,sK1,sK1),sK6(X1,sK1,sK1)),sK1)) ) | ~spl7_14),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f579])).
% 0.22/0.53  fof(f579,plain,(
% 0.22/0.53    ( ! [X1] : (r2_hidden(k4_tarski(sK5(X1,sK1,sK1),sK6(X1,sK1,sK1)),sK1) | sK1 = k8_relat_1(X1,sK1) | r2_hidden(k4_tarski(sK5(X1,sK1,sK1),sK6(X1,sK1,sK1)),sK1)) ) | ~spl7_14),
% 0.22/0.53    inference(resolution,[],[f309,f111])).
% 0.22/0.53  fof(f258,plain,(
% 0.22/0.53    ~spl7_16 | ~spl7_34),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f253])).
% 0.22/0.53  fof(f253,plain,(
% 0.22/0.53    $false | (~spl7_16 | ~spl7_34)),
% 0.22/0.53    inference(resolution,[],[f245,f124])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(k4_tarski(sK4,X0),sK1)) ) | ~spl7_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f123])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    spl7_16 <=> ! [X0] : ~r2_hidden(k4_tarski(sK4,X0),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK1) | ~spl7_34),
% 0.22/0.53    inference(avatar_component_clause,[],[f244])).
% 0.22/0.53  fof(f244,plain,(
% 0.22/0.53    spl7_34 <=> r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.22/0.53  fof(f246,plain,(
% 0.22/0.53    ~spl7_4 | spl7_34 | ~spl7_30 | ~spl7_31),
% 0.22/0.53    inference(avatar_split_clause,[],[f234,f229,f216,f244,f63])).
% 0.22/0.53  fof(f216,plain,(
% 0.22/0.53    spl7_30 <=> r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.22/0.53  fof(f229,plain,(
% 0.22/0.53    spl7_31 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X1,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.22/0.53  fof(f234,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK1) | ~r2_hidden(k1_funct_1(sK2,sK4),sK0) | (~spl7_30 | ~spl7_31)),
% 0.22/0.53    inference(resolution,[],[f230,f217])).
% 0.22/0.53  fof(f217,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK2) | ~spl7_30),
% 0.22/0.53    inference(avatar_component_clause,[],[f216])).
% 0.22/0.53  fof(f230,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X1,sK0)) ) | ~spl7_31),
% 0.22/0.53    inference(avatar_component_clause,[],[f229])).
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    ~spl7_12 | spl7_31 | ~spl7_14 | ~spl7_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f227,f54,f110,f229,f102])).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(X1,sK0) | r2_hidden(k4_tarski(X0,X1),sK1) | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 0.22/0.53    inference(superposition,[],[f49,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    sK1 = k8_relat_1(sK0,sK2) | ~spl7_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f54])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X6,X0,X5,X1] : (~v1_relat_1(k8_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0) | r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    spl7_30 | ~spl7_3 | ~spl7_18),
% 0.22/0.53    inference(avatar_split_clause,[],[f214,f140,f60,f216])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    spl7_3 <=> r2_hidden(sK4,k1_relat_1(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.53  fof(f214,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK4,k1_funct_1(sK2,sK4)),sK2) | (~spl7_3 | ~spl7_18)),
% 0.22/0.53    inference(resolution,[],[f72,f141])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    r2_hidden(sK4,k1_relat_1(sK2)) | ~spl7_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f60])).
% 0.22/0.53  fof(f213,plain,(
% 0.22/0.53    ~spl7_12 | ~spl7_11 | spl7_5 | ~spl7_28),
% 0.22/0.53    inference(avatar_split_clause,[],[f208,f204,f66,f98,f102])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    spl7_5 <=> k1_funct_1(sK2,sK3) = k1_funct_1(sK1,sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    spl7_28 <=> r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    k1_funct_1(sK2,sK3) = k1_funct_1(sK1,sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_28),
% 0.22/0.53    inference(resolution,[],[f205,f47])).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK2) | ~spl7_28),
% 0.22/0.53    inference(avatar_component_clause,[],[f204])).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    spl7_28 | ~spl7_6 | ~spl7_19 | ~spl7_26),
% 0.22/0.53    inference(avatar_split_clause,[],[f198,f189,f144,f75,f204])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    spl7_6 <=> r2_hidden(sK3,k1_relat_1(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK2) | (~spl7_6 | ~spl7_19 | ~spl7_26)),
% 0.22/0.53    inference(resolution,[],[f193,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    r2_hidden(sK3,k1_relat_1(sK1)) | ~spl7_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f75])).
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    ~spl7_12 | spl7_26 | ~spl7_14 | ~spl7_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f187,f54,f110,f189,f102])).
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(k4_tarski(X0,X1),sK2) | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 0.22/0.53    inference(superposition,[],[f50,f80])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X6,X0,X5,X1] : (~v1_relat_1(k8_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | r2_hidden(k4_tarski(X5,X6),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    ~spl7_14 | ~spl7_13 | spl7_25 | ~spl7_10 | ~spl7_18),
% 0.22/0.53    inference(avatar_split_clause,[],[f176,f140,f94,f178,f106,f110])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) | ~r2_hidden(k4_tarski(X0,X1),sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl7_10 | ~spl7_18)),
% 0.22/0.53    inference(resolution,[],[f161,f46])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    ~spl7_12 | spl7_21 | ~spl7_14 | ~spl7_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f153,f54,f110,f155,f102])).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(X1,sK0) | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 0.22/0.53    inference(superposition,[],[f51,f80])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    ~spl7_14 | spl7_19 | ~spl7_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f138,f106,f144,f110])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK1) | ~v1_relat_1(sK1)) ) | ~spl7_13),
% 0.22/0.53    inference(resolution,[],[f52,f107])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    v1_funct_1(sK1) | ~spl7_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f106])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(equality_resolution,[],[f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    ~spl7_12 | spl7_18 | ~spl7_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f137,f98,f140,f102])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2) | ~v1_relat_1(sK2)) ) | ~spl7_11),
% 0.22/0.53    inference(resolution,[],[f52,f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    v1_funct_1(sK2) | ~spl7_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f98])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    ~spl7_12 | ~spl7_11 | spl7_17 | spl7_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f127,f60,f132,f98,f102])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(k4_tarski(sK4,X0),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | spl7_3),
% 0.22/0.53    inference(resolution,[],[f61,f46])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ~r2_hidden(sK4,k1_relat_1(sK2)) | spl7_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f60])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ~spl7_14 | ~spl7_13 | spl7_16 | spl7_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f121,f57,f123,f106,f110])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(k4_tarski(sK4,X0),sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | spl7_2),
% 0.22/0.53    inference(resolution,[],[f58,f46])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ~r2_hidden(sK4,k1_relat_1(sK1)) | spl7_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f57])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    ~spl7_14 | ~spl7_13 | spl7_15 | ~spl7_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f114,f82,f118,f106,f110])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl7_7 <=> ! [X5] : (k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5) | ~r2_hidden(X5,k1_relat_1(sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)) ) | ~spl7_7),
% 0.22/0.53    inference(resolution,[],[f46,f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X5] : (~r2_hidden(X5,k1_relat_1(sK1)) | k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5)) ) | ~spl7_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f82])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    spl7_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f26,f110])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    v1_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    (((k1_funct_1(sK2,sK3) != k1_funct_1(sK1,sK3) & r2_hidden(sK3,k1_relat_1(sK1))) | ((~r2_hidden(k1_funct_1(sK2,sK4),sK0) | ~r2_hidden(sK4,k1_relat_1(sK2)) | ~r2_hidden(sK4,k1_relat_1(sK1))) & ((r2_hidden(k1_funct_1(sK2,sK4),sK0) & r2_hidden(sK4,k1_relat_1(sK2))) | r2_hidden(sK4,k1_relat_1(sK1)))) | sK1 != k8_relat_1(sK0,sK2)) & ((! [X5] : (k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5) | ~r2_hidden(X5,k1_relat_1(sK1))) & ! [X6] : ((r2_hidden(X6,k1_relat_1(sK1)) | ~r2_hidden(k1_funct_1(sK2,X6),sK0) | ~r2_hidden(X6,k1_relat_1(sK2))) & ((r2_hidden(k1_funct_1(sK2,X6),sK0) & r2_hidden(X6,k1_relat_1(sK2))) | ~r2_hidden(X6,k1_relat_1(sK1))))) | sK1 = k8_relat_1(sK0,sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f17,f16,f15,f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) | ? [X4] : ((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1)))) | k8_relat_1(X0,X2) != X1) & ((! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X1,X5) | ~r2_hidden(X5,k1_relat_1(X1))) & ! [X6] : ((r2_hidden(X6,k1_relat_1(X1)) | ~r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X6),X0) & r2_hidden(X6,k1_relat_1(X2))) | ~r2_hidden(X6,k1_relat_1(X1))))) | k8_relat_1(X0,X2) = X1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(sK1,X3) & r2_hidden(X3,k1_relat_1(sK1))) | ? [X4] : ((~r2_hidden(k1_funct_1(X2,X4),sK0) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(sK1))) & ((r2_hidden(k1_funct_1(X2,X4),sK0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(sK1)))) | sK1 != k8_relat_1(sK0,X2)) & ((! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(sK1,X5) | ~r2_hidden(X5,k1_relat_1(sK1))) & ! [X6] : ((r2_hidden(X6,k1_relat_1(sK1)) | ~r2_hidden(k1_funct_1(X2,X6),sK0) | ~r2_hidden(X6,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X6),sK0) & r2_hidden(X6,k1_relat_1(X2))) | ~r2_hidden(X6,k1_relat_1(sK1))))) | sK1 = k8_relat_1(sK0,X2)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X2] : ((? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(sK1,X3) & r2_hidden(X3,k1_relat_1(sK1))) | ? [X4] : ((~r2_hidden(k1_funct_1(X2,X4),sK0) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(sK1))) & ((r2_hidden(k1_funct_1(X2,X4),sK0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(sK1)))) | sK1 != k8_relat_1(sK0,X2)) & ((! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(sK1,X5) | ~r2_hidden(X5,k1_relat_1(sK1))) & ! [X6] : ((r2_hidden(X6,k1_relat_1(sK1)) | ~r2_hidden(k1_funct_1(X2,X6),sK0) | ~r2_hidden(X6,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X6),sK0) & r2_hidden(X6,k1_relat_1(X2))) | ~r2_hidden(X6,k1_relat_1(sK1))))) | sK1 = k8_relat_1(sK0,X2)) & v1_funct_1(X2) & v1_relat_1(X2)) => ((? [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3) & r2_hidden(X3,k1_relat_1(sK1))) | ? [X4] : ((~r2_hidden(k1_funct_1(sK2,X4),sK0) | ~r2_hidden(X4,k1_relat_1(sK2)) | ~r2_hidden(X4,k1_relat_1(sK1))) & ((r2_hidden(k1_funct_1(sK2,X4),sK0) & r2_hidden(X4,k1_relat_1(sK2))) | r2_hidden(X4,k1_relat_1(sK1)))) | sK1 != k8_relat_1(sK0,sK2)) & ((! [X5] : (k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5) | ~r2_hidden(X5,k1_relat_1(sK1))) & ! [X6] : ((r2_hidden(X6,k1_relat_1(sK1)) | ~r2_hidden(k1_funct_1(sK2,X6),sK0) | ~r2_hidden(X6,k1_relat_1(sK2))) & ((r2_hidden(k1_funct_1(sK2,X6),sK0) & r2_hidden(X6,k1_relat_1(sK2))) | ~r2_hidden(X6,k1_relat_1(sK1))))) | sK1 = k8_relat_1(sK0,sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X3] : (k1_funct_1(sK1,X3) != k1_funct_1(sK2,X3) & r2_hidden(X3,k1_relat_1(sK1))) => (k1_funct_1(sK2,sK3) != k1_funct_1(sK1,sK3) & r2_hidden(sK3,k1_relat_1(sK1)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X4] : ((~r2_hidden(k1_funct_1(sK2,X4),sK0) | ~r2_hidden(X4,k1_relat_1(sK2)) | ~r2_hidden(X4,k1_relat_1(sK1))) & ((r2_hidden(k1_funct_1(sK2,X4),sK0) & r2_hidden(X4,k1_relat_1(sK2))) | r2_hidden(X4,k1_relat_1(sK1)))) => ((~r2_hidden(k1_funct_1(sK2,sK4),sK0) | ~r2_hidden(sK4,k1_relat_1(sK2)) | ~r2_hidden(sK4,k1_relat_1(sK1))) & ((r2_hidden(k1_funct_1(sK2,sK4),sK0) & r2_hidden(sK4,k1_relat_1(sK2))) | r2_hidden(sK4,k1_relat_1(sK1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) | ? [X4] : ((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1)))) | k8_relat_1(X0,X2) != X1) & ((! [X5] : (k1_funct_1(X2,X5) = k1_funct_1(X1,X5) | ~r2_hidden(X5,k1_relat_1(X1))) & ! [X6] : ((r2_hidden(X6,k1_relat_1(X1)) | ~r2_hidden(k1_funct_1(X2,X6),X0) | ~r2_hidden(X6,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X6),X0) & r2_hidden(X6,k1_relat_1(X2))) | ~r2_hidden(X6,k1_relat_1(X1))))) | k8_relat_1(X0,X2) = X1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.53    inference(rectify,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : ((? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) | ? [X4] : ((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1)))) | k8_relat_1(X0,X2) != X1) & ((! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : ((r2_hidden(X4,k1_relat_1(X1)) | ~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X4,k1_relat_1(X1))))) | k8_relat_1(X0,X2) = X1) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : ((((? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) | ? [X4] : (((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1))))) | k8_relat_1(X0,X2) != X1) & ((! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : ((r2_hidden(X4,k1_relat_1(X1)) | (~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X4,k1_relat_1(X1))))) | k8_relat_1(X0,X2) = X1)) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : ((k8_relat_1(X0,X2) = X1 <~> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f6])).
% 0.22/0.53  fof(f6,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2] : ((k8_relat_1(X0,X2) = X1 <~> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,plain,(
% 0.22/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))))))))),
% 0.22/0.53    inference(rectify,[],[f4])).
% 0.22/0.53  fof(f4,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X3] : (r2_hidden(X3,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X3),X0) & r2_hidden(X3,k1_relat_1(X2))))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f3])).
% 0.22/0.53  fof(f3,conjecture,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X3] : (r2_hidden(X3,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X3),X0) & r2_hidden(X3,k1_relat_1(X2))))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    spl7_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f106])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    v1_funct_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    spl7_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f28,f102])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    v1_relat_1(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    spl7_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f29,f98])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    v1_funct_1(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    spl7_1 | spl7_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f30,f94,f54])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X6] : (r2_hidden(X6,k1_relat_1(sK2)) | ~r2_hidden(X6,k1_relat_1(sK1)) | sK1 = k8_relat_1(sK0,sK2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    spl7_1 | spl7_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f31,f90,f54])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X6] : (r2_hidden(k1_funct_1(sK2,X6),sK0) | ~r2_hidden(X6,k1_relat_1(sK1)) | sK1 = k8_relat_1(sK0,sK2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    spl7_1 | spl7_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f32,f86,f54])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X6] : (r2_hidden(X6,k1_relat_1(sK1)) | ~r2_hidden(k1_funct_1(sK2,X6),sK0) | ~r2_hidden(X6,k1_relat_1(sK2)) | sK1 = k8_relat_1(sK0,sK2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    spl7_1 | spl7_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f33,f82,f54])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X5] : (k1_funct_1(sK1,X5) = k1_funct_1(sK2,X5) | ~r2_hidden(X5,k1_relat_1(sK1)) | sK1 = k8_relat_1(sK0,sK2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ~spl7_1 | spl7_2 | spl7_3 | spl7_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f75,f60,f57,f54])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    r2_hidden(sK3,k1_relat_1(sK1)) | r2_hidden(sK4,k1_relat_1(sK2)) | r2_hidden(sK4,k1_relat_1(sK1)) | sK1 != k8_relat_1(sK0,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ~spl7_1 | spl7_2 | spl7_4 | spl7_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f75,f63,f57,f54])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    r2_hidden(sK3,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK2,sK4),sK0) | r2_hidden(sK4,k1_relat_1(sK1)) | sK1 != k8_relat_1(sK0,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f36,f75,f63,f60,f57,f54])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    r2_hidden(sK3,k1_relat_1(sK1)) | ~r2_hidden(k1_funct_1(sK2,sK4),sK0) | ~r2_hidden(sK4,k1_relat_1(sK2)) | ~r2_hidden(sK4,k1_relat_1(sK1)) | sK1 != k8_relat_1(sK0,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ~spl7_1 | spl7_2 | spl7_3 | ~spl7_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f37,f66,f60,f57,f54])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    k1_funct_1(sK2,sK3) != k1_funct_1(sK1,sK3) | r2_hidden(sK4,k1_relat_1(sK2)) | r2_hidden(sK4,k1_relat_1(sK1)) | sK1 != k8_relat_1(sK0,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ~spl7_1 | spl7_2 | spl7_4 | ~spl7_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f66,f63,f57,f54])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    k1_funct_1(sK2,sK3) != k1_funct_1(sK1,sK3) | r2_hidden(k1_funct_1(sK2,sK4),sK0) | r2_hidden(sK4,k1_relat_1(sK1)) | sK1 != k8_relat_1(sK0,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f66,f63,f60,f57,f54])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    k1_funct_1(sK2,sK3) != k1_funct_1(sK1,sK3) | ~r2_hidden(k1_funct_1(sK2,sK4),sK0) | ~r2_hidden(sK4,k1_relat_1(sK2)) | ~r2_hidden(sK4,k1_relat_1(sK1)) | sK1 != k8_relat_1(sK0,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (26212)------------------------------
% 0.22/0.53  % (26212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26212)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (26212)Memory used [KB]: 11641
% 0.22/0.53  % (26212)Time elapsed: 0.041 s
% 0.22/0.53  % (26212)------------------------------
% 0.22/0.53  % (26212)------------------------------
% 0.22/0.53  % (26198)Success in time 0.172 s
%------------------------------------------------------------------------------
