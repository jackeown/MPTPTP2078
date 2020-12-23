%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0402+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:28 EST 2020

% Result     : Theorem 4.40s
% Output     : Refutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 144 expanded)
%              Number of leaves         :   29 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  318 ( 504 expanded)
%              Number of equality atoms :   88 (  88 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8797,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1320,f1325,f1330,f1335,f1383,f1775,f1780,f7764,f7821,f7833,f7835,f8777,f8793,f8796])).

fof(f8796,plain,
    ( sK11(k2_tarski(sK0,sK1),sK3) != k2_xboole_0(sK3,sK11(k2_tarski(sK0,sK1),sK3))
    | sK0 != sK11(k2_tarski(sK0,sK1),sK3)
    | r1_tarski(sK11(k2_tarski(sK0,sK1),sK3),sK0)
    | ~ r1_tarski(k2_xboole_0(sK3,sK11(k2_tarski(sK0,sK1),sK3)),sK11(k2_tarski(sK0,sK1),sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f8793,plain,
    ( sK1 != sK11(k2_tarski(sK0,sK1),sK3)
    | k1_xboole_0 != k4_xboole_0(sK3,sK11(k2_tarski(sK0,sK1),sK3))
    | k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f8777,plain,
    ( spl42_484
    | spl42_485
    | ~ spl42_51 ),
    inference(avatar_split_clause,[],[f8544,f1777,f8774,f8770])).

fof(f8770,plain,
    ( spl42_484
  <=> sK1 = sK11(k2_tarski(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_484])])).

fof(f8774,plain,
    ( spl42_485
  <=> sK0 = sK11(k2_tarski(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_485])])).

fof(f1777,plain,
    ( spl42_51
  <=> r2_hidden(sK11(k2_tarski(sK0,sK1),sK3),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_51])])).

fof(f8544,plain,
    ( sK0 = sK11(k2_tarski(sK0,sK1),sK3)
    | sK1 = sK11(k2_tarski(sK0,sK1),sK3)
    | ~ spl42_51 ),
    inference(resolution,[],[f1779,f1286])).

fof(f1286,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f983])).

fof(f983,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f808])).

fof(f808,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK12(X0,X1,X2) != X1
              & sK12(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK12(X0,X1,X2),X2) )
          & ( sK12(X0,X1,X2) = X1
            | sK12(X0,X1,X2) = X0
            | r2_hidden(sK12(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f806,f807])).

fof(f807,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK12(X0,X1,X2) != X1
            & sK12(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK12(X0,X1,X2),X2) )
        & ( sK12(X0,X1,X2) = X1
          | sK12(X0,X1,X2) = X0
          | r2_hidden(sK12(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f806,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f805])).

fof(f805,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f804])).

fof(f804,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f176])).

fof(f176,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f1779,plain,
    ( r2_hidden(sK11(k2_tarski(sK0,sK1),sK3),k2_tarski(sK0,sK1))
    | ~ spl42_51 ),
    inference(avatar_component_clause,[],[f1777])).

fof(f7835,plain,
    ( spl42_432
    | ~ spl42_50 ),
    inference(avatar_split_clause,[],[f7528,f1772,f7694])).

fof(f7694,plain,
    ( spl42_432
  <=> k1_xboole_0 = k4_xboole_0(sK3,sK11(k2_tarski(sK0,sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_432])])).

fof(f1772,plain,
    ( spl42_50
  <=> r1_tarski(sK3,sK11(k2_tarski(sK0,sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_50])])).

fof(f7528,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,sK11(k2_tarski(sK0,sK1),sK3))
    | ~ spl42_50 ),
    inference(resolution,[],[f1774,f1072])).

fof(f1072,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f837])).

fof(f837,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f97])).

fof(f97,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f1774,plain,
    ( r1_tarski(sK3,sK11(k2_tarski(sK0,sK1),sK3))
    | ~ spl42_50 ),
    inference(avatar_component_clause,[],[f1772])).

fof(f7833,plain,
    ( spl42_435
    | ~ spl42_50 ),
    inference(avatar_split_clause,[],[f7526,f1772,f7710])).

fof(f7710,plain,
    ( spl42_435
  <=> sK11(k2_tarski(sK0,sK1),sK3) = k2_xboole_0(sK3,sK11(k2_tarski(sK0,sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_435])])).

fof(f7526,plain,
    ( sK11(k2_tarski(sK0,sK1),sK3) = k2_xboole_0(sK3,sK11(k2_tarski(sK0,sK1),sK3))
    | ~ spl42_50 ),
    inference(resolution,[],[f1774,f914])).

fof(f914,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f600])).

fof(f600,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f7821,plain,
    ( ~ spl42_440
    | spl42_2
    | ~ spl42_50 ),
    inference(avatar_split_clause,[],[f7522,f1772,f1322,f7735])).

fof(f7735,plain,
    ( spl42_440
  <=> r1_tarski(sK11(k2_tarski(sK0,sK1),sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_440])])).

fof(f1322,plain,
    ( spl42_2
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_2])])).

fof(f7522,plain,
    ( ~ r1_tarski(sK11(k2_tarski(sK0,sK1),sK3),sK0)
    | spl42_2
    | ~ spl42_50 ),
    inference(resolution,[],[f1774,f1444])).

fof(f1444,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK0)
        | ~ r1_tarski(sK3,X1) )
    | spl42_2 ),
    inference(resolution,[],[f1324,f896])).

fof(f896,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f591])).

fof(f591,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f590])).

fof(f590,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1324,plain,
    ( ~ r1_tarski(sK3,sK0)
    | spl42_2 ),
    inference(avatar_component_clause,[],[f1322])).

fof(f7764,plain,
    ( spl42_443
    | ~ spl42_50 ),
    inference(avatar_split_clause,[],[f7339,f1772,f7754])).

fof(f7754,plain,
    ( spl42_443
  <=> r1_tarski(k2_xboole_0(sK3,sK11(k2_tarski(sK0,sK1),sK3)),sK11(k2_tarski(sK0,sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_443])])).

fof(f7339,plain,
    ( r1_tarski(k2_xboole_0(sK3,sK11(k2_tarski(sK0,sK1),sK3)),sK11(k2_tarski(sK0,sK1),sK3))
    | ~ spl42_50 ),
    inference(unit_resulting_resolution,[],[f1261,f1774,f895])).

fof(f895,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f589])).

fof(f589,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f588])).

fof(f588,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f161])).

fof(f161,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f1261,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f907])).

fof(f907,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f768])).

fof(f768,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f767])).

fof(f767,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1780,plain,
    ( spl42_51
    | ~ spl42_3
    | ~ spl42_4 ),
    inference(avatar_split_clause,[],[f1766,f1332,f1327,f1777])).

fof(f1327,plain,
    ( spl42_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_3])])).

fof(f1332,plain,
    ( spl42_4
  <=> r1_setfam_1(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_4])])).

fof(f1766,plain,
    ( r2_hidden(sK11(k2_tarski(sK0,sK1),sK3),k2_tarski(sK0,sK1))
    | ~ spl42_3
    | ~ spl42_4 ),
    inference(unit_resulting_resolution,[],[f1329,f1334,f934])).

fof(f934,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK11(X1,X4),X1)
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f787])).

fof(f787,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK10(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK10(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK11(X1,X4))
              & r2_hidden(sK11(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f784,f786,f785])).

fof(f785,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK10(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK10(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f786,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK11(X1,X4))
        & r2_hidden(sK11(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f784,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f783])).

fof(f783,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f608])).

fof(f608,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f545])).

fof(f545,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f1334,plain,
    ( r1_setfam_1(sK2,k2_tarski(sK0,sK1))
    | ~ spl42_4 ),
    inference(avatar_component_clause,[],[f1332])).

fof(f1329,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl42_3 ),
    inference(avatar_component_clause,[],[f1327])).

fof(f1775,plain,
    ( spl42_50
    | ~ spl42_3
    | ~ spl42_4 ),
    inference(avatar_split_clause,[],[f1767,f1332,f1327,f1772])).

fof(f1767,plain,
    ( r1_tarski(sK3,sK11(k2_tarski(sK0,sK1),sK3))
    | ~ spl42_3
    | ~ spl42_4 ),
    inference(unit_resulting_resolution,[],[f1329,f1334,f935])).

fof(f935,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(X4,sK11(X1,X4))
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f787])).

fof(f1383,plain,
    ( ~ spl42_8
    | spl42_1 ),
    inference(avatar_split_clause,[],[f1353,f1317,f1379])).

fof(f1379,plain,
    ( spl42_8
  <=> k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_8])])).

fof(f1317,plain,
    ( spl42_1
  <=> r1_tarski(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_1])])).

fof(f1353,plain,
    ( k1_xboole_0 != k4_xboole_0(sK3,sK1)
    | spl42_1 ),
    inference(unit_resulting_resolution,[],[f1319,f1069])).

fof(f1069,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f836])).

fof(f836,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1319,plain,
    ( ~ r1_tarski(sK3,sK1)
    | spl42_1 ),
    inference(avatar_component_clause,[],[f1317])).

fof(f1335,plain,(
    spl42_4 ),
    inference(avatar_split_clause,[],[f887,f1332])).

fof(f887,plain,(
    r1_setfam_1(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f758])).

fof(f758,plain,
    ( ~ r1_tarski(sK3,sK1)
    & ~ r1_tarski(sK3,sK0)
    & r2_hidden(sK3,sK2)
    & r1_setfam_1(sK2,k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f583,f757,f756])).

fof(f756,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(X3,X1)
            & ~ r1_tarski(X3,X0)
            & r2_hidden(X3,X2) )
        & r1_setfam_1(X2,k2_tarski(X0,X1)) )
   => ( ? [X3] :
          ( ~ r1_tarski(X3,sK1)
          & ~ r1_tarski(X3,sK0)
          & r2_hidden(X3,sK2) )
      & r1_setfam_1(sK2,k2_tarski(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f757,plain,
    ( ? [X3] :
        ( ~ r1_tarski(X3,sK1)
        & ~ r1_tarski(X3,sK0)
        & r2_hidden(X3,sK2) )
   => ( ~ r1_tarski(sK3,sK1)
      & ~ r1_tarski(sK3,sK0)
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f583,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X1)
          & ~ r1_tarski(X3,X0)
          & r2_hidden(X3,X2) )
      & r1_setfam_1(X2,k2_tarski(X0,X1)) ) ),
    inference(ennf_transformation,[],[f565])).

fof(f565,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_setfam_1(X2,k2_tarski(X0,X1))
       => ! [X3] :
            ~ ( ~ r1_tarski(X3,X1)
              & ~ r1_tarski(X3,X0)
              & r2_hidden(X3,X2) ) ) ),
    inference(negated_conjecture,[],[f564])).

fof(f564,conjecture,(
    ! [X0,X1,X2] :
      ( r1_setfam_1(X2,k2_tarski(X0,X1))
     => ! [X3] :
          ~ ( ~ r1_tarski(X3,X1)
            & ~ r1_tarski(X3,X0)
            & r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_setfam_1)).

fof(f1330,plain,(
    spl42_3 ),
    inference(avatar_split_clause,[],[f888,f1327])).

fof(f888,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f758])).

fof(f1325,plain,(
    ~ spl42_2 ),
    inference(avatar_split_clause,[],[f889,f1322])).

fof(f889,plain,(
    ~ r1_tarski(sK3,sK0) ),
    inference(cnf_transformation,[],[f758])).

fof(f1320,plain,(
    ~ spl42_1 ),
    inference(avatar_split_clause,[],[f890,f1317])).

fof(f890,plain,(
    ~ r1_tarski(sK3,sK1) ),
    inference(cnf_transformation,[],[f758])).
%------------------------------------------------------------------------------
