%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0851+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:53 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   38 (  40 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :   12
%              Number of atoms          :  125 ( 129 expanded)
%              Number of equality atoms :  112 ( 114 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1622,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1534,f1619,f1621])).

fof(f1621,plain,(
    spl45_2 ),
    inference(avatar_contradiction_clause,[],[f1620])).

fof(f1620,plain,
    ( $false
    | spl45_2 ),
    inference(subsumption_resolution,[],[f1533,f1602])).

fof(f1602,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(equality_resolution,[],[f1504])).

fof(f1504,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(X4,X5) != k4_tarski(X6,X7)
      | k2_mcart_1(k4_tarski(X4,X5)) = X5 ) ),
    inference(equality_resolution,[],[f1503])).

fof(f1503,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X5
      | k2_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f1413])).

fof(f1413,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X5
      | k4_tarski(X4,X5) != X0
      | k2_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f1340])).

fof(f1340,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ( sK3(X0,X1) != X1
              & k4_tarski(sK2(X0,X1),sK3(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f1338,f1339])).

fof(f1339,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X3
          & k4_tarski(X2,X3) = X0 )
     => ( sK3(X0,X1) != X1
        & k4_tarski(sK2(X0,X1),sK3(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f1338,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X3
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f1337])).

fof(f1337,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k2_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X5
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X5
                | k4_tarski(X4,X5) != X0 )
            | k2_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f1306])).

fof(f1306,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X5
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f1300])).

fof(f1300,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k2_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X5 ) ) ) ),
    inference(rectify,[],[f1273])).

fof(f1273,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k2_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_mcart_1)).

fof(f1533,plain,
    ( sK1 != k2_mcart_1(k4_tarski(sK0,sK1))
    | spl45_2 ),
    inference(avatar_component_clause,[],[f1532])).

fof(f1532,plain,
    ( spl45_2
  <=> sK1 = k2_mcart_1(k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_2])])).

fof(f1619,plain,(
    spl45_1 ),
    inference(avatar_contradiction_clause,[],[f1615])).

fof(f1615,plain,
    ( $false
    | spl45_1 ),
    inference(unit_resulting_resolution,[],[f1530,f1613])).

fof(f1613,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(equality_resolution,[],[f1508])).

fof(f1508,plain,(
    ! [X6,X4,X7,X5] :
      ( k4_tarski(X4,X5) != k4_tarski(X6,X7)
      | k1_mcart_1(k4_tarski(X4,X5)) = X4 ) ),
    inference(equality_resolution,[],[f1507])).

fof(f1507,plain,(
    ! [X6,X4,X7,X5,X1] :
      ( X1 = X4
      | k1_mcart_1(k4_tarski(X4,X5)) != X1
      | k4_tarski(X4,X5) != k4_tarski(X6,X7) ) ),
    inference(equality_resolution,[],[f1416])).

fof(f1416,plain,(
    ! [X6,X4,X0,X7,X5,X1] :
      ( X1 = X4
      | k4_tarski(X4,X5) != X0
      | k1_mcart_1(X0) != X1
      | k4_tarski(X6,X7) != X0 ) ),
    inference(cnf_transformation,[],[f1344])).

fof(f1344,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ( sK4(X0,X1) != X1
              & k4_tarski(sK4(X0,X1),sK5(X0,X1)) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f1342,f1343])).

fof(f1343,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X1 != X2
          & k4_tarski(X2,X3) = X0 )
     => ( sK4(X0,X1) != X1
        & k4_tarski(sK4(X0,X1),sK5(X0,X1)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f1342,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k1_mcart_1(X0) = X1
            | ? [X2,X3] :
                ( X1 != X2
                & k4_tarski(X2,X3) = X0 ) )
          & ( ! [X4,X5] :
                ( X1 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X1 ) )
      | ! [X6,X7] : k4_tarski(X6,X7) != X0 ) ),
    inference(rectify,[],[f1341])).

fof(f1341,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ( k1_mcart_1(X0) = X3
            | ? [X4,X5] :
                ( X3 != X4
                & k4_tarski(X4,X5) = X0 ) )
          & ( ! [X4,X5] :
                ( X3 = X4
                | k4_tarski(X4,X5) != X0 )
            | k1_mcart_1(X0) != X3 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(nnf_transformation,[],[f1307])).

fof(f1307,plain,(
    ! [X0] :
      ( ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( X3 = X4
              | k4_tarski(X4,X5) != X0 ) )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f1301])).

fof(f1301,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X3] :
          ( k1_mcart_1(X0) = X3
        <=> ! [X4,X5] :
              ( k4_tarski(X4,X5) = X0
             => X3 = X4 ) ) ) ),
    inference(rectify,[],[f1272])).

fof(f1272,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ! [X1] :
          ( k1_mcart_1(X0) = X1
        <=> ! [X2,X3] :
              ( k4_tarski(X2,X3) = X0
             => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_mcart_1)).

fof(f1530,plain,
    ( sK0 != k1_mcart_1(k4_tarski(sK0,sK1))
    | spl45_1 ),
    inference(avatar_component_clause,[],[f1529])).

fof(f1529,plain,
    ( spl45_1
  <=> sK0 = k1_mcart_1(k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_1])])).

fof(f1534,plain,
    ( ~ spl45_1
    | ~ spl45_2 ),
    inference(avatar_split_clause,[],[f1412,f1532,f1529])).

fof(f1412,plain,
    ( sK1 != k2_mcart_1(k4_tarski(sK0,sK1))
    | sK0 != k1_mcart_1(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f1336])).

fof(f1336,plain,
    ( sK1 != k2_mcart_1(k4_tarski(sK0,sK1))
    | sK0 != k1_mcart_1(k4_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1305,f1335])).

fof(f1335,plain,
    ( ? [X0,X1] :
        ( k2_mcart_1(k4_tarski(X0,X1)) != X1
        | k1_mcart_1(k4_tarski(X0,X1)) != X0 )
   => ( sK1 != k2_mcart_1(k4_tarski(sK0,sK1))
      | sK0 != k1_mcart_1(k4_tarski(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f1305,plain,(
    ? [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) != X1
      | k1_mcart_1(k4_tarski(X0,X1)) != X0 ) ),
    inference(ennf_transformation,[],[f1299])).

fof(f1299,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_mcart_1(k4_tarski(X0,X1)) = X1
        & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    inference(negated_conjecture,[],[f1298])).

fof(f1298,conjecture,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
%------------------------------------------------------------------------------
