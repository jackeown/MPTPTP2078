%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0730+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:46 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 107 expanded)
%              Number of leaves         :    8 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  198 ( 530 expanded)
%              Number of equality atoms :   59 ( 146 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1384,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1324,f1309])).

fof(f1309,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f1296,f1278])).

fof(f1278,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f1218])).

fof(f1218,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1151])).

fof(f1151,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f1149,f1150])).

fof(f1150,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1149,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f1148])).

fof(f1148,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f1296,plain,(
    sK0 != sK1 ),
    inference(subsumption_resolution,[],[f1295,f1269])).

fof(f1269,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f1185,f1184])).

fof(f1184,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1054])).

fof(f1054,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f1185,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f1058])).

fof(f1058,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f1295,plain,
    ( sK0 != sK1
    | ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    inference(inner_rewriting,[],[f1265])).

fof(f1265,plain,
    ( sK0 != sK1
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f1169,f1184])).

fof(f1169,plain,
    ( sK0 != sK1
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f1127])).

fof(f1127,plain,
    ( ( ( sK0 != sK1
        & ~ r2_hidden(sK0,sK1) )
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( sK0 = sK1
      | r2_hidden(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1125,f1126])).

fof(f1126,plain,
    ( ? [X0,X1] :
        ( ( ( X0 != X1
            & ~ r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_ordinal1(X1)) )
        & ( X0 = X1
          | r2_hidden(X0,X1)
          | r2_hidden(X0,k1_ordinal1(X1)) ) )
   => ( ( ( sK0 != sK1
          & ~ r2_hidden(sK0,sK1) )
        | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
      & ( sK0 = sK1
        | r2_hidden(sK0,sK1)
        | r2_hidden(sK0,k1_ordinal1(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1125,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f1124])).

fof(f1124,plain,(
    ? [X0,X1] :
      ( ( ( X0 != X1
          & ~ r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k1_ordinal1(X1)) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1069])).

fof(f1069,plain,(
    ? [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <~> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f1061])).

fof(f1061,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,k1_ordinal1(X1))
      <=> ( X0 = X1
          | r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f1060])).

fof(f1060,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f1324,plain,(
    r2_hidden(sK0,k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f1297,f1299,f1275])).

fof(f1275,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f1193])).

fof(f1193,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1143])).

fof(f1143,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f1141,f1142])).

fof(f1142,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1141,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f1140])).

fof(f1140,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f1139])).

fof(f1139,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f1299,plain,(
    r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(subsumption_resolution,[],[f1298,f1297])).

fof(f1298,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(subsumption_resolution,[],[f1267,f1296])).

fof(f1267,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f1167,f1184])).

fof(f1167,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f1127])).

fof(f1297,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1266,f1274])).

fof(f1274,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f1194])).

fof(f1194,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1143])).

fof(f1266,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f1168,f1184])).

fof(f1168,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f1127])).
%------------------------------------------------------------------------------
