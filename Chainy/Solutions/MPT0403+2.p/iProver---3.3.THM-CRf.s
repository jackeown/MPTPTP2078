%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0403+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:39 EST 2020

% Result     : Theorem 39.15s
% Output     : CNFRefutation 39.15s
% Verified   : 
% Statistics : Number of formulae       :   55 (  73 expanded)
%              Number of clauses        :   17 (  19 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :  202 ( 255 expanded)
%              Number of equality atoms :   44 (  55 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1495,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f149])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1513,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1453,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f2216,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f1513,f1453])).

fof(f2353,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f1495,f2216])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1510,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1302,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f546,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f935,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f546])).

fof(f1272,plain,(
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
    inference(nnf_transformation,[],[f935])).

fof(f1273,plain,(
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
    inference(rectify,[],[f1272])).

fof(f1275,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK95(X1,X4))
        & r2_hidden(sK95(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f1274,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK94(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK94(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1276,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK94(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK94(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK95(X1,X4))
              & r2_hidden(sK95(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK94,sK95])],[f1273,f1275,f1274])).

fof(f2169,plain,(
    ! [X0,X3,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(sK94(X0,X1),X3)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1276])).

fof(f548,axiom,(
    ! [X0,X1,X2] :
      ( k2_setfam_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k2_xboole_0(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1282,plain,(
    ! [X0,X1,X2] :
      ( ( k2_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k2_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k2_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k2_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k2_xboole_0(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_setfam_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f548])).

fof(f1283,plain,(
    ! [X0,X1,X2] :
      ( ( k2_setfam_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k2_xboole_0(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k2_xboole_0(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k2_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k2_xboole_0(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_setfam_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f1282])).

fof(f1286,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k2_xboole_0(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k2_xboole_0(sK101(X0,X1,X8),sK102(X0,X1,X8)) = X8
        & r2_hidden(sK102(X0,X1,X8),X1)
        & r2_hidden(sK101(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1285,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k2_xboole_0(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k2_xboole_0(sK99(X0,X1,X2),sK100(X0,X1,X2)) = X3
        & r2_hidden(sK100(X0,X1,X2),X1)
        & r2_hidden(sK99(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1284,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k2_xboole_0(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k2_xboole_0(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k2_xboole_0(X4,X5) != sK98(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK98(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k2_xboole_0(X6,X7) = sK98(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK98(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1287,plain,(
    ! [X0,X1,X2] :
      ( ( k2_setfam_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k2_xboole_0(X4,X5) != sK98(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK98(X0,X1,X2),X2) )
          & ( ( k2_xboole_0(sK99(X0,X1,X2),sK100(X0,X1,X2)) = sK98(X0,X1,X2)
              & r2_hidden(sK100(X0,X1,X2),X1)
              & r2_hidden(sK99(X0,X1,X2),X0) )
            | r2_hidden(sK98(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k2_xboole_0(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k2_xboole_0(sK101(X0,X1,X8),sK102(X0,X1,X8)) = X8
                & r2_hidden(sK102(X0,X1,X8),X1)
                & r2_hidden(sK101(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_setfam_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK98,sK99,sK100,sK101,sK102])],[f1283,f1286,f1285,f1284])).

fof(f2177,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k2_xboole_0(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1287])).

fof(f2682,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k5_xboole_0(k5_xboole_0(X9,X10),k4_xboole_0(X9,k4_xboole_0(X9,X10))) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_setfam_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f2177,f2216])).

fof(f2836,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k5_xboole_0(k5_xboole_0(X9,X10),k4_xboole_0(X9,k4_xboole_0(X9,X10))),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_setfam_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f2682])).

fof(f2837,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k5_xboole_0(k5_xboole_0(X9,X10),k4_xboole_0(X9,k4_xboole_0(X9,X10))),k2_setfam_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f2836])).

fof(f2168,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK94(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1276])).

fof(f568,conjecture,(
    ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f569,negated_conjecture,(
    ~ ! [X0] : r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(negated_conjecture,[],[f568])).

fof(f949,plain,(
    ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0)) ),
    inference(ennf_transformation,[],[f569])).

fof(f1293,plain,
    ( ? [X0] : ~ r1_setfam_1(X0,k2_setfam_1(X0,X0))
   => ~ r1_setfam_1(sK105,k2_setfam_1(sK105,sK105)) ),
    introduced(choice_axiom,[])).

fof(f1294,plain,(
    ~ r1_setfam_1(sK105,k2_setfam_1(sK105,sK105)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK105])],[f949,f1293])).

fof(f2201,plain,(
    ~ r1_setfam_1(sK105,k2_setfam_1(sK105,sK105)) ),
    inference(cnf_transformation,[],[f1294])).

cnf(c_196,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(cnf_transformation,[],[f2353])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1510])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1302])).

cnf(c_26353,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(theory_normalisation,[status(thm)],[c_196,c_211,c_7])).

cnf(c_66199,plain,
    ( r1_tarski(sK94(sK105,k2_setfam_1(sK105,sK105)),k5_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),k5_xboole_0(X0,k4_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),k4_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),X0))))) ),
    inference(instantiation,[status(thm)],[c_26353])).

cnf(c_145920,plain,
    ( r1_tarski(sK94(sK105,k2_setfam_1(sK105,sK105)),k5_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),k5_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),k4_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),k4_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),sK94(sK105,k2_setfam_1(sK105,sK105))))))) ),
    inference(instantiation,[status(thm)],[c_66199])).

cnf(c_854,plain,
    ( r1_setfam_1(X0,X1)
    | ~ r1_tarski(sK94(X0,X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f2169])).

cnf(c_44888,plain,
    ( r1_setfam_1(sK105,k2_setfam_1(sK105,sK105))
    | ~ r1_tarski(sK94(sK105,k2_setfam_1(sK105,sK105)),X0)
    | ~ r2_hidden(X0,k2_setfam_1(sK105,sK105)) ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_88362,plain,
    ( r1_setfam_1(sK105,k2_setfam_1(sK105,sK105))
    | ~ r1_tarski(sK94(sK105,k2_setfam_1(sK105,sK105)),k5_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),k5_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),k4_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),k4_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),sK94(sK105,k2_setfam_1(sK105,sK105)))))))
    | ~ r2_hidden(k5_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),k5_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),k4_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),k4_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),sK94(sK105,k2_setfam_1(sK105,sK105)))))),k2_setfam_1(sK105,sK105)) ),
    inference(instantiation,[status(thm)],[c_44888])).

cnf(c_866,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k5_xboole_0(k5_xboole_0(X2,X0),k4_xboole_0(X2,k4_xboole_0(X2,X0))),k2_setfam_1(X3,X1)) ),
    inference(cnf_transformation,[],[f2837])).

cnf(c_26139,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k5_xboole_0(X0,k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X0)))),k2_setfam_1(X3,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_866,c_211,c_7])).

cnf(c_50333,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK94(sK105,k2_setfam_1(sK105,sK105)),sK105)
    | r2_hidden(k5_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,sK94(sK105,k2_setfam_1(sK105,sK105)))))),k2_setfam_1(X1,sK105)) ),
    inference(instantiation,[status(thm)],[c_26139])).

cnf(c_70249,plain,
    ( ~ r2_hidden(sK94(sK105,k2_setfam_1(sK105,sK105)),sK105)
    | r2_hidden(k5_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),k5_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),k4_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),k4_xboole_0(sK94(sK105,k2_setfam_1(sK105,sK105)),sK94(sK105,k2_setfam_1(sK105,sK105)))))),k2_setfam_1(sK105,sK105)) ),
    inference(instantiation,[status(thm)],[c_50333])).

cnf(c_855,plain,
    ( r1_setfam_1(X0,X1)
    | r2_hidden(sK94(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2168])).

cnf(c_44877,plain,
    ( r1_setfam_1(sK105,k2_setfam_1(sK105,sK105))
    | r2_hidden(sK94(sK105,k2_setfam_1(sK105,sK105)),sK105) ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_889,negated_conjecture,
    ( ~ r1_setfam_1(sK105,k2_setfam_1(sK105,sK105)) ),
    inference(cnf_transformation,[],[f2201])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_145920,c_88362,c_70249,c_44877,c_889])).

%------------------------------------------------------------------------------
