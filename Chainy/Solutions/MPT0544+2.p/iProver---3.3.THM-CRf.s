%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0544+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:44 EST 2020

% Result     : Theorem 31.41s
% Output     : CNFRefutation 31.41s
% Verified   : 
% Statistics : Number of formulae       :   69 (  98 expanded)
%              Number of clauses        :   22 (  23 expanded)
%              Number of leaves         :   17 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  276 ( 424 expanded)
%              Number of equality atoms :   63 (  92 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f643,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1235,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f643])).

fof(f1796,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1235])).

fof(f1797,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1796])).

fof(f1800,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK133(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK133(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1799,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK132(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK132(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1798,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK131(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK131(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK131(X0,X1,X2)),X0) )
          | r2_hidden(sK131(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1801,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK131(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK131(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK132(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK132(X0,X1,X2),sK131(X0,X1,X2)),X0) )
                | r2_hidden(sK131(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK133(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK133(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK131,sK132,sK133])],[f1797,f1800,f1799,f1798])).

fof(f2892,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X4,sK131(X0,X1,X2)),X0)
      | ~ r2_hidden(sK131(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1801])).

fof(f647,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1815,plain,(
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
    inference(nnf_transformation,[],[f647])).

fof(f1816,plain,(
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
    inference(rectify,[],[f1815])).

fof(f1819,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK143(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1818,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK142(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1817,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK141(X0,X1),X3),X0)
          | ~ r2_hidden(sK141(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK141(X0,X1),X4),X0)
          | r2_hidden(sK141(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1820,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK141(X0,X1),X3),X0)
            | ~ r2_hidden(sK141(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK141(X0,X1),sK142(X0,X1)),X0)
            | r2_hidden(sK141(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK143(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK141,sK142,sK143])],[f1816,f1819,f1818,f1817])).

fof(f2904,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1820])).

fof(f3816,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f2904])).

fof(f409,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1008,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(ennf_transformation,[],[f409])).

fof(f2457,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f1008])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2018,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f3466,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,k1_tarski(X1))) != k1_tarski(X1) ) ),
    inference(definition_unfolding,[],[f2457,f2018])).

fof(f648,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1821,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f648])).

fof(f1822,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f1821])).

fof(f1825,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK146(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1824,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK145(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1823,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK144(X0,X1)),X0)
          | ~ r2_hidden(sK144(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK144(X0,X1)),X0)
          | r2_hidden(sK144(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1826,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK144(X0,X1)),X0)
            | ~ r2_hidden(sK144(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK145(X0,X1),sK144(X0,X1)),X0)
            | r2_hidden(sK144(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK146(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK144,sK145,sK146])],[f1822,f1825,f1824,f1823])).

fof(f2908,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1826])).

fof(f3818,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f2908])).

fof(f2907,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK146(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1826])).

fof(f3819,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK146(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f2907])).

fof(f410,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1009,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f410])).

fof(f2458,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k1_tarski(X0)) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1009])).

fof(f3467,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) = k1_tarski(X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f2458,f2018])).

fof(f2890,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK132(X0,X1,X2),sK131(X0,X1,X2)),X0)
      | r2_hidden(sK131(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1801])).

fof(f723,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f724,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(negated_conjecture,[],[f723])).

fof(f1323,plain,(
    ? [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) != k2_relat_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f724])).

fof(f1845,plain,
    ( ? [X0] :
        ( k9_relat_1(X0,k1_relat_1(X0)) != k2_relat_1(X0)
        & v1_relat_1(X0) )
   => ( k9_relat_1(sK155,k1_relat_1(sK155)) != k2_relat_1(sK155)
      & v1_relat_1(sK155) ) ),
    introduced(choice_axiom,[])).

fof(f1846,plain,
    ( k9_relat_1(sK155,k1_relat_1(sK155)) != k2_relat_1(sK155)
    & v1_relat_1(sK155) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK155])],[f1323,f1845])).

fof(f3002,plain,(
    k9_relat_1(sK155,k1_relat_1(sK155)) != k2_relat_1(sK155) ),
    inference(cnf_transformation,[],[f1846])).

fof(f3001,plain,(
    v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f1846])).

cnf(c_1010,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK131(X2,X1,X3),X3)
    | ~ r2_hidden(k4_tarski(X0,sK131(X2,X1,X3)),X2)
    | ~ v1_relat_1(X2)
    | k9_relat_1(X2,X1) = X3 ),
    inference(cnf_transformation,[],[f2892])).

cnf(c_46559,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK155))
    | ~ r2_hidden(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155)),k2_relat_1(sK155))
    | ~ r2_hidden(k4_tarski(X0,sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))),sK155)
    | ~ v1_relat_1(sK155)
    | k9_relat_1(sK155,k1_relat_1(sK155)) = k2_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_1010])).

cnf(c_86119,plain,
    ( ~ r2_hidden(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155)),k2_relat_1(sK155))
    | ~ r2_hidden(sK146(sK155,sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))),k1_relat_1(sK155))
    | ~ r2_hidden(k4_tarski(sK146(sK155,sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))),sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))),sK155)
    | ~ v1_relat_1(sK155)
    | k9_relat_1(sK155,k1_relat_1(sK155)) = k2_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_46559])).

cnf(c_1028,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3816])).

cnf(c_86103,plain,
    ( r2_hidden(sK146(sK155,sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))),k1_relat_1(sK155))
    | ~ r2_hidden(k4_tarski(sK146(sK155,sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))),sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))),sK155) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_582,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3466])).

cnf(c_85684,plain,
    ( r2_hidden(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155)),k2_relat_1(sK155))
    | k4_xboole_0(k2_relat_1(sK155),k4_xboole_0(k2_relat_1(sK155),k1_tarski(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))))) != k1_tarski(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))) ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_1032,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f3818])).

cnf(c_78615,plain,
    ( r2_hidden(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155)),k2_relat_1(sK155))
    | ~ r2_hidden(k4_tarski(sK132(sK155,k1_relat_1(sK155),k2_relat_1(sK155)),sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))),sK155) ),
    inference(instantiation,[status(thm)],[c_1032])).

cnf(c_78616,plain,
    ( r2_hidden(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155)),k2_relat_1(sK155)) = iProver_top
    | r2_hidden(k4_tarski(sK132(sK155,k1_relat_1(sK155),k2_relat_1(sK155)),sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))),sK155) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78615])).

cnf(c_1033,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK146(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f3819])).

cnf(c_57434,plain,
    ( ~ r2_hidden(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155)),k2_relat_1(sK155))
    | r2_hidden(k4_tarski(sK146(sK155,sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))),sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))),sK155) ),
    inference(instantiation,[status(thm)],[c_1033])).

cnf(c_583,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3467])).

cnf(c_57334,plain,
    ( ~ r2_hidden(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155)),k2_relat_1(sK155))
    | k4_xboole_0(k2_relat_1(sK155),k4_xboole_0(k2_relat_1(sK155),k1_tarski(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))))) = k1_tarski(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_57344,plain,
    ( k4_xboole_0(k2_relat_1(sK155),k4_xboole_0(k2_relat_1(sK155),k1_tarski(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))))) = k1_tarski(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155)))
    | r2_hidden(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155)),k2_relat_1(sK155)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57334])).

cnf(c_1012,plain,
    ( r2_hidden(sK131(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK132(X0,X1,X2),sK131(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f2890])).

cnf(c_46564,plain,
    ( r2_hidden(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155)),k2_relat_1(sK155))
    | r2_hidden(k4_tarski(sK132(sK155,k1_relat_1(sK155),k2_relat_1(sK155)),sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))),sK155)
    | ~ v1_relat_1(sK155)
    | k9_relat_1(sK155,k1_relat_1(sK155)) = k2_relat_1(sK155) ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_46565,plain,
    ( k9_relat_1(sK155,k1_relat_1(sK155)) = k2_relat_1(sK155)
    | r2_hidden(sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155)),k2_relat_1(sK155)) = iProver_top
    | r2_hidden(k4_tarski(sK132(sK155,k1_relat_1(sK155),k2_relat_1(sK155)),sK131(sK155,k1_relat_1(sK155),k2_relat_1(sK155))),sK155) = iProver_top
    | v1_relat_1(sK155) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46564])).

cnf(c_1124,negated_conjecture,
    ( k9_relat_1(sK155,k1_relat_1(sK155)) != k2_relat_1(sK155) ),
    inference(cnf_transformation,[],[f3002])).

cnf(c_1125,negated_conjecture,
    ( v1_relat_1(sK155) ),
    inference(cnf_transformation,[],[f3001])).

cnf(c_1215,plain,
    ( v1_relat_1(sK155) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_86119,c_86103,c_85684,c_78616,c_57434,c_57344,c_46565,c_1124,c_1215,c_1125])).

%------------------------------------------------------------------------------
