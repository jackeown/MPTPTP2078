%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0316+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:34 EST 2020

% Result     : Theorem 27.30s
% Output     : CNFRefutation 27.30s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 109 expanded)
%              Number of clauses        :   34 (  35 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  305 ( 488 expanded)
%              Number of equality atoms :  112 ( 178 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f693,plain,(
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

fof(f694,plain,(
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
    inference(rectify,[],[f693])).

fof(f695,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK20(X0,X1) != X0
          | ~ r2_hidden(sK20(X0,X1),X1) )
        & ( sK20(X0,X1) = X0
          | r2_hidden(sK20(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f696,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK20(X0,X1) != X0
            | ~ r2_hidden(sK20(X0,X1),X1) )
          & ( sK20(X0,X1) = X0
            | r2_hidden(sK20(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f694,f695])).

fof(f1037,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f696])).

fof(f1809,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f1037])).

fof(f1810,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f1809])).

fof(f338,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f339,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      <=> ( r2_hidden(X1,X3)
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f338])).

fof(f572,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <~> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f339])).

fof(f770,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f572])).

fof(f771,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f770])).

fof(f772,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(X1,X3)
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
        & ( ( r2_hidden(X1,X3)
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) )
   => ( ( ~ r2_hidden(sK51,sK53)
        | sK50 != sK52
        | ~ r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53)) )
      & ( ( r2_hidden(sK51,sK53)
          & sK50 = sK52 )
        | r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53)) ) ) ),
    introduced(choice_axiom,[])).

fof(f773,plain,
    ( ( ~ r2_hidden(sK51,sK53)
      | sK50 != sK52
      | ~ r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53)) )
    & ( ( r2_hidden(sK51,sK53)
        & sK50 = sK52 )
      | r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK50,sK51,sK52,sK53])],[f771,f772])).

fof(f1281,plain,
    ( r2_hidden(sK51,sK53)
    | r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53)) ),
    inference(cnf_transformation,[],[f773])).

fof(f320,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
     => r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f558,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2))
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f320])).

fof(f1253,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2))
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f558])).

fof(f319,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f763,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f319])).

fof(f764,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f763])).

fof(f1251,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f764])).

fof(f1250,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f764])).

fof(f392,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f788,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f392])).

fof(f1361,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f788])).

fof(f1036,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f696])).

fof(f1811,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f1036])).

fof(f1360,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f788])).

fof(f285,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f722,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f285])).

fof(f723,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f722])).

fof(f726,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK28(X0,X1,X8),sK29(X0,X1,X8)) = X8
        & r2_hidden(sK29(X0,X1,X8),X1)
        & r2_hidden(sK28(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f725,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK26(X0,X1,X2),sK27(X0,X1,X2)) = X3
        & r2_hidden(sK27(X0,X1,X2),X1)
        & r2_hidden(sK26(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f724,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK25(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK25(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK25(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK25(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f727,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK25(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK25(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK26(X0,X1,X2),sK27(X0,X1,X2)) = sK25(X0,X1,X2)
              & r2_hidden(sK27(X0,X1,X2),X1)
              & r2_hidden(sK26(X0,X1,X2),X0) )
            | r2_hidden(sK25(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK28(X0,X1,X8),sK29(X0,X1,X8)) = X8
                & r2_hidden(sK29(X0,X1,X8),X1)
                & r2_hidden(sK28(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25,sK26,sK27,sK28,sK29])],[f723,f726,f725,f724])).

fof(f1181,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f727])).

fof(f1840,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f1181])).

fof(f1841,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f1840])).

fof(f1282,plain,
    ( ~ r2_hidden(sK51,sK53)
    | sK50 != sK52
    | ~ r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53)) ),
    inference(cnf_transformation,[],[f773])).

fof(f1280,plain,
    ( sK50 = sK52
    | r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53)) ),
    inference(cnf_transformation,[],[f773])).

cnf(c_10080,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_91179,plain,
    ( k1_tarski(sK52) = k1_tarski(sK52) ),
    inference(instantiation,[status(thm)],[c_10080])).

cnf(c_231,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1810])).

cnf(c_81762,plain,
    ( r2_hidden(sK52,k1_tarski(sK52)) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_10085,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_25205,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK50,k1_tarski(sK52))
    | k1_tarski(sK52) != X1
    | sK50 != X0 ),
    inference(instantiation,[status(thm)],[c_10085])).

cnf(c_49444,plain,
    ( ~ r2_hidden(sK52,X0)
    | r2_hidden(sK50,k1_tarski(sK52))
    | k1_tarski(sK52) != X0
    | sK50 != sK52 ),
    inference(instantiation,[status(thm)],[c_25205])).

cnf(c_52965,plain,
    ( ~ r2_hidden(sK52,k1_tarski(sK52))
    | r2_hidden(sK50,k1_tarski(sK52))
    | k1_tarski(sK52) != k1_tarski(sK52)
    | sK50 != sK52 ),
    inference(instantiation,[status(thm)],[c_49444])).

cnf(c_464,negated_conjecture,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53))
    | r2_hidden(sK51,sK53) ),
    inference(cnf_transformation,[],[f1281])).

cnf(c_16639,plain,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53)) = iProver_top
    | r2_hidden(sK51,sK53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_436,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) ),
    inference(cnf_transformation,[],[f1253])).

cnf(c_16652,plain,
    ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_46678,plain,
    ( r2_hidden(k4_tarski(sK51,sK50),k2_zfmisc_1(sK53,k1_tarski(sK52))) = iProver_top
    | r2_hidden(sK51,sK53) = iProver_top ),
    inference(superposition,[status(thm)],[c_16639,c_16652])).

cnf(c_590,plain,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53)) = iProver_top
    | r2_hidden(sK51,sK53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_434,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f1251])).

cnf(c_19034,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK51),k2_zfmisc_1(X1,sK53))
    | r2_hidden(sK51,sK53) ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_37753,plain,
    ( ~ r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53))
    | r2_hidden(sK51,sK53) ),
    inference(instantiation,[status(thm)],[c_19034])).

cnf(c_37754,plain,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53)) != iProver_top
    | r2_hidden(sK51,sK53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37753])).

cnf(c_48130,plain,
    ( r2_hidden(sK51,sK53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46678,c_590,c_37754])).

cnf(c_435,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f1250])).

cnf(c_25107,plain,
    ( ~ r2_hidden(k4_tarski(sK50,X0),k2_zfmisc_1(k1_tarski(sK52),X1))
    | r2_hidden(sK50,k1_tarski(sK52)) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_39930,plain,
    ( ~ r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53))
    | r2_hidden(sK50,k1_tarski(sK52)) ),
    inference(instantiation,[status(thm)],[c_25107])).

cnf(c_543,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) = X1 ),
    inference(cnf_transformation,[],[f1361])).

cnf(c_25594,plain,
    ( r2_hidden(sK51,sK53)
    | k4_xboole_0(sK53,k1_tarski(sK51)) = sK53 ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_232,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f1811])).

cnf(c_18387,plain,
    ( ~ r2_hidden(sK50,k1_tarski(sK52))
    | sK50 = sK52 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_544,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_tarski(X0)) != X1 ),
    inference(cnf_transformation,[],[f1360])).

cnf(c_17910,plain,
    ( ~ r2_hidden(sK51,sK53)
    | k4_xboole_0(sK53,k1_tarski(sK51)) != sK53 ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_17923,plain,
    ( k4_xboole_0(sK53,k1_tarski(sK51)) != sK53
    | r2_hidden(sK51,sK53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17910])).

cnf(c_365,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f1841])).

cnf(c_17861,plain,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53))
    | ~ r2_hidden(sK50,k1_tarski(sK52))
    | ~ r2_hidden(sK51,sK53) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_463,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53))
    | ~ r2_hidden(sK51,sK53)
    | sK50 != sK52 ),
    inference(cnf_transformation,[],[f1282])).

cnf(c_465,negated_conjecture,
    ( r2_hidden(k4_tarski(sK50,sK51),k2_zfmisc_1(k1_tarski(sK52),sK53))
    | sK50 = sK52 ),
    inference(cnf_transformation,[],[f1280])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_91179,c_81762,c_52965,c_48130,c_39930,c_25594,c_18387,c_17923,c_17861,c_463,c_465])).

%------------------------------------------------------------------------------
