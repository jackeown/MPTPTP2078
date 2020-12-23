%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0301+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:34 EST 2020

% Result     : Theorem 47.21s
% Output     : CNFRefutation 47.21s
% Verified   : 
% Statistics : Number of formulae       :  389 (1733 expanded)
%              Number of clauses        :  182 ( 430 expanded)
%              Number of leaves         :   63 ( 456 expanded)
%              Depth                    :   21
%              Number of atoms          : 1180 (5025 expanded)
%              Number of equality atoms :  565 (3088 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    8 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f321,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f320])).

fof(f536,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f321])).

fof(f721,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f536])).

fof(f722,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f721])).

fof(f723,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK43
          & k1_xboole_0 != sK42 )
        | k1_xboole_0 != k2_zfmisc_1(sK42,sK43) )
      & ( k1_xboole_0 = sK43
        | k1_xboole_0 = sK42
        | k1_xboole_0 = k2_zfmisc_1(sK42,sK43) ) ) ),
    introduced(choice_axiom,[])).

fof(f724,plain,
    ( ( ( k1_xboole_0 != sK43
        & k1_xboole_0 != sK42 )
      | k1_xboole_0 != k2_zfmisc_1(sK42,sK43) )
    & ( k1_xboole_0 = sK43
      | k1_xboole_0 = sK42
      | k1_xboole_0 = k2_zfmisc_1(sK42,sK43) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK42,sK43])],[f722,f723])).

fof(f1195,plain,
    ( k1_xboole_0 = sK43
    | k1_xboole_0 = sK42
    | k1_xboole_0 = k2_zfmisc_1(sK42,sK43) ),
    inference(cnf_transformation,[],[f724])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f761,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1602,plain,
    ( o_0_0_xboole_0 = sK43
    | o_0_0_xboole_0 = sK42
    | o_0_0_xboole_0 = k2_zfmisc_1(sK42,sK43) ),
    inference(definition_unfolding,[],[f1195,f761,f761,f761])).

fof(f318,axiom,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
        <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) )
     => k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f534,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
      | ? [X4,X5] :
          ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
        <~> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(ennf_transformation,[],[f318])).

fof(f718,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
      | ? [X4,X5] :
          ( ( ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))
            | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) )
          & ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))
            | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ) ) ),
    inference(nnf_transformation,[],[f534])).

fof(f719,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4,X5] :
          ( ( ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))
            | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) )
          & ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3))
            | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK40(X0,X1,X2,X3),sK41(X0,X1,X2,X3)),k2_zfmisc_1(X2,X3))
          | ~ r2_hidden(k4_tarski(sK40(X0,X1,X2,X3),sK41(X0,X1,X2,X3)),k2_zfmisc_1(X0,X1)) )
        & ( r2_hidden(k4_tarski(sK40(X0,X1,X2,X3),sK41(X0,X1,X2,X3)),k2_zfmisc_1(X2,X3))
          | r2_hidden(k4_tarski(sK40(X0,X1,X2,X3),sK41(X0,X1,X2,X3)),k2_zfmisc_1(X0,X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f720,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
      | ( ( ~ r2_hidden(k4_tarski(sK40(X0,X1,X2,X3),sK41(X0,X1,X2,X3)),k2_zfmisc_1(X2,X3))
          | ~ r2_hidden(k4_tarski(sK40(X0,X1,X2,X3),sK41(X0,X1,X2,X3)),k2_zfmisc_1(X0,X1)) )
        & ( r2_hidden(k4_tarski(sK40(X0,X1,X2,X3),sK41(X0,X1,X2,X3)),k2_zfmisc_1(X2,X3))
          | r2_hidden(k4_tarski(sK40(X0,X1,X2,X3),sK41(X0,X1,X2,X3)),k2_zfmisc_1(X0,X1)) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK40,sK41])],[f718,f719])).

fof(f1192,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
      | r2_hidden(k4_tarski(sK40(X0,X1,X2,X3),sK41(X0,X1,X2,X3)),k2_zfmisc_1(X2,X3))
      | r2_hidden(k4_tarski(sK40(X0,X1,X2,X3),sK41(X0,X1,X2,X3)),k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f720])).

fof(f317,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
     => r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f533,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2))
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f317])).

fof(f1191,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2))
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f533])).

fof(f112,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f911,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f112])).

fof(f1425,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f911,f761,f761])).

fof(f373,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f737,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f373])).

fof(f738,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f737])).

fof(f1273,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f738])).

fof(f1767,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f1273])).

fof(f313,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f531,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f313])).

fof(f712,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k4_tarski(sK36(X1,X2,X3),sK37(X1,X2,X3)) = X3
        & r2_hidden(sK37(X1,X2,X3),X2)
        & r2_hidden(sK36(X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f713,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k4_tarski(sK36(X1,X2,X3),sK37(X1,X2,X3)) = X3
        & r2_hidden(sK37(X1,X2,X3),X2)
        & r2_hidden(sK36(X1,X2,X3),X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK36,sK37])],[f531,f712])).

fof(f1181,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK36(X1,X2,X3),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f713])).

fof(f316,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f716,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f316])).

fof(f717,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f716])).

fof(f1190,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f717])).

fof(f380,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f742,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f380])).

fof(f743,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f742])).

fof(f1285,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | r2_hidden(X1,X2)
      | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f743])).

fof(f226,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1065,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f226])).

fof(f166,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f969,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f166])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f909,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f1319,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f969,f909])).

fof(f1320,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f1065,f1319])).

fof(f1665,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | r2_hidden(X1,X2)
      | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2) != k1_tarski(X0) ) ),
    inference(definition_unfolding,[],[f1285,f1320])).

fof(f1287,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f743])).

fof(f1663,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2) = k1_tarski(X0)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f1287,f1320])).

fof(f1768,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k1_tarski(X1)),k4_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X1),k1_tarski(X1)))),X2) = k1_tarski(X1)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f1663])).

fof(f361,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1259,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f361])).

fof(f1648,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2))) != o_0_0_xboole_0 ),
    inference(definition_unfolding,[],[f1259,f1319,f1320,f761])).

fof(f359,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_xboole_0(k2_tarski(X0,X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f559,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f359])).

fof(f560,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f559])).

fof(f1257,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X2),X1) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f560])).

fof(f1646,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),X1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),X1))) = X1
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f1257,f1319,f1320])).

fof(f153,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f650,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f153])).

fof(f955,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f650])).

fof(f956,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f650])).

fof(f149,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f951,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f149])).

fof(f1454,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f951,f1319])).

fof(f141,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f492,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f141])).

fof(f493,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f492])).

fof(f943,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f493])).

fof(f1448,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ) ),
    inference(definition_unfolding,[],[f943,f1319])).

fof(f135,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f484,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f135])).

fof(f485,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f484])).

fof(f935,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f485])).

fof(f132,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f479,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f931,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f479])).

fof(f1439,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(definition_unfolding,[],[f931,f761])).

fof(f1702,plain,(
    r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(equality_resolution,[],[f1439])).

fof(f127,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f474,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f127])).

fof(f926,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f474])).

fof(f1435,plain,(
    ! [X0] :
      ( r2_xboole_0(o_0_0_xboole_0,X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f926,f761,f761])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f591,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f592,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f591])).

fof(f593,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f594,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f592,f593])).

fof(f760,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f594])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f656,plain,(
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

fof(f657,plain,(
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
    inference(rectify,[],[f656])).

fof(f658,plain,(
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

fof(f659,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f657,f658])).

fof(f986,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f659])).

fof(f1710,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f986])).

fof(f1711,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f1710])).

fof(f131,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f930,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f131])).

fof(f1437,plain,(
    ! [X0] : r1_xboole_0(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f930,f761])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f412,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f797,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f412])).

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

fof(f685,plain,(
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

fof(f686,plain,(
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
    inference(rectify,[],[f685])).

fof(f689,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK28(X0,X1,X8),sK29(X0,X1,X8)) = X8
        & r2_hidden(sK29(X0,X1,X8),X1)
        & r2_hidden(sK28(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f688,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK26(X0,X1,X2),sK27(X0,X1,X2)) = X3
        & r2_hidden(sK27(X0,X1,X2),X1)
        & r2_hidden(sK26(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f687,plain,(
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

fof(f690,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25,sK26,sK27,sK28,sK29])],[f686,f689,f688,f687])).

fof(f1128,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK29(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f690])).

fof(f1744,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK29(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1128])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f499,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f950,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f499])).

fof(f35,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f419,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f632,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK15(X0,X1),X0)
        & r2_hidden(sK15(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f633,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK15(X0,X1),X0)
        & r2_hidden(sK15(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f419,f632])).

fof(f817,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK15(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f633])).

fof(f1127,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK28(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f690])).

fof(f1745,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK28(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1127])).

fof(f331,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f541,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f331])).

fof(f1208,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f541])).

fof(f1609,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | o_0_0_xboole_0 != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(definition_unfolding,[],[f1208,f761])).

fof(f377,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f741,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f377])).

fof(f1281,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f741])).

fof(f1660,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f1281,f761])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f405,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f416,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f405])).

fof(f628,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK13(X0,X1),X1)
        & r2_hidden(sK13(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f629,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK13(X0,X1),X1)
          & r2_hidden(sK13(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f416,f628])).

fof(f810,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f629])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f636,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f637,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f636])).

fof(f822,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f637])).

fof(f330,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f725,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f330])).

fof(f1206,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f725])).

fof(f1757,plain,(
    ! [X1] : k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) != k1_tarski(X1) ),
    inference(equality_resolution,[],[f1206])).

fof(f88,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f886,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

fof(f1406,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) ),
    inference(definition_unfolding,[],[f886,f909,f761,f761])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f899,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f1414,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f899,f761])).

fof(f354,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f554,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f354])).

fof(f1247,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = X1
      | k1_tarski(X0) = X2
      | k1_tarski(X0) = X1
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f554])).

fof(f1639,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = X1
      | k1_tarski(X0) = X2
      | k1_tarski(X0) = X1
      | k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) != k1_tarski(X0) ) ),
    inference(definition_unfolding,[],[f1247,f1319])).

fof(f163,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f966,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f163])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f758,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f76,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f872,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

fof(f1393,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,o_0_0_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f872,f1319,f761])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f615,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f616,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f615])).

fof(f788,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f616])).

fof(f348,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f728,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f348])).

fof(f1230,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f728])).

fof(f379,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f574,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f379])).

fof(f1283,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f574])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f410,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f595,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f410])).

fof(f596,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f595])).

fof(f597,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f598,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f596,f597])).

fof(f763,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f598])).

fof(f121,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f468,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f121])).

fof(f920,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f468])).

fof(f762,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f598])).

fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f486,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f936,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f486])).

fof(f1441,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f936,f761])).

fof(f1197,plain,
    ( k1_xboole_0 != sK43
    | k1_xboole_0 != k2_zfmisc_1(sK42,sK43) ),
    inference(cnf_transformation,[],[f724])).

fof(f1600,plain,
    ( o_0_0_xboole_0 != sK43
    | o_0_0_xboole_0 != k2_zfmisc_1(sK42,sK43) ),
    inference(definition_unfolding,[],[f1197,f761,f761])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f420,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f634,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK16(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f635,plain,(
    ! [X0] :
      ( r2_hidden(sK16(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f420,f634])).

fof(f819,plain,(
    ! [X0] :
      ( r2_hidden(sK16(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f635])).

fof(f1358,plain,(
    ! [X0] :
      ( r2_hidden(sK16(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f819,f761])).

fof(f284,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f681,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f284])).

fof(f682,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f681])).

fof(f683,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK24(X0,X1),X0)
          | ~ r2_hidden(sK24(X0,X1),X1) )
        & ( r1_tarski(sK24(X0,X1),X0)
          | r2_hidden(sK24(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f684,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK24(X0,X1),X0)
            | ~ r2_hidden(sK24(X0,X1),X1) )
          & ( r1_tarski(sK24(X0,X1),X0)
            | r2_hidden(sK24(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f682,f683])).

fof(f1123,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f684])).

fof(f1740,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f1123])).

fof(f1196,plain,
    ( k1_xboole_0 != sK42
    | k1_xboole_0 != k2_zfmisc_1(sK42,sK43) ),
    inference(cnf_transformation,[],[f724])).

fof(f1601,plain,
    ( o_0_0_xboole_0 != sK42
    | o_0_0_xboole_0 != k2_zfmisc_1(sK42,sK43) ),
    inference(definition_unfolding,[],[f1196,f761,f761])).

fof(f1182,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK37(X1,X2,X3),X2)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f713])).

cnf(c_431,negated_conjecture,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK42,sK43)
    | o_0_0_xboole_0 = sK42
    | o_0_0_xboole_0 = sK43 ),
    inference(cnf_transformation,[],[f1602])).

cnf(c_427,plain,
    ( r2_hidden(k4_tarski(sK40(X0,X1,X2,X3),sK41(X0,X1,X2,X3)),k2_zfmisc_1(X2,X3))
    | r2_hidden(k4_tarski(sK40(X0,X1,X2,X3),sK41(X0,X1,X2,X3)),k2_zfmisc_1(X0,X1))
    | k2_zfmisc_1(X2,X3) = k2_zfmisc_1(X0,X1) ),
    inference(cnf_transformation,[],[f1192])).

cnf(c_16330,plain,
    ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
    | r2_hidden(k4_tarski(sK40(X2,X3,X0,X1),sK41(X2,X3,X0,X1)),k2_zfmisc_1(X0,X1)) = iProver_top
    | r2_hidden(k4_tarski(sK40(X2,X3,X0,X1),sK41(X2,X3,X0,X1)),k2_zfmisc_1(X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_20951,plain,
    ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(sK42,sK43)
    | sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r2_hidden(k4_tarski(sK40(sK42,sK43,X0,X1),sK41(sK42,sK43,X0,X1)),k2_zfmisc_1(X0,X1)) = iProver_top
    | r2_hidden(k4_tarski(sK40(sK42,sK43,X0,X1),sK41(sK42,sK43,X0,X1)),o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_16330])).

cnf(c_425,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) ),
    inference(cnf_transformation,[],[f1191])).

cnf(c_16332,plain,
    ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) != iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X3,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_23162,plain,
    ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(sK42,sK43)
    | sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r2_hidden(k4_tarski(sK41(sK42,sK43,X0,X1),sK40(sK42,sK43,X0,X1)),k2_zfmisc_1(X1,X0)) = iProver_top
    | r2_hidden(k4_tarski(sK40(sK42,sK43,X0,X1),sK41(sK42,sK43,X0,X1)),o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_20951,c_16332])).

cnf(c_23457,plain,
    ( k2_zfmisc_1(sK43,sK42) = k2_zfmisc_1(sK42,sK43)
    | sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r2_hidden(k4_tarski(sK41(sK42,sK43,sK43,sK42),sK40(sK42,sK43,sK43,sK42)),o_0_0_xboole_0) = iProver_top
    | r2_hidden(k4_tarski(sK40(sK42,sK43,sK43,sK42),sK41(sK42,sK43,sK43,sK42)),o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_23162])).

cnf(c_156,plain,
    ( k4_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1425])).

cnf(c_507,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f1767])).

cnf(c_16305,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_27388,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_156,c_16305])).

cnf(c_28059,plain,
    ( k2_zfmisc_1(sK43,sK42) = k2_zfmisc_1(sK42,sK43)
    | sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r2_hidden(k4_tarski(sK40(sK42,sK43,sK43,sK42),sK41(sK42,sK43,sK43,sK42)),o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_23457,c_27388])).

cnf(c_28082,plain,
    ( k2_zfmisc_1(sK43,sK42) = k2_zfmisc_1(sK42,sK43)
    | sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_28059,c_27388])).

cnf(c_28117,plain,
    ( k2_zfmisc_1(sK43,sK42) = o_0_0_xboole_0
    | sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_28082,c_431])).

cnf(c_28507,plain,
    ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(sK43,sK42)
    | sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r2_hidden(k4_tarski(sK40(X0,X1,sK43,sK42),sK41(X0,X1,sK43,sK42)),k2_zfmisc_1(X0,X1)) = iProver_top
    | r2_hidden(k4_tarski(sK40(X0,X1,sK43,sK42),sK41(X0,X1,sK43,sK42)),o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_28117,c_16330])).

cnf(c_28584,plain,
    ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(sK43,sK42)
    | sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r2_hidden(k4_tarski(sK40(X0,X1,sK43,sK42),sK41(X0,X1,sK43,sK42)),k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_28507,c_27388])).

cnf(c_417,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(sK36(X1,X2,X3),X1) ),
    inference(cnf_transformation,[],[f1181])).

cnf(c_16337,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(sK36(X1,X2,X3),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_31285,plain,
    ( sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r1_tarski(X0,o_0_0_xboole_0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(sK36(sK42,sK43,X1),sK42) = iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_16337])).

cnf(c_32196,plain,
    ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(sK43,sK42)
    | sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r1_tarski(k2_zfmisc_1(X0,X1),o_0_0_xboole_0) != iProver_top
    | r2_hidden(sK36(sK42,sK43,k4_tarski(sK40(X0,X1,sK43,sK42),sK41(X0,X1,sK43,sK42))),sK42) = iProver_top ),
    inference(superposition,[status(thm)],[c_28584,c_31285])).

cnf(c_422,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f1190])).

cnf(c_16346,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_47226,plain,
    ( sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r2_hidden(X0,sK42) != iProver_top
    | r2_hidden(X1,sK43) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_16346])).

cnf(c_49257,plain,
    ( sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r2_hidden(X0,sK42) != iProver_top
    | r2_hidden(X1,sK43) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_47226,c_27388])).

cnf(c_49266,plain,
    ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(sK43,sK42)
    | sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r1_tarski(k2_zfmisc_1(X0,X1),o_0_0_xboole_0) != iProver_top
    | r2_hidden(X2,sK43) != iProver_top ),
    inference(superposition,[status(thm)],[c_32196,c_49257])).

cnf(c_520,plain,
    ( r2_hidden(X0,X1)
    | X0 = X2
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k1_tarski(X0)),k4_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X2),k1_tarski(X0)))),X1) != k1_tarski(X2) ),
    inference(cnf_transformation,[],[f1665])).

cnf(c_620,plain,
    ( r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0) != k1_tarski(o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_518,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X0)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X0)))),X1) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1768])).

cnf(c_624,plain,
    ( r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0) = k1_tarski(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_518])).

cnf(c_493,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),X2))) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1648])).

cnf(c_692,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0))) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_491,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),X1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k1_tarski(X2)),k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),k1_tarski(X2)))),X1))) = X1 ),
    inference(cnf_transformation,[],[f1646])).

cnf(c_695,plain,
    ( ~ r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k4_xboole_0(k1_tarski(o_0_0_xboole_0),k1_tarski(o_0_0_xboole_0)))),o_0_0_xboole_0))) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_201,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f955])).

cnf(c_1114,plain,
    ( ~ r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
    | k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_200,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f956])).

cnf(c_1116,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_200])).

cnf(c_1118,plain,
    ( k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0
    | r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1116])).

cnf(c_196,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(cnf_transformation,[],[f1454])).

cnf(c_1127,plain,
    ( r1_tarski(o_0_0_xboole_0,k5_xboole_0(k5_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0),k4_xboole_0(o_0_0_xboole_0,k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)))) ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_1126,plain,
    ( r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_196])).

cnf(c_1128,plain,
    ( r1_tarski(o_0_0_xboole_0,k5_xboole_0(k5_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0),k4_xboole_0(o_0_0_xboole_0,k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_188,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(X0,k5_xboole_0(k5_xboole_0(X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ),
    inference(cnf_transformation,[],[f1448])).

cnf(c_1151,plain,
    ( ~ r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ r1_tarski(o_0_0_xboole_0,k5_xboole_0(k5_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0),k4_xboole_0(o_0_0_xboole_0,k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0))))
    | r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_1150,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(X0,k5_xboole_0(k5_xboole_0(X2,X1),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_188])).

cnf(c_1152,plain,
    ( r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | r1_tarski(o_0_0_xboole_0,k5_xboole_0(k5_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0),k4_xboole_0(o_0_0_xboole_0,k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)))) != iProver_top
    | r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1150])).

cnf(c_180,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f935])).

cnf(c_1167,plain,
    ( ~ r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_180])).

cnf(c_1166,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_1168,plain,
    ( r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1166])).

cnf(c_177,plain,
    ( r1_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1702])).

cnf(c_20953,plain,
    ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(sK42,sK43)
    | sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r2_hidden(k4_tarski(sK40(X0,X1,sK42,sK43),sK41(X0,X1,sK42,sK43)),k2_zfmisc_1(X0,X1)) = iProver_top
    | r2_hidden(k4_tarski(sK40(X0,X1,sK42,sK43),sK41(X0,X1,sK42,sK43)),o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_16330])).

cnf(c_20995,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0) = k2_zfmisc_1(sK42,sK43)
    | sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r2_hidden(k4_tarski(sK40(o_0_0_xboole_0,o_0_0_xboole_0,sK42,sK43),sK41(o_0_0_xboole_0,o_0_0_xboole_0,sK42,sK43)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) = iProver_top
    | r2_hidden(k4_tarski(sK40(o_0_0_xboole_0,o_0_0_xboole_0,sK42,sK43),sK41(o_0_0_xboole_0,o_0_0_xboole_0,sK42,sK43)),o_0_0_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_20953])).

cnf(c_171,plain,
    ( r2_xboole_0(o_0_0_xboole_0,X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1435])).

cnf(c_22744,plain,
    ( r2_xboole_0(o_0_0_xboole_0,k2_zfmisc_1(sK42,sK43))
    | o_0_0_xboole_0 = k2_zfmisc_1(sK42,sK43) ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_8,plain,
    ( r2_hidden(sK4(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f760])).

cnf(c_31831,plain,
    ( r2_hidden(sK4(k2_zfmisc_1(sK42,sK43)),k2_zfmisc_1(sK42,sK43))
    | v1_xboole_0(k2_zfmisc_1(sK42,sK43)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9563,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_31834,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(sK42,sK43))
    | k2_zfmisc_1(sK42,sK43) != X0 ),
    inference(instantiation,[status(thm)],[c_9563])).

cnf(c_31836,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK42,sK43))
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k2_zfmisc_1(sK42,sK43) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_31834])).

cnf(c_231,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1711])).

cnf(c_32066,plain,
    ( r2_hidden(k2_zfmisc_1(sK42,sK43),k1_tarski(k2_zfmisc_1(sK42,sK43))) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_33195,plain,
    ( r2_hidden(k4_tarski(sK40(X0,X1,sK42,sK43),sK41(X0,X1,sK42,sK43)),k2_zfmisc_1(X0,X1))
    | r2_hidden(k4_tarski(sK40(X0,X1,sK42,sK43),sK41(X0,X1,sK42,sK43)),k2_zfmisc_1(sK42,sK43))
    | k2_zfmisc_1(sK42,sK43) = k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_427])).

cnf(c_33202,plain,
    ( k2_zfmisc_1(sK42,sK43) = k2_zfmisc_1(X0,X1)
    | r2_hidden(k4_tarski(sK40(X0,X1,sK42,sK43),sK41(X0,X1,sK42,sK43)),k2_zfmisc_1(X0,X1)) = iProver_top
    | r2_hidden(k4_tarski(sK40(X0,X1,sK42,sK43),sK41(X0,X1,sK42,sK43)),k2_zfmisc_1(sK42,sK43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33195])).

cnf(c_33204,plain,
    ( k2_zfmisc_1(sK42,sK43) = k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | r2_hidden(k4_tarski(sK40(o_0_0_xboole_0,o_0_0_xboole_0,sK42,sK43),sK41(o_0_0_xboole_0,o_0_0_xboole_0,sK42,sK43)),k2_zfmisc_1(sK42,sK43)) = iProver_top
    | r2_hidden(k4_tarski(sK40(o_0_0_xboole_0,o_0_0_xboole_0,sK42,sK43),sK41(o_0_0_xboole_0,o_0_0_xboole_0,sK42,sK43)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_33202])).

cnf(c_175,plain,
    ( r1_xboole_0(X0,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1437])).

cnf(c_33490,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK42,sK43),o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_33493,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK42,sK43),o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33490])).

cnf(c_44,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f797])).

cnf(c_33691,plain,
    ( r1_xboole_0(X0,k2_zfmisc_1(sK42,sK43))
    | ~ r1_xboole_0(k2_zfmisc_1(sK42,sK43),X0) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_33692,plain,
    ( r1_xboole_0(X0,k2_zfmisc_1(sK42,sK43)) = iProver_top
    | r1_xboole_0(k2_zfmisc_1(sK42,sK43),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33691])).

cnf(c_33694,plain,
    ( r1_xboole_0(k2_zfmisc_1(sK42,sK43),o_0_0_xboole_0) != iProver_top
    | r1_xboole_0(o_0_0_xboole_0,k2_zfmisc_1(sK42,sK43)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_33692])).

cnf(c_367,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK29(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f1744])).

cnf(c_195,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f950])).

cnf(c_34710,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(resolution,[status(thm)],[c_367,c_195])).

cnf(c_34728,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(resolution,[status(thm)],[c_34710,c_8])).

cnf(c_34730,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_34728])).

cnf(c_34729,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34728])).

cnf(c_34731,plain,
    ( v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34729])).

cnf(c_65,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(sK15(X0,X1),X1) ),
    inference(cnf_transformation,[],[f817])).

cnf(c_34744,plain,
    ( ~ r2_xboole_0(X0,k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(resolution,[status(thm)],[c_34710,c_65])).

cnf(c_34746,plain,
    ( ~ r2_xboole_0(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_34744])).

cnf(c_368,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK28(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f1745])).

cnf(c_57074,plain,
    ( r2_hidden(sK28(sK42,sK43,sK4(k2_zfmisc_1(sK42,sK43))),sK42)
    | ~ r2_hidden(sK4(k2_zfmisc_1(sK42,sK43)),k2_zfmisc_1(sK42,sK43)) ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_61573,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
    | v1_xboole_0(k2_zfmisc_1(sK42,sK43))
    | k2_zfmisc_1(sK42,sK43) != k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_31834])).

cnf(c_61576,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK42,sK43))
    | ~ v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | k2_zfmisc_1(sK42,sK43) != k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_61573])).

cnf(c_442,plain,
    ( X0 = X1
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X0)) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1609])).

cnf(c_33072,plain,
    ( k2_zfmisc_1(sK42,sK43) = X0
    | k4_xboole_0(k1_tarski(X0),k1_tarski(k2_zfmisc_1(sK42,sK43))) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_62651,plain,
    ( k2_zfmisc_1(sK42,sK43) = k2_zfmisc_1(sK42,sK43)
    | k4_xboole_0(k1_tarski(k2_zfmisc_1(sK42,sK43)),k1_tarski(k2_zfmisc_1(sK42,sK43))) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_33072])).

cnf(c_514,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k1_tarski(X0),X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1660])).

cnf(c_19906,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_514])).

cnf(c_62654,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK42,sK43),k1_tarski(k2_zfmisc_1(sK42,sK43)))
    | k4_xboole_0(k1_tarski(k2_zfmisc_1(sK42,sK43)),k1_tarski(k2_zfmisc_1(sK42,sK43))) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19906])).

cnf(c_9562,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_32050,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(o_0_0_xboole_0,k2_zfmisc_1(sK42,sK43))
    | X1 != k2_zfmisc_1(sK42,sK43)
    | X0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9562])).

cnf(c_67792,plain,
    ( r2_xboole_0(X0,k2_zfmisc_1(X1,X2))
    | ~ r2_xboole_0(o_0_0_xboole_0,k2_zfmisc_1(sK42,sK43))
    | X0 != o_0_0_xboole_0
    | k2_zfmisc_1(X1,X2) != k2_zfmisc_1(sK42,sK43) ),
    inference(instantiation,[status(thm)],[c_32050])).

cnf(c_67795,plain,
    ( ~ r2_xboole_0(o_0_0_xboole_0,k2_zfmisc_1(sK42,sK43))
    | r2_xboole_0(o_0_0_xboole_0,k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0) != k2_zfmisc_1(sK42,sK43)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_67792])).

cnf(c_9557,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_33135,plain,
    ( X0 != X1
    | k2_zfmisc_1(sK42,sK43) != X1
    | k2_zfmisc_1(sK42,sK43) = X0 ),
    inference(instantiation,[status(thm)],[c_9557])).

cnf(c_69846,plain,
    ( X0 != k2_zfmisc_1(sK42,sK43)
    | k2_zfmisc_1(sK42,sK43) = X0
    | k2_zfmisc_1(sK42,sK43) != k2_zfmisc_1(sK42,sK43) ),
    inference(instantiation,[status(thm)],[c_33135])).

cnf(c_69847,plain,
    ( k2_zfmisc_1(sK42,sK43) != k2_zfmisc_1(sK42,sK43)
    | k2_zfmisc_1(sK42,sK43) = o_0_0_xboole_0
    | o_0_0_xboole_0 != k2_zfmisc_1(sK42,sK43) ),
    inference(instantiation,[status(thm)],[c_69846])).

cnf(c_82964,plain,
    ( ~ r2_hidden(k4_tarski(sK40(X0,X1,sK42,sK43),sK41(X0,X1,sK42,sK43)),k2_zfmisc_1(X0,X1))
    | ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_83040,plain,
    ( r2_hidden(k4_tarski(sK40(X0,X1,sK42,sK43),sK41(X0,X1,sK42,sK43)),k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_82964])).

cnf(c_83042,plain,
    ( r2_hidden(k4_tarski(sK40(o_0_0_xboole_0,o_0_0_xboole_0,sK42,sK43),sK41(o_0_0_xboole_0,o_0_0_xboole_0,sK42,sK43)),k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_83040])).

cnf(c_55,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f810])).

cnf(c_88765,plain,
    ( ~ r1_xboole_0(X0,k2_zfmisc_1(sK42,sK43))
    | ~ r2_hidden(k4_tarski(sK40(X1,X2,sK42,sK43),sK41(X1,X2,sK42,sK43)),X0)
    | ~ r2_hidden(k4_tarski(sK40(X1,X2,sK42,sK43),sK41(X1,X2,sK42,sK43)),k2_zfmisc_1(sK42,sK43)) ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_88766,plain,
    ( r1_xboole_0(X0,k2_zfmisc_1(sK42,sK43)) != iProver_top
    | r2_hidden(k4_tarski(sK40(X1,X2,sK42,sK43),sK41(X1,X2,sK42,sK43)),X0) != iProver_top
    | r2_hidden(k4_tarski(sK40(X1,X2,sK42,sK43),sK41(X1,X2,sK42,sK43)),k2_zfmisc_1(sK42,sK43)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_88765])).

cnf(c_88768,plain,
    ( r1_xboole_0(o_0_0_xboole_0,k2_zfmisc_1(sK42,sK43)) != iProver_top
    | r2_hidden(k4_tarski(sK40(o_0_0_xboole_0,o_0_0_xboole_0,sK42,sK43),sK41(o_0_0_xboole_0,o_0_0_xboole_0,sK42,sK43)),k2_zfmisc_1(sK42,sK43)) != iProver_top
    | r2_hidden(k4_tarski(sK40(o_0_0_xboole_0,o_0_0_xboole_0,sK42,sK43),sK41(o_0_0_xboole_0,o_0_0_xboole_0,sK42,sK43)),o_0_0_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_88766])).

cnf(c_145044,plain,
    ( ~ r2_hidden(sK28(sK42,sK43,sK4(k2_zfmisc_1(sK42,sK43))),sK42)
    | ~ v1_xboole_0(sK42) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_120576,plain,
    ( X0 != k2_zfmisc_1(sK42,sK43)
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = sK42
    | o_0_0_xboole_0 = sK43 ),
    inference(resolution,[status(thm)],[c_9557,c_431])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f822])).

cnf(c_121308,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK42,sK43))
    | ~ r1_tarski(k2_zfmisc_1(sK42,sK43),X0)
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = sK42
    | o_0_0_xboole_0 = sK43 ),
    inference(resolution,[status(thm)],[c_120576,c_67])).

cnf(c_441,plain,
    ( k4_xboole_0(k1_tarski(X0),k1_tarski(X0)) != k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1757])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1406])).

cnf(c_145,plain,
    ( k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1414])).

cnf(c_16648,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_132,c_145])).

cnf(c_16658,plain,
    ( k1_tarski(X0) != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_441,c_16648])).

cnf(c_484,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) != k1_tarski(X2)
    | k1_tarski(X2) = X0
    | k1_tarski(X2) = X1 ),
    inference(cnf_transformation,[],[f1639])).

cnf(c_211,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f966])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f758])).

cnf(c_9361,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) != k1_tarski(X2)
    | k1_tarski(X2) = X0
    | k1_tarski(X2) = X1 ),
    inference(theory_normalisation,[status(thm)],[c_484,c_211,c_7])).

cnf(c_20716,plain,
    ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(o_0_0_xboole_0,k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),o_0_0_xboole_0)))) != k1_tarski(X0)
    | k1_tarski(X0) = k1_tarski(X0)
    | k1_tarski(X0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9361])).

cnf(c_118,plain,
    ( k5_xboole_0(k5_xboole_0(X0,o_0_0_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f1393])).

cnf(c_9526,plain,
    ( k5_xboole_0(X0,k5_xboole_0(o_0_0_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,o_0_0_xboole_0)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_118,c_211,c_7])).

cnf(c_20717,plain,
    ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(o_0_0_xboole_0,k4_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X0),o_0_0_xboole_0)))) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_9526])).

cnf(c_33,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f788])).

cnf(c_33093,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK42,sK43))
    | r2_xboole_0(X0,k2_zfmisc_1(sK42,sK43))
    | k2_zfmisc_1(sK42,sK43) = X0 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_9561,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_20480,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_tarski(X2))
    | X0 != X2
    | X1 != k1_tarski(X2) ),
    inference(instantiation,[status(thm)],[c_9561])).

cnf(c_27344,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(X1,k1_tarski(X0))
    | X1 != X0
    | k1_tarski(X0) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_20480])).

cnf(c_53789,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(k2_zfmisc_1(sK42,sK43),k1_tarski(X0))
    | k2_zfmisc_1(sK42,sK43) != X0
    | k1_tarski(X0) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_27344])).

cnf(c_463,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f1230])).

cnf(c_517,plain,
    ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f1283])).

cnf(c_31377,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_463,c_517])).

cnf(c_121309,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK42,sK43),k1_tarski(X0))
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = sK42
    | o_0_0_xboole_0 = sK43 ),
    inference(resolution,[status(thm)],[c_120576,c_31377])).

cnf(c_121307,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK42,sK43),X0)
    | r2_xboole_0(k2_zfmisc_1(sK42,sK43),X0)
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = sK42
    | o_0_0_xboole_0 = sK43 ),
    inference(resolution,[status(thm)],[c_120576,c_33])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK5(X0,X1),X0) ),
    inference(cnf_transformation,[],[f763])).

cnf(c_33238,plain,
    ( r1_tarski(k2_zfmisc_1(sK42,sK43),X0)
    | r2_hidden(sK5(k2_zfmisc_1(sK42,sK43),X0),k2_zfmisc_1(sK42,sK43)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_63075,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK42,sK43),X0),k2_zfmisc_1(sK42,sK43))
    | ~ v1_xboole_0(k2_zfmisc_1(sK42,sK43)) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_127450,plain,
    ( r2_xboole_0(k2_zfmisc_1(sK42,sK43),X0)
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = sK42
    | o_0_0_xboole_0 = sK43 ),
    inference(global_propositional_subsumption,[status(thm)],[c_121307,c_431,c_1127,c_1151,c_1167,c_177,c_31836,c_32066,c_33238,c_62651,c_62654,c_63075,c_69847])).

cnf(c_165,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f920])).

cnf(c_128559,plain,
    ( ~ r2_xboole_0(X0,k2_zfmisc_1(sK42,sK43))
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = sK42
    | o_0_0_xboole_0 = sK43 ),
    inference(resolution,[status(thm)],[c_127450,c_165])).

cnf(c_128572,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(sK42,sK43))
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = sK42
    | o_0_0_xboole_0 = sK43 ),
    inference(global_propositional_subsumption,[status(thm)],[c_121308,c_231,c_16658,c_20716,c_20717,c_33093,c_53789,c_121309,c_128559])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f762])).

cnf(c_181,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1441])).

cnf(c_429,negated_conjecture,
    ( o_0_0_xboole_0 != k2_zfmisc_1(sK42,sK43)
    | o_0_0_xboole_0 != sK43 ),
    inference(cnf_transformation,[],[f1600])).

cnf(c_20061,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK42,sK43))
    | o_0_0_xboole_0 != sK43 ),
    inference(resolution,[status(thm)],[c_181,c_429])).

cnf(c_66,plain,
    ( r2_hidden(sK16(X0),X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f1358])).

cnf(c_36056,plain,
    ( r2_hidden(sK16(sK43),sK43)
    | ~ v1_xboole_0(k2_zfmisc_1(sK42,sK43)) ),
    inference(resolution,[status(thm)],[c_20061,c_66])).

cnf(c_55662,plain,
    ( ~ r1_tarski(sK43,X0)
    | r2_hidden(sK16(sK43),X0)
    | ~ v1_xboole_0(k2_zfmisc_1(sK42,sK43)) ),
    inference(resolution,[status(thm)],[c_12,c_36056])).

cnf(c_360,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f1740])).

cnf(c_56568,plain,
    ( r1_tarski(sK16(sK43),X0)
    | ~ r1_tarski(sK43,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(k2_zfmisc_1(sK42,sK43)) ),
    inference(resolution,[status(thm)],[c_55662,c_360])).

cnf(c_128624,plain,
    ( ~ r1_tarski(sK43,k1_zfmisc_1(k2_zfmisc_1(sK42,sK43)))
    | ~ v1_xboole_0(k2_zfmisc_1(sK42,sK43))
    | o_0_0_xboole_0 = sK16(sK43)
    | o_0_0_xboole_0 = sK42
    | o_0_0_xboole_0 = sK43 ),
    inference(resolution,[status(thm)],[c_128572,c_56568])).

cnf(c_20086,plain,
    ( sK43 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK43 ),
    inference(instantiation,[status(thm)],[c_9557])).

cnf(c_20087,plain,
    ( sK43 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK43
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20086])).

cnf(c_20088,plain,
    ( sK42 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK42 ),
    inference(instantiation,[status(thm)],[c_9557])).

cnf(c_20089,plain,
    ( sK42 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK42
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20088])).

cnf(c_16544,plain,
    ( o_0_0_xboole_0 = X0
    | r2_hidden(sK16(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66])).

cnf(c_49262,plain,
    ( sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r2_hidden(X0,sK43) != iProver_top ),
    inference(superposition,[status(thm)],[c_16544,c_49257])).

cnf(c_148248,plain,
    ( sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_16544,c_49262])).

cnf(c_148555,plain,
    ( o_0_0_xboole_0 = sK42
    | o_0_0_xboole_0 = sK43 ),
    inference(global_propositional_subsumption,[status(thm)],[c_128624,c_620,c_624,c_692,c_695,c_20087,c_20089,c_148248])).

cnf(c_430,negated_conjecture,
    ( o_0_0_xboole_0 != k2_zfmisc_1(sK42,sK43)
    | o_0_0_xboole_0 != sK42 ),
    inference(cnf_transformation,[],[f1601])).

cnf(c_20062,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK42,sK43))
    | o_0_0_xboole_0 != sK42 ),
    inference(resolution,[status(thm)],[c_181,c_430])).

cnf(c_148565,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK42,sK43))
    | o_0_0_xboole_0 = sK43 ),
    inference(resolution,[status(thm)],[c_148555,c_20062])).

cnf(c_148570,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK42,sK43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_148565,c_20061])).

cnf(c_158782,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK42)
    | sK42 != X0 ),
    inference(instantiation,[status(thm)],[c_9563])).

cnf(c_158784,plain,
    ( v1_xboole_0(sK42)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | sK42 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_158782])).

cnf(c_159005,plain,
    ( sK43 = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_49266,c_1127,c_1151,c_1167,c_177,c_20061,c_31831,c_57074,c_145044,c_148248,c_148565,c_158784])).

cnf(c_416,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X3,X0)
    | r2_hidden(sK37(X1,X2,X3),X2) ),
    inference(cnf_transformation,[],[f1182])).

cnf(c_16338,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(X3,X0) != iProver_top
    | r2_hidden(sK37(X1,X2,X3),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_34011,plain,
    ( sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r1_tarski(X0,o_0_0_xboole_0) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(sK37(sK42,sK43,X1),sK43) = iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_16338])).

cnf(c_35165,plain,
    ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(sK43,sK42)
    | sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r1_tarski(k2_zfmisc_1(X0,X1),o_0_0_xboole_0) != iProver_top
    | r2_hidden(sK37(sK42,sK43,k4_tarski(sK40(X0,X1,sK43,sK42),sK41(X0,X1,sK43,sK42))),sK43) = iProver_top ),
    inference(superposition,[status(thm)],[c_28584,c_34011])).

cnf(c_16594,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_195])).

cnf(c_102070,plain,
    ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(sK43,sK42)
    | sK42 = o_0_0_xboole_0
    | sK43 = o_0_0_xboole_0
    | r1_tarski(k2_zfmisc_1(X0,X1),o_0_0_xboole_0) != iProver_top
    | v1_xboole_0(sK43) != iProver_top ),
    inference(superposition,[status(thm)],[c_35165,c_16594])).

cnf(c_20400,plain,
    ( r2_hidden(sK16(k2_zfmisc_1(sK42,sK43)),k2_zfmisc_1(sK42,sK43))
    | o_0_0_xboole_0 != sK43 ),
    inference(resolution,[status(thm)],[c_66,c_429])).

cnf(c_34757,plain,
    ( ~ v1_xboole_0(sK43)
    | o_0_0_xboole_0 != sK43 ),
    inference(resolution,[status(thm)],[c_34710,c_20400])).

cnf(c_19532,plain,
    ( ~ v1_xboole_0(sK43)
    | o_0_0_xboole_0 = sK43 ),
    inference(instantiation,[status(thm)],[c_181])).

cnf(c_35474,plain,
    ( ~ v1_xboole_0(sK43) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34757,c_19532])).

cnf(c_35476,plain,
    ( v1_xboole_0(sK43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35474])).

cnf(c_156535,plain,
    ( v1_xboole_0(sK43) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_102070,c_35476])).

cnf(c_159008,plain,
    ( v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_159005,c_156535])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_159008,c_177,c_1168,c_1152,c_1128,c_1118,c_1114])).

%------------------------------------------------------------------------------
