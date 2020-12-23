%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:10 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  134 (1302 expanded)
%              Number of clauses        :   97 ( 440 expanded)
%              Number of leaves         :   10 ( 245 expanded)
%              Depth                    :   37
%              Number of atoms          :  384 (4781 expanded)
%              Number of equality atoms :  212 (1304 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f9])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_tarski(X1,X2)
          & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
            | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X1,X2)
      & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 )
   => ( ~ r1_tarski(sK2,sK3)
      & ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3))
        | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) )
      & k1_xboole_0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r1_tarski(sK2,sK3)
    & ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3))
      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) )
    & k1_xboole_0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f8,f19])).

fof(f34,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3))
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f32])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f31])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_395,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_398,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3))
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_390,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_394,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_397,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1258,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X4) = iProver_top
    | r1_tarski(k2_zfmisc_1(X3,X1),X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_394,c_397])).

cnf(c_1457,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK3)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_390,c_1258])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_393,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2108,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(X1,sK3) = iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1457,c_393])).

cnf(c_2353,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
    | r1_tarski(sK1,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_398,c_2108])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_396,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3412,plain,
    ( k2_zfmisc_1(sK3,sK1) = k2_zfmisc_1(sK2,sK1)
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK3,sK1),k2_zfmisc_1(sK2,sK1)) != iProver_top
    | r1_tarski(sK1,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2353,c_396])).

cnf(c_196,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_195,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1957,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(X3,k2_zfmisc_1(X4,X5))
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    inference(resolution,[status(thm)],[c_196,c_195])).

cnf(c_605,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK1,sK3))
    | ~ r2_hidden(X0,k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) ),
    inference(resolution,[status(thm)],[c_2,c_13])).

cnf(c_10937,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | ~ r2_hidden(X3,k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1))
    | X0 != X3
    | X1 != sK1
    | X2 != sK3 ),
    inference(resolution,[status(thm)],[c_1957,c_605])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1256,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_394])).

cnf(c_1290,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k4_tarski(sK0(X1,X2),X0),k1_xboole_0) = iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_398,c_1256])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_815,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_393])).

cnf(c_1854,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_tarski(X2,X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_815])).

cnf(c_2070,plain,
    ( r2_hidden(sK0(k1_xboole_0,X0),X1) = iProver_top
    | r1_tarski(X2,X3) = iProver_top
    | r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_398,c_1854])).

cnf(c_3908,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
    | r1_tarski(k1_xboole_0,X3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2070,c_2108])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_17,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_18,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_193,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_507,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_508,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_399,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3900,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k1_xboole_0,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2070,c_399])).

cnf(c_3973,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3900,c_396])).

cnf(c_4242,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2353,c_3973])).

cnf(c_4435,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
    | r1_tarski(X1,X2) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3908,c_14,c_17,c_18,c_508,c_4242])).

cnf(c_4436,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4435])).

cnf(c_4450,plain,
    ( r2_hidden(sK0(X0,sK3),sK2) != iProver_top
    | r1_tarski(X1,X2) = iProver_top
    | r1_tarski(X0,sK3) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4436,c_399])).

cnf(c_11229,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_398,c_4450])).

cnf(c_3414,plain,
    ( r2_hidden(sK0(X0,sK3),sK2) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
    | r1_tarski(sK1,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2353,c_399])).

cnf(c_9766,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
    | r1_tarski(sK1,X0) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_398,c_3414])).

cnf(c_832,plain,
    ( r2_hidden(X0,sK3)
    | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK1,sK2))
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) ),
    inference(resolution,[status(thm)],[c_7,c_605])).

cnf(c_1064,plain,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(X1,sK3)
    | ~ r2_hidden(X1,sK2)
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) ),
    inference(resolution,[status(thm)],[c_832,c_6])).

cnf(c_1079,plain,
    ( r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK2)
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1))
    | r1_tarski(sK1,X1) ),
    inference(resolution,[status(thm)],[c_1064,c_1])).

cnf(c_1513,plain,
    ( ~ r2_hidden(sK0(X0,sK3),sK2)
    | r1_tarski(X0,sK3)
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1))
    | r1_tarski(sK1,X1) ),
    inference(resolution,[status(thm)],[c_1079,c_0])).

cnf(c_3634,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1))
    | r1_tarski(sK1,X0)
    | r1_tarski(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_1513,c_1])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_6840,plain,
    ( r1_tarski(sK1,X0)
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3634,c_12])).

cnf(c_6841,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1))
    | r1_tarski(sK1,X0) ),
    inference(renaming,[status(thm)],[c_6840])).

cnf(c_6842,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6841])).

cnf(c_9805,plain,
    ( r1_tarski(sK1,X0) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9766,c_6842])).

cnf(c_9806,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_9805])).

cnf(c_9814,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9806,c_3973])).

cnf(c_11268,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11229,c_14,c_17,c_18,c_508,c_9814])).

cnf(c_11269,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_11268])).

cnf(c_11294,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_11269])).

cnf(c_11296,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11294])).

cnf(c_11301,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11296])).

cnf(c_11303,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10937,c_11301])).

cnf(c_11315,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK3,sK1))
    | ~ r2_hidden(X0,k2_zfmisc_1(sK2,sK1)) ),
    inference(resolution,[status(thm)],[c_11303,c_2])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_11335,plain,
    ( r2_hidden(X0,sK3)
    | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK1)) ),
    inference(resolution,[status(thm)],[c_11315,c_8])).

cnf(c_13814,plain,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(X1,sK3)
    | ~ r2_hidden(X1,sK2) ),
    inference(resolution,[status(thm)],[c_11335,c_6])).

cnf(c_16382,plain,
    ( r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK2)
    | r1_tarski(sK1,X1) ),
    inference(resolution,[status(thm)],[c_13814,c_1])).

cnf(c_16383,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(sK1,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16382])).

cnf(c_18959,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r1_tarski(sK1,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3412,c_16383])).

cnf(c_18960,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(sK1,X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_18959])).

cnf(c_18966,plain,
    ( r2_hidden(sK0(sK2,X0),sK3) = iProver_top
    | r1_tarski(sK1,X1) = iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_398,c_18960])).

cnf(c_19236,plain,
    ( r1_tarski(sK1,X0) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_18966,c_399])).

cnf(c_16,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_19412,plain,
    ( r1_tarski(sK1,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19236,c_16])).

cnf(c_19419,plain,
    ( sK1 = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_19412,c_396])).

cnf(c_504,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_505,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_539,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0)
    | r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_540,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_623,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK1),X0)
    | ~ r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_624,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK1),X0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_2261,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,sK1),sK1)
    | r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2264,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK1),sK1) != iProver_top
    | r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2261])).

cnf(c_3978,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3900])).

cnf(c_3980,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3978])).

cnf(c_2269,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,sK1),X0)
    | r2_hidden(sK0(k1_xboole_0,sK1),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_17310,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,sK1),X0)
    | r2_hidden(sK0(k1_xboole_0,sK1),sK1)
    | ~ r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_2269])).

cnf(c_17311,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK1),X0) != iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK1),sK1) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17310])).

cnf(c_19396,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_19236])).

cnf(c_19507,plain,
    ( r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19419,c_14,c_16,c_505,c_540,c_624,c_2264,c_3980,c_17311,c_19396])).

cnf(c_19512,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_395,c_19507])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:16:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.98/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.01  
% 3.98/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.98/1.01  
% 3.98/1.01  ------  iProver source info
% 3.98/1.01  
% 3.98/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.98/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.98/1.01  git: non_committed_changes: false
% 3.98/1.01  git: last_make_outside_of_git: false
% 3.98/1.01  
% 3.98/1.01  ------ 
% 3.98/1.01  ------ Parsing...
% 3.98/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.98/1.01  
% 3.98/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.98/1.01  
% 3.98/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.98/1.01  
% 3.98/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.98/1.01  ------ Proving...
% 3.98/1.01  ------ Problem Properties 
% 3.98/1.01  
% 3.98/1.01  
% 3.98/1.01  clauses                                 14
% 3.98/1.01  conjectures                             3
% 3.98/1.01  EPR                                     5
% 3.98/1.01  Horn                                    11
% 3.98/1.01  unary                                   5
% 3.98/1.01  binary                                  5
% 3.98/1.01  lits                                    27
% 3.98/1.01  lits eq                                 7
% 3.98/1.01  fd_pure                                 0
% 3.98/1.01  fd_pseudo                               0
% 3.98/1.01  fd_cond                                 1
% 3.98/1.01  fd_pseudo_cond                          1
% 3.98/1.01  AC symbols                              0
% 3.98/1.01  
% 3.98/1.01  ------ Input Options Time Limit: Unbounded
% 3.98/1.01  
% 3.98/1.01  
% 3.98/1.01  ------ 
% 3.98/1.01  Current options:
% 3.98/1.01  ------ 
% 3.98/1.01  
% 3.98/1.01  
% 3.98/1.01  
% 3.98/1.01  
% 3.98/1.01  ------ Proving...
% 3.98/1.01  
% 3.98/1.01  
% 3.98/1.01  % SZS status Theorem for theBenchmark.p
% 3.98/1.01  
% 3.98/1.01   Resolution empty clause
% 3.98/1.01  
% 3.98/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.98/1.01  
% 3.98/1.01  fof(f2,axiom,(
% 3.98/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.01  
% 3.98/1.01  fof(f13,plain,(
% 3.98/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.98/1.01    inference(nnf_transformation,[],[f2])).
% 3.98/1.01  
% 3.98/1.01  fof(f14,plain,(
% 3.98/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.98/1.01    inference(flattening,[],[f13])).
% 3.98/1.01  
% 3.98/1.01  fof(f24,plain,(
% 3.98/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.98/1.01    inference(cnf_transformation,[],[f14])).
% 3.98/1.01  
% 3.98/1.01  fof(f37,plain,(
% 3.98/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.98/1.01    inference(equality_resolution,[],[f24])).
% 3.98/1.01  
% 3.98/1.01  fof(f1,axiom,(
% 3.98/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.01  
% 3.98/1.01  fof(f7,plain,(
% 3.98/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.98/1.01    inference(ennf_transformation,[],[f1])).
% 3.98/1.01  
% 3.98/1.01  fof(f9,plain,(
% 3.98/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.98/1.01    inference(nnf_transformation,[],[f7])).
% 3.98/1.01  
% 3.98/1.01  fof(f10,plain,(
% 3.98/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.98/1.01    inference(rectify,[],[f9])).
% 3.98/1.01  
% 3.98/1.01  fof(f11,plain,(
% 3.98/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.98/1.01    introduced(choice_axiom,[])).
% 3.98/1.01  
% 3.98/1.01  fof(f12,plain,(
% 3.98/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f11])).
% 3.98/1.01  
% 3.98/1.01  fof(f22,plain,(
% 3.98/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.98/1.01    inference(cnf_transformation,[],[f12])).
% 3.98/1.01  
% 3.98/1.01  fof(f5,conjecture,(
% 3.98/1.01    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 3.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.01  
% 3.98/1.01  fof(f6,negated_conjecture,(
% 3.98/1.01    ~! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 3.98/1.01    inference(negated_conjecture,[],[f5])).
% 3.98/1.01  
% 3.98/1.01  fof(f8,plain,(
% 3.98/1.01    ? [X0,X1,X2] : (~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 3.98/1.01    inference(ennf_transformation,[],[f6])).
% 3.98/1.01  
% 3.98/1.01  fof(f19,plain,(
% 3.98/1.01    ? [X0,X1,X2] : (~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0) => (~r1_tarski(sK2,sK3) & (r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3)) | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1))) & k1_xboole_0 != sK1)),
% 3.98/1.01    introduced(choice_axiom,[])).
% 3.98/1.01  
% 3.98/1.01  fof(f20,plain,(
% 3.98/1.01    ~r1_tarski(sK2,sK3) & (r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3)) | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1))) & k1_xboole_0 != sK1),
% 3.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f8,f19])).
% 3.98/1.01  
% 3.98/1.01  fof(f34,plain,(
% 3.98/1.01    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3)) | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1))),
% 3.98/1.01    inference(cnf_transformation,[],[f20])).
% 3.98/1.01  
% 3.98/1.01  fof(f3,axiom,(
% 3.98/1.01    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.01  
% 3.98/1.01  fof(f15,plain,(
% 3.98/1.01    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.98/1.01    inference(nnf_transformation,[],[f3])).
% 3.98/1.01  
% 3.98/1.01  fof(f16,plain,(
% 3.98/1.01    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.98/1.01    inference(flattening,[],[f15])).
% 3.98/1.01  
% 3.98/1.01  fof(f29,plain,(
% 3.98/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 3.98/1.01    inference(cnf_transformation,[],[f16])).
% 3.98/1.01  
% 3.98/1.01  fof(f21,plain,(
% 3.98/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.98/1.01    inference(cnf_transformation,[],[f12])).
% 3.98/1.01  
% 3.98/1.01  fof(f28,plain,(
% 3.98/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.98/1.01    inference(cnf_transformation,[],[f16])).
% 3.98/1.01  
% 3.98/1.01  fof(f26,plain,(
% 3.98/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.98/1.01    inference(cnf_transformation,[],[f14])).
% 3.98/1.01  
% 3.98/1.01  fof(f4,axiom,(
% 3.98/1.01    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.98/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.98/1.01  
% 3.98/1.01  fof(f17,plain,(
% 3.98/1.01    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.98/1.01    inference(nnf_transformation,[],[f4])).
% 3.98/1.01  
% 3.98/1.01  fof(f18,plain,(
% 3.98/1.01    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.98/1.01    inference(flattening,[],[f17])).
% 3.98/1.01  
% 3.98/1.01  fof(f32,plain,(
% 3.98/1.01    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.98/1.01    inference(cnf_transformation,[],[f18])).
% 3.98/1.01  
% 3.98/1.01  fof(f38,plain,(
% 3.98/1.01    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.98/1.01    inference(equality_resolution,[],[f32])).
% 3.98/1.01  
% 3.98/1.01  fof(f31,plain,(
% 3.98/1.01    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.98/1.01    inference(cnf_transformation,[],[f18])).
% 3.98/1.01  
% 3.98/1.01  fof(f39,plain,(
% 3.98/1.01    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.98/1.01    inference(equality_resolution,[],[f31])).
% 3.98/1.01  
% 3.98/1.01  fof(f33,plain,(
% 3.98/1.01    k1_xboole_0 != sK1),
% 3.98/1.01    inference(cnf_transformation,[],[f20])).
% 3.98/1.01  
% 3.98/1.01  fof(f30,plain,(
% 3.98/1.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 3.98/1.01    inference(cnf_transformation,[],[f18])).
% 3.98/1.01  
% 3.98/1.01  fof(f23,plain,(
% 3.98/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.98/1.01    inference(cnf_transformation,[],[f12])).
% 3.98/1.01  
% 3.98/1.01  fof(f35,plain,(
% 3.98/1.01    ~r1_tarski(sK2,sK3)),
% 3.98/1.01    inference(cnf_transformation,[],[f20])).
% 3.98/1.01  
% 3.98/1.01  fof(f27,plain,(
% 3.98/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.98/1.01    inference(cnf_transformation,[],[f16])).
% 3.98/1.01  
% 3.98/1.01  cnf(c_5,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f37]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_395,plain,
% 3.98/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1,plain,
% 3.98/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.98/1.01      inference(cnf_transformation,[],[f22]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_398,plain,
% 3.98/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.98/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_13,negated_conjecture,
% 3.98/1.01      ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3))
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) ),
% 3.98/1.01      inference(cnf_transformation,[],[f34]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_390,plain,
% 3.98/1.01      ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3)) = iProver_top
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_6,plain,
% 3.98/1.01      ( ~ r2_hidden(X0,X1)
% 3.98/1.01      | ~ r2_hidden(X2,X3)
% 3.98/1.01      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.98/1.01      inference(cnf_transformation,[],[f29]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_394,plain,
% 3.98/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.98/1.01      | r2_hidden(X2,X3) != iProver_top
% 3.98/1.01      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_2,plain,
% 3.98/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.98/1.01      inference(cnf_transformation,[],[f21]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_397,plain,
% 3.98/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.98/1.01      | r2_hidden(X0,X2) = iProver_top
% 3.98/1.01      | r1_tarski(X1,X2) != iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1258,plain,
% 3.98/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.98/1.01      | r2_hidden(X2,X3) != iProver_top
% 3.98/1.01      | r2_hidden(k4_tarski(X2,X0),X4) = iProver_top
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(X3,X1),X4) != iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_394,c_397]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1457,plain,
% 3.98/1.01      ( r2_hidden(X0,sK1) != iProver_top
% 3.98/1.01      | r2_hidden(X1,sK2) != iProver_top
% 3.98/1.01      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK1,sK3)) = iProver_top
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_390,c_1258]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_7,plain,
% 3.98/1.01      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.98/1.01      inference(cnf_transformation,[],[f28]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_393,plain,
% 3.98/1.01      ( r2_hidden(X0,X1) = iProver_top
% 3.98/1.01      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_2108,plain,
% 3.98/1.01      ( r2_hidden(X0,sK1) != iProver_top
% 3.98/1.01      | r2_hidden(X1,sK3) = iProver_top
% 3.98/1.01      | r2_hidden(X1,sK2) != iProver_top
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_1457,c_393]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_2353,plain,
% 3.98/1.01      ( r2_hidden(X0,sK3) = iProver_top
% 3.98/1.01      | r2_hidden(X0,sK2) != iProver_top
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
% 3.98/1.01      | r1_tarski(sK1,X1) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_398,c_2108]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_3,plain,
% 3.98/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.98/1.01      inference(cnf_transformation,[],[f26]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_396,plain,
% 3.98/1.01      ( X0 = X1
% 3.98/1.01      | r1_tarski(X1,X0) != iProver_top
% 3.98/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_3412,plain,
% 3.98/1.01      ( k2_zfmisc_1(sK3,sK1) = k2_zfmisc_1(sK2,sK1)
% 3.98/1.01      | r2_hidden(X0,sK3) = iProver_top
% 3.98/1.01      | r2_hidden(X0,sK2) != iProver_top
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK3,sK1),k2_zfmisc_1(sK2,sK1)) != iProver_top
% 3.98/1.01      | r1_tarski(sK1,X1) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_2353,c_396]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_196,plain,
% 3.98/1.01      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 3.98/1.01      theory(equality) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_195,plain,
% 3.98/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.98/1.01      theory(equality) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1957,plain,
% 3.98/1.01      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.98/1.01      | r2_hidden(X3,k2_zfmisc_1(X4,X5))
% 3.98/1.01      | X3 != X0
% 3.98/1.01      | X4 != X1
% 3.98/1.01      | X5 != X2 ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_196,c_195]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_605,plain,
% 3.98/1.01      ( r2_hidden(X0,k2_zfmisc_1(sK1,sK3))
% 3.98/1.01      | ~ r2_hidden(X0,k2_zfmisc_1(sK1,sK2))
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_2,c_13]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_10937,plain,
% 3.98/1.01      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.98/1.01      | ~ r2_hidden(X3,k2_zfmisc_1(sK1,sK2))
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1))
% 3.98/1.01      | X0 != X3
% 3.98/1.01      | X1 != sK1
% 3.98/1.01      | X2 != sK3 ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_1957,c_605]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_9,plain,
% 3.98/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.98/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1256,plain,
% 3.98/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.98/1.01      | r2_hidden(X2,k1_xboole_0) != iProver_top
% 3.98/1.01      | r2_hidden(k4_tarski(X0,X2),k1_xboole_0) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_9,c_394]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1290,plain,
% 3.98/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.98/1.01      | r2_hidden(k4_tarski(sK0(X1,X2),X0),k1_xboole_0) = iProver_top
% 3.98/1.01      | r1_tarski(X1,X2) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_398,c_1256]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_10,plain,
% 3.98/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.98/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_815,plain,
% 3.98/1.01      ( r2_hidden(X0,X1) = iProver_top
% 3.98/1.01      | r2_hidden(k4_tarski(X2,X0),k1_xboole_0) != iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_10,c_393]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1854,plain,
% 3.98/1.01      ( r2_hidden(X0,X1) = iProver_top
% 3.98/1.01      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.98/1.01      | r1_tarski(X2,X3) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_1290,c_815]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_2070,plain,
% 3.98/1.01      ( r2_hidden(sK0(k1_xboole_0,X0),X1) = iProver_top
% 3.98/1.01      | r1_tarski(X2,X3) = iProver_top
% 3.98/1.01      | r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_398,c_1854]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_3908,plain,
% 3.98/1.01      ( r2_hidden(X0,sK3) = iProver_top
% 3.98/1.01      | r2_hidden(X0,sK2) != iProver_top
% 3.98/1.01      | r1_tarski(X1,X2) = iProver_top
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
% 3.98/1.01      | r1_tarski(k1_xboole_0,X3) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_2070,c_2108]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_14,negated_conjecture,
% 3.98/1.01      ( k1_xboole_0 != sK1 ),
% 3.98/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_11,plain,
% 3.98/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.98/1.01      | k1_xboole_0 = X1
% 3.98/1.01      | k1_xboole_0 = X0 ),
% 3.98/1.01      inference(cnf_transformation,[],[f30]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_17,plain,
% 3.98/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.98/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 3.98/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_18,plain,
% 3.98/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.98/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_193,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_507,plain,
% 3.98/1.01      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.98/1.01      inference(instantiation,[status(thm)],[c_193]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_508,plain,
% 3.98/1.01      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 3.98/1.01      inference(instantiation,[status(thm)],[c_507]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_0,plain,
% 3.98/1.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.98/1.01      inference(cnf_transformation,[],[f23]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_399,plain,
% 3.98/1.01      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.98/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_3900,plain,
% 3.98/1.01      ( r1_tarski(X0,X1) = iProver_top
% 3.98/1.01      | r1_tarski(k1_xboole_0,X2) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_2070,c_399]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_3973,plain,
% 3.98/1.01      ( k1_xboole_0 = X0
% 3.98/1.01      | r1_tarski(X1,X2) = iProver_top
% 3.98/1.01      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_3900,c_396]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_4242,plain,
% 3.98/1.01      ( sK1 = k1_xboole_0
% 3.98/1.01      | r2_hidden(X0,sK3) = iProver_top
% 3.98/1.01      | r2_hidden(X0,sK2) != iProver_top
% 3.98/1.01      | r1_tarski(X1,X2) = iProver_top
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_2353,c_3973]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_4435,plain,
% 3.98/1.01      ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
% 3.98/1.01      | r1_tarski(X1,X2) = iProver_top
% 3.98/1.01      | r2_hidden(X0,sK2) != iProver_top
% 3.98/1.01      | r2_hidden(X0,sK3) = iProver_top ),
% 3.98/1.01      inference(global_propositional_subsumption,
% 3.98/1.01                [status(thm)],
% 3.98/1.01                [c_3908,c_14,c_17,c_18,c_508,c_4242]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_4436,plain,
% 3.98/1.01      ( r2_hidden(X0,sK3) = iProver_top
% 3.98/1.01      | r2_hidden(X0,sK2) != iProver_top
% 3.98/1.01      | r1_tarski(X1,X2) = iProver_top
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 3.98/1.01      inference(renaming,[status(thm)],[c_4435]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_4450,plain,
% 3.98/1.01      ( r2_hidden(sK0(X0,sK3),sK2) != iProver_top
% 3.98/1.01      | r1_tarski(X1,X2) = iProver_top
% 3.98/1.01      | r1_tarski(X0,sK3) = iProver_top
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_4436,c_399]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_11229,plain,
% 3.98/1.01      ( r1_tarski(X0,X1) = iProver_top
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
% 3.98/1.01      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_398,c_4450]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_3414,plain,
% 3.98/1.01      ( r2_hidden(sK0(X0,sK3),sK2) != iProver_top
% 3.98/1.01      | r1_tarski(X0,sK3) = iProver_top
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
% 3.98/1.01      | r1_tarski(sK1,X1) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_2353,c_399]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_9766,plain,
% 3.98/1.01      ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
% 3.98/1.01      | r1_tarski(sK1,X0) = iProver_top
% 3.98/1.01      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_398,c_3414]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_832,plain,
% 3.98/1.01      ( r2_hidden(X0,sK3)
% 3.98/1.01      | ~ r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK1,sK2))
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_7,c_605]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1064,plain,
% 3.98/1.01      ( ~ r2_hidden(X0,sK1)
% 3.98/1.01      | r2_hidden(X1,sK3)
% 3.98/1.01      | ~ r2_hidden(X1,sK2)
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_832,c_6]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1079,plain,
% 3.98/1.01      ( r2_hidden(X0,sK3)
% 3.98/1.01      | ~ r2_hidden(X0,sK2)
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1))
% 3.98/1.01      | r1_tarski(sK1,X1) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_1064,c_1]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_1513,plain,
% 3.98/1.01      ( ~ r2_hidden(sK0(X0,sK3),sK2)
% 3.98/1.01      | r1_tarski(X0,sK3)
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1))
% 3.98/1.01      | r1_tarski(sK1,X1) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_1079,c_0]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_3634,plain,
% 3.98/1.01      ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1))
% 3.98/1.01      | r1_tarski(sK1,X0)
% 3.98/1.01      | r1_tarski(sK2,sK3) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_1513,c_1]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_12,negated_conjecture,
% 3.98/1.01      ( ~ r1_tarski(sK2,sK3) ),
% 3.98/1.01      inference(cnf_transformation,[],[f35]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_6840,plain,
% 3.98/1.01      ( r1_tarski(sK1,X0)
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) ),
% 3.98/1.01      inference(global_propositional_subsumption,[status(thm)],[c_3634,c_12]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_6841,plain,
% 3.98/1.01      ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1))
% 3.98/1.01      | r1_tarski(sK1,X0) ),
% 3.98/1.01      inference(renaming,[status(thm)],[c_6840]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_6842,plain,
% 3.98/1.01      ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
% 3.98/1.01      | r1_tarski(sK1,X0) = iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_6841]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_9805,plain,
% 3.98/1.01      ( r1_tarski(sK1,X0) = iProver_top
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 3.98/1.01      inference(global_propositional_subsumption,[status(thm)],[c_9766,c_6842]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_9806,plain,
% 3.98/1.01      ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
% 3.98/1.01      | r1_tarski(sK1,X0) = iProver_top ),
% 3.98/1.01      inference(renaming,[status(thm)],[c_9805]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_9814,plain,
% 3.98/1.01      ( sK1 = k1_xboole_0
% 3.98/1.01      | r1_tarski(X0,X1) = iProver_top
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_9806,c_3973]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_11268,plain,
% 3.98/1.01      ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
% 3.98/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.98/1.01      inference(global_propositional_subsumption,
% 3.98/1.01                [status(thm)],
% 3.98/1.01                [c_11229,c_14,c_17,c_18,c_508,c_9814]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_11269,plain,
% 3.98/1.01      ( r1_tarski(X0,X1) = iProver_top
% 3.98/1.01      | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 3.98/1.01      inference(renaming,[status(thm)],[c_11268]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_11294,plain,
% 3.98/1.01      ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top
% 3.98/1.01      | iProver_top != iProver_top ),
% 3.98/1.01      inference(equality_factoring,[status(thm)],[c_11269]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_11296,plain,
% 3.98/1.01      ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 3.98/1.01      inference(equality_resolution_simp,[status(thm)],[c_11294]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_11301,plain,
% 3.98/1.01      ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) ),
% 3.98/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_11296]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_11303,plain,
% 3.98/1.01      ( r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK3,sK1)) ),
% 3.98/1.01      inference(global_propositional_subsumption,
% 3.98/1.01                [status(thm)],
% 3.98/1.01                [c_10937,c_11301]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_11315,plain,
% 3.98/1.01      ( r2_hidden(X0,k2_zfmisc_1(sK3,sK1))
% 3.98/1.01      | ~ r2_hidden(X0,k2_zfmisc_1(sK2,sK1)) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_11303,c_2]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_8,plain,
% 3.98/1.01      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.98/1.01      inference(cnf_transformation,[],[f27]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_11335,plain,
% 3.98/1.01      ( r2_hidden(X0,sK3)
% 3.98/1.01      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK1)) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_11315,c_8]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_13814,plain,
% 3.98/1.01      ( ~ r2_hidden(X0,sK1) | r2_hidden(X1,sK3) | ~ r2_hidden(X1,sK2) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_11335,c_6]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_16382,plain,
% 3.98/1.01      ( r2_hidden(X0,sK3) | ~ r2_hidden(X0,sK2) | r1_tarski(sK1,X1) ),
% 3.98/1.01      inference(resolution,[status(thm)],[c_13814,c_1]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_16383,plain,
% 3.98/1.01      ( r2_hidden(X0,sK3) = iProver_top
% 3.98/1.01      | r2_hidden(X0,sK2) != iProver_top
% 3.98/1.01      | r1_tarski(sK1,X1) = iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_16382]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_18959,plain,
% 3.98/1.01      ( r2_hidden(X0,sK2) != iProver_top
% 3.98/1.01      | r2_hidden(X0,sK3) = iProver_top
% 3.98/1.01      | r1_tarski(sK1,X1) = iProver_top ),
% 3.98/1.01      inference(global_propositional_subsumption,
% 3.98/1.01                [status(thm)],
% 3.98/1.01                [c_3412,c_16383]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_18960,plain,
% 3.98/1.01      ( r2_hidden(X0,sK3) = iProver_top
% 3.98/1.01      | r2_hidden(X0,sK2) != iProver_top
% 3.98/1.01      | r1_tarski(sK1,X1) = iProver_top ),
% 3.98/1.01      inference(renaming,[status(thm)],[c_18959]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_18966,plain,
% 3.98/1.01      ( r2_hidden(sK0(sK2,X0),sK3) = iProver_top
% 3.98/1.01      | r1_tarski(sK1,X1) = iProver_top
% 3.98/1.01      | r1_tarski(sK2,X0) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_398,c_18960]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_19236,plain,
% 3.98/1.01      ( r1_tarski(sK1,X0) = iProver_top | r1_tarski(sK2,sK3) = iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_18966,c_399]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_16,plain,
% 3.98/1.01      ( r1_tarski(sK2,sK3) != iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_19412,plain,
% 3.98/1.01      ( r1_tarski(sK1,X0) = iProver_top ),
% 3.98/1.01      inference(global_propositional_subsumption,[status(thm)],[c_19236,c_16]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_19419,plain,
% 3.98/1.01      ( sK1 = X0 | r1_tarski(X0,sK1) != iProver_top ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_19412,c_396]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_504,plain,
% 3.98/1.01      ( ~ r1_tarski(sK1,k1_xboole_0)
% 3.98/1.01      | ~ r1_tarski(k1_xboole_0,sK1)
% 3.98/1.01      | k1_xboole_0 = sK1 ),
% 3.98/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_505,plain,
% 3.98/1.01      ( k1_xboole_0 = sK1
% 3.98/1.01      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 3.98/1.01      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_539,plain,
% 3.98/1.01      ( r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0)
% 3.98/1.01      | r1_tarski(k1_xboole_0,sK1) ),
% 3.98/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_540,plain,
% 3.98/1.01      ( r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0) = iProver_top
% 3.98/1.01      | r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_623,plain,
% 3.98/1.01      ( r2_hidden(sK0(k1_xboole_0,sK1),X0)
% 3.98/1.01      | ~ r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0)
% 3.98/1.01      | ~ r1_tarski(k1_xboole_0,X0) ),
% 3.98/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_624,plain,
% 3.98/1.01      ( r2_hidden(sK0(k1_xboole_0,sK1),X0) = iProver_top
% 3.98/1.01      | r2_hidden(sK0(k1_xboole_0,sK1),k1_xboole_0) != iProver_top
% 3.98/1.01      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_623]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_2261,plain,
% 3.98/1.01      ( ~ r2_hidden(sK0(k1_xboole_0,sK1),sK1) | r1_tarski(k1_xboole_0,sK1) ),
% 3.98/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_2264,plain,
% 3.98/1.01      ( r2_hidden(sK0(k1_xboole_0,sK1),sK1) != iProver_top
% 3.98/1.01      | r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_2261]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_3978,plain,
% 3.98/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top | iProver_top != iProver_top ),
% 3.98/1.01      inference(equality_factoring,[status(thm)],[c_3900]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_3980,plain,
% 3.98/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.98/1.01      inference(equality_resolution_simp,[status(thm)],[c_3978]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_2269,plain,
% 3.98/1.01      ( ~ r2_hidden(sK0(k1_xboole_0,sK1),X0)
% 3.98/1.01      | r2_hidden(sK0(k1_xboole_0,sK1),X1)
% 3.98/1.01      | ~ r1_tarski(X0,X1) ),
% 3.98/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_17310,plain,
% 3.98/1.01      ( ~ r2_hidden(sK0(k1_xboole_0,sK1),X0)
% 3.98/1.01      | r2_hidden(sK0(k1_xboole_0,sK1),sK1)
% 3.98/1.01      | ~ r1_tarski(X0,sK1) ),
% 3.98/1.01      inference(instantiation,[status(thm)],[c_2269]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_17311,plain,
% 3.98/1.01      ( r2_hidden(sK0(k1_xboole_0,sK1),X0) != iProver_top
% 3.98/1.01      | r2_hidden(sK0(k1_xboole_0,sK1),sK1) = iProver_top
% 3.98/1.01      | r1_tarski(X0,sK1) != iProver_top ),
% 3.98/1.01      inference(predicate_to_equality,[status(thm)],[c_17310]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_19396,plain,
% 3.98/1.01      ( r1_tarski(sK1,k1_xboole_0) = iProver_top
% 3.98/1.01      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.98/1.01      inference(instantiation,[status(thm)],[c_19236]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_19507,plain,
% 3.98/1.01      ( r1_tarski(X0,sK1) != iProver_top ),
% 3.98/1.01      inference(global_propositional_subsumption,
% 3.98/1.01                [status(thm)],
% 3.98/1.01                [c_19419,c_14,c_16,c_505,c_540,c_624,c_2264,c_3980,c_17311,
% 3.98/1.01                 c_19396]) ).
% 3.98/1.01  
% 3.98/1.01  cnf(c_19512,plain,
% 3.98/1.01      ( $false ),
% 3.98/1.01      inference(superposition,[status(thm)],[c_395,c_19507]) ).
% 3.98/1.01  
% 3.98/1.01  
% 3.98/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.98/1.01  
% 3.98/1.01  ------                               Statistics
% 3.98/1.01  
% 3.98/1.01  ------ Selected
% 3.98/1.01  
% 3.98/1.01  total_time:                             0.508
% 3.98/1.01  
%------------------------------------------------------------------------------
