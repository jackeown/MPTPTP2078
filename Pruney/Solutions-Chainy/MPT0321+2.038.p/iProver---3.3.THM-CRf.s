%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:44 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  116 (1301 expanded)
%              Number of clauses        :   70 ( 440 expanded)
%              Number of leaves         :   12 ( 255 expanded)
%              Depth                    :   21
%              Number of atoms          :  316 (4500 expanded)
%              Number of equality atoms :  189 (2224 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f25])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2))) ) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f54,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_tarski(X2,X2))) ),
    inference(equality_resolution,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f12])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK3 != sK5
        | sK2 != sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( sK3 != sK5
      | sK2 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f13,f27])).

fof(f45,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f23])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,
    ( sK3 != sK5
    | sK2 != sK4 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_456,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) = iProver_top
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X0,X0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_449,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_891,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_449])).

cnf(c_1991,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_456,c_891])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_459,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_18,negated_conjecture,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_453,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1971,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_453])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_451,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2047,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1971,c_451])).

cnf(c_2202,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK0(sK4,X1),sK2) = iProver_top
    | r1_tarski(sK4,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_459,c_2047])).

cnf(c_3145,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK0(sK4,X0),sK2) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1991,c_2202])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_37,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_41,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_532,plain,
    ( ~ r1_tarski(sK5,sK3)
    | ~ r1_tarski(sK3,sK5)
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_533,plain,
    ( sK3 = sK5
    | r1_tarski(sK5,sK3) != iProver_top
    | r1_tarski(sK3,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_248,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_500,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_723,plain,
    ( sK3 != sK5
    | k1_xboole_0 != sK5
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_500])).

cnf(c_854,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_855,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_452,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1322,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_452])).

cnf(c_1976,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X1,sK5) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_1322])).

cnf(c_2120,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1991,c_1976])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_524,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_525,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_2262,plain,
    ( r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2120,c_17,c_37,c_41,c_525])).

cnf(c_2268,plain,
    ( r2_hidden(sK0(sK3,X0),sK5) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_459,c_2262])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_460,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2484,plain,
    ( r1_tarski(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2268,c_460])).

cnf(c_1156,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_451])).

cnf(c_1975,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_1156])).

cnf(c_2094,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK1(k1_xboole_0,sK2),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1991,c_1975])).

cnf(c_2419,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK1(k1_xboole_0,sK2),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2094,c_17,c_37,c_41,c_525])).

cnf(c_2425,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK2),sK4) = iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_459,c_2419])).

cnf(c_501,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_500])).

cnf(c_2428,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0,sK2),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1991,c_2419])).

cnf(c_3247,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK2),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2425,c_16,c_37,c_41,c_501,c_2428])).

cnf(c_2046,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK5) != iProver_top
    | r2_hidden(X1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1971,c_452])).

cnf(c_3253,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3247,c_2046])).

cnf(c_3510,plain,
    ( r2_hidden(sK0(sK5,X0),sK3) = iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_459,c_3253])).

cnf(c_3922,plain,
    ( r1_tarski(sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3510,c_460])).

cnf(c_8653,plain,
    ( r2_hidden(sK0(sK4,X0),sK2) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3145,c_16,c_37,c_41,c_533,c_723,c_855,c_2484,c_3922])).

cnf(c_8659,plain,
    ( r1_tarski(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_8653,c_460])).

cnf(c_2271,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0,sK3),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1991,c_2262])).

cnf(c_5130,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK3),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2271,c_16,c_37,c_41,c_501])).

cnf(c_455,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2574,plain,
    ( sK5 = sK3
    | r1_tarski(sK5,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2484,c_455])).

cnf(c_3935,plain,
    ( sK5 = sK3 ),
    inference(superposition,[status(thm)],[c_3922,c_2574])).

cnf(c_5134,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK3),sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5130,c_3935])).

cnf(c_2091,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(sK0(sK2,X1),sK4) = iProver_top
    | r1_tarski(sK2,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_459,c_1975])).

cnf(c_5138,plain,
    ( r2_hidden(sK0(sK2,X0),sK4) = iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5134,c_2091])).

cnf(c_6706,plain,
    ( r1_tarski(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5138,c_460])).

cnf(c_476,plain,
    ( ~ r1_tarski(sK4,sK2)
    | ~ r1_tarski(sK2,sK4)
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_477,plain,
    ( sK2 = sK4
    | r1_tarski(sK4,sK2) != iProver_top
    | r1_tarski(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_15,negated_conjecture,
    ( sK2 != sK4
    | sK3 != sK5 ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8659,c_6706,c_3922,c_2484,c_533,c_477,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:36:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.57/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.00  
% 3.57/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.57/1.00  
% 3.57/1.00  ------  iProver source info
% 3.57/1.00  
% 3.57/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.57/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.57/1.00  git: non_committed_changes: false
% 3.57/1.00  git: last_make_outside_of_git: false
% 3.57/1.00  
% 3.57/1.00  ------ 
% 3.57/1.00  
% 3.57/1.00  ------ Input Options
% 3.57/1.00  
% 3.57/1.00  --out_options                           all
% 3.57/1.00  --tptp_safe_out                         true
% 3.57/1.00  --problem_path                          ""
% 3.57/1.00  --include_path                          ""
% 3.57/1.00  --clausifier                            res/vclausify_rel
% 3.57/1.00  --clausifier_options                    ""
% 3.57/1.00  --stdin                                 false
% 3.57/1.00  --stats_out                             all
% 3.57/1.00  
% 3.57/1.00  ------ General Options
% 3.57/1.00  
% 3.57/1.00  --fof                                   false
% 3.57/1.00  --time_out_real                         305.
% 3.57/1.00  --time_out_virtual                      -1.
% 3.57/1.00  --symbol_type_check                     false
% 3.57/1.00  --clausify_out                          false
% 3.57/1.00  --sig_cnt_out                           false
% 3.57/1.00  --trig_cnt_out                          false
% 3.57/1.00  --trig_cnt_out_tolerance                1.
% 3.57/1.00  --trig_cnt_out_sk_spl                   false
% 3.57/1.00  --abstr_cl_out                          false
% 3.57/1.00  
% 3.57/1.00  ------ Global Options
% 3.57/1.00  
% 3.57/1.00  --schedule                              default
% 3.57/1.00  --add_important_lit                     false
% 3.57/1.00  --prop_solver_per_cl                    1000
% 3.57/1.00  --min_unsat_core                        false
% 3.57/1.00  --soft_assumptions                      false
% 3.57/1.00  --soft_lemma_size                       3
% 3.57/1.00  --prop_impl_unit_size                   0
% 3.57/1.00  --prop_impl_unit                        []
% 3.57/1.00  --share_sel_clauses                     true
% 3.57/1.00  --reset_solvers                         false
% 3.57/1.00  --bc_imp_inh                            [conj_cone]
% 3.57/1.00  --conj_cone_tolerance                   3.
% 3.57/1.00  --extra_neg_conj                        none
% 3.57/1.00  --large_theory_mode                     true
% 3.57/1.00  --prolific_symb_bound                   200
% 3.57/1.00  --lt_threshold                          2000
% 3.57/1.00  --clause_weak_htbl                      true
% 3.57/1.00  --gc_record_bc_elim                     false
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing Options
% 3.57/1.00  
% 3.57/1.00  --preprocessing_flag                    true
% 3.57/1.00  --time_out_prep_mult                    0.1
% 3.57/1.00  --splitting_mode                        input
% 3.57/1.00  --splitting_grd                         true
% 3.57/1.00  --splitting_cvd                         false
% 3.57/1.00  --splitting_cvd_svl                     false
% 3.57/1.00  --splitting_nvd                         32
% 3.57/1.00  --sub_typing                            true
% 3.57/1.00  --prep_gs_sim                           true
% 3.57/1.00  --prep_unflatten                        true
% 3.57/1.00  --prep_res_sim                          true
% 3.57/1.00  --prep_upred                            true
% 3.57/1.00  --prep_sem_filter                       exhaustive
% 3.57/1.00  --prep_sem_filter_out                   false
% 3.57/1.00  --pred_elim                             true
% 3.57/1.00  --res_sim_input                         true
% 3.57/1.00  --eq_ax_congr_red                       true
% 3.57/1.00  --pure_diseq_elim                       true
% 3.57/1.00  --brand_transform                       false
% 3.57/1.00  --non_eq_to_eq                          false
% 3.57/1.00  --prep_def_merge                        true
% 3.57/1.00  --prep_def_merge_prop_impl              false
% 3.57/1.00  --prep_def_merge_mbd                    true
% 3.57/1.00  --prep_def_merge_tr_red                 false
% 3.57/1.00  --prep_def_merge_tr_cl                  false
% 3.57/1.00  --smt_preprocessing                     true
% 3.57/1.00  --smt_ac_axioms                         fast
% 3.57/1.00  --preprocessed_out                      false
% 3.57/1.00  --preprocessed_stats                    false
% 3.57/1.00  
% 3.57/1.00  ------ Abstraction refinement Options
% 3.57/1.00  
% 3.57/1.00  --abstr_ref                             []
% 3.57/1.00  --abstr_ref_prep                        false
% 3.57/1.00  --abstr_ref_until_sat                   false
% 3.57/1.00  --abstr_ref_sig_restrict                funpre
% 3.57/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/1.00  --abstr_ref_under                       []
% 3.57/1.00  
% 3.57/1.00  ------ SAT Options
% 3.57/1.00  
% 3.57/1.00  --sat_mode                              false
% 3.57/1.00  --sat_fm_restart_options                ""
% 3.57/1.00  --sat_gr_def                            false
% 3.57/1.00  --sat_epr_types                         true
% 3.57/1.00  --sat_non_cyclic_types                  false
% 3.57/1.00  --sat_finite_models                     false
% 3.57/1.00  --sat_fm_lemmas                         false
% 3.57/1.00  --sat_fm_prep                           false
% 3.57/1.00  --sat_fm_uc_incr                        true
% 3.57/1.00  --sat_out_model                         small
% 3.57/1.00  --sat_out_clauses                       false
% 3.57/1.00  
% 3.57/1.00  ------ QBF Options
% 3.57/1.00  
% 3.57/1.00  --qbf_mode                              false
% 3.57/1.00  --qbf_elim_univ                         false
% 3.57/1.00  --qbf_dom_inst                          none
% 3.57/1.00  --qbf_dom_pre_inst                      false
% 3.57/1.00  --qbf_sk_in                             false
% 3.57/1.00  --qbf_pred_elim                         true
% 3.57/1.00  --qbf_split                             512
% 3.57/1.00  
% 3.57/1.00  ------ BMC1 Options
% 3.57/1.00  
% 3.57/1.00  --bmc1_incremental                      false
% 3.57/1.00  --bmc1_axioms                           reachable_all
% 3.57/1.00  --bmc1_min_bound                        0
% 3.57/1.00  --bmc1_max_bound                        -1
% 3.57/1.00  --bmc1_max_bound_default                -1
% 3.57/1.00  --bmc1_symbol_reachability              true
% 3.57/1.00  --bmc1_property_lemmas                  false
% 3.57/1.00  --bmc1_k_induction                      false
% 3.57/1.00  --bmc1_non_equiv_states                 false
% 3.57/1.00  --bmc1_deadlock                         false
% 3.57/1.00  --bmc1_ucm                              false
% 3.57/1.00  --bmc1_add_unsat_core                   none
% 3.57/1.00  --bmc1_unsat_core_children              false
% 3.57/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/1.00  --bmc1_out_stat                         full
% 3.57/1.00  --bmc1_ground_init                      false
% 3.57/1.00  --bmc1_pre_inst_next_state              false
% 3.57/1.00  --bmc1_pre_inst_state                   false
% 3.57/1.00  --bmc1_pre_inst_reach_state             false
% 3.57/1.00  --bmc1_out_unsat_core                   false
% 3.57/1.00  --bmc1_aig_witness_out                  false
% 3.57/1.00  --bmc1_verbose                          false
% 3.57/1.00  --bmc1_dump_clauses_tptp                false
% 3.57/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.57/1.00  --bmc1_dump_file                        -
% 3.57/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.57/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.57/1.00  --bmc1_ucm_extend_mode                  1
% 3.57/1.00  --bmc1_ucm_init_mode                    2
% 3.57/1.00  --bmc1_ucm_cone_mode                    none
% 3.57/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.57/1.00  --bmc1_ucm_relax_model                  4
% 3.57/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.57/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/1.00  --bmc1_ucm_layered_model                none
% 3.57/1.00  --bmc1_ucm_max_lemma_size               10
% 3.57/1.00  
% 3.57/1.00  ------ AIG Options
% 3.57/1.00  
% 3.57/1.00  --aig_mode                              false
% 3.57/1.00  
% 3.57/1.00  ------ Instantiation Options
% 3.57/1.00  
% 3.57/1.00  --instantiation_flag                    true
% 3.57/1.00  --inst_sos_flag                         true
% 3.57/1.00  --inst_sos_phase                        true
% 3.57/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/1.00  --inst_lit_sel_side                     num_symb
% 3.57/1.00  --inst_solver_per_active                1400
% 3.57/1.00  --inst_solver_calls_frac                1.
% 3.57/1.00  --inst_passive_queue_type               priority_queues
% 3.57/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/1.00  --inst_passive_queues_freq              [25;2]
% 3.57/1.00  --inst_dismatching                      true
% 3.57/1.00  --inst_eager_unprocessed_to_passive     true
% 3.57/1.00  --inst_prop_sim_given                   true
% 3.57/1.00  --inst_prop_sim_new                     false
% 3.57/1.00  --inst_subs_new                         false
% 3.57/1.00  --inst_eq_res_simp                      false
% 3.57/1.00  --inst_subs_given                       false
% 3.57/1.00  --inst_orphan_elimination               true
% 3.57/1.00  --inst_learning_loop_flag               true
% 3.57/1.00  --inst_learning_start                   3000
% 3.57/1.00  --inst_learning_factor                  2
% 3.57/1.00  --inst_start_prop_sim_after_learn       3
% 3.57/1.00  --inst_sel_renew                        solver
% 3.57/1.00  --inst_lit_activity_flag                true
% 3.57/1.00  --inst_restr_to_given                   false
% 3.57/1.00  --inst_activity_threshold               500
% 3.57/1.00  --inst_out_proof                        true
% 3.57/1.00  
% 3.57/1.00  ------ Resolution Options
% 3.57/1.00  
% 3.57/1.00  --resolution_flag                       true
% 3.57/1.00  --res_lit_sel                           adaptive
% 3.57/1.00  --res_lit_sel_side                      none
% 3.57/1.00  --res_ordering                          kbo
% 3.57/1.00  --res_to_prop_solver                    active
% 3.57/1.00  --res_prop_simpl_new                    false
% 3.57/1.00  --res_prop_simpl_given                  true
% 3.57/1.00  --res_passive_queue_type                priority_queues
% 3.57/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/1.00  --res_passive_queues_freq               [15;5]
% 3.57/1.00  --res_forward_subs                      full
% 3.57/1.00  --res_backward_subs                     full
% 3.57/1.00  --res_forward_subs_resolution           true
% 3.57/1.00  --res_backward_subs_resolution          true
% 3.57/1.00  --res_orphan_elimination                true
% 3.57/1.00  --res_time_limit                        2.
% 3.57/1.00  --res_out_proof                         true
% 3.57/1.00  
% 3.57/1.00  ------ Superposition Options
% 3.57/1.00  
% 3.57/1.00  --superposition_flag                    true
% 3.57/1.00  --sup_passive_queue_type                priority_queues
% 3.57/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.57/1.00  --demod_completeness_check              fast
% 3.57/1.00  --demod_use_ground                      true
% 3.57/1.00  --sup_to_prop_solver                    passive
% 3.57/1.00  --sup_prop_simpl_new                    true
% 3.57/1.00  --sup_prop_simpl_given                  true
% 3.57/1.00  --sup_fun_splitting                     true
% 3.57/1.00  --sup_smt_interval                      50000
% 3.57/1.00  
% 3.57/1.00  ------ Superposition Simplification Setup
% 3.57/1.00  
% 3.57/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.57/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.57/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.57/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.57/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.57/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.57/1.00  --sup_immed_triv                        [TrivRules]
% 3.57/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/1.00  --sup_immed_bw_main                     []
% 3.57/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.57/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/1.00  --sup_input_bw                          []
% 3.57/1.00  
% 3.57/1.00  ------ Combination Options
% 3.57/1.00  
% 3.57/1.00  --comb_res_mult                         3
% 3.57/1.00  --comb_sup_mult                         2
% 3.57/1.00  --comb_inst_mult                        10
% 3.57/1.00  
% 3.57/1.00  ------ Debug Options
% 3.57/1.00  
% 3.57/1.00  --dbg_backtrace                         false
% 3.57/1.00  --dbg_dump_prop_clauses                 false
% 3.57/1.00  --dbg_dump_prop_clauses_file            -
% 3.57/1.00  --dbg_out_stat                          false
% 3.57/1.00  ------ Parsing...
% 3.57/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.57/1.00  ------ Proving...
% 3.57/1.00  ------ Problem Properties 
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  clauses                                 18
% 3.57/1.00  conjectures                             4
% 3.57/1.00  EPR                                     6
% 3.57/1.00  Horn                                    15
% 3.57/1.00  unary                                   6
% 3.57/1.00  binary                                  6
% 3.57/1.00  lits                                    36
% 3.57/1.00  lits eq                                 10
% 3.57/1.00  fd_pure                                 0
% 3.57/1.00  fd_pseudo                               0
% 3.57/1.00  fd_cond                                 0
% 3.57/1.00  fd_pseudo_cond                          4
% 3.57/1.00  AC symbols                              0
% 3.57/1.00  
% 3.57/1.00  ------ Schedule dynamic 5 is on 
% 3.57/1.00  
% 3.57/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  ------ 
% 3.57/1.00  Current options:
% 3.57/1.00  ------ 
% 3.57/1.00  
% 3.57/1.00  ------ Input Options
% 3.57/1.00  
% 3.57/1.00  --out_options                           all
% 3.57/1.00  --tptp_safe_out                         true
% 3.57/1.00  --problem_path                          ""
% 3.57/1.00  --include_path                          ""
% 3.57/1.00  --clausifier                            res/vclausify_rel
% 3.57/1.00  --clausifier_options                    ""
% 3.57/1.00  --stdin                                 false
% 3.57/1.00  --stats_out                             all
% 3.57/1.00  
% 3.57/1.00  ------ General Options
% 3.57/1.00  
% 3.57/1.00  --fof                                   false
% 3.57/1.00  --time_out_real                         305.
% 3.57/1.00  --time_out_virtual                      -1.
% 3.57/1.00  --symbol_type_check                     false
% 3.57/1.00  --clausify_out                          false
% 3.57/1.00  --sig_cnt_out                           false
% 3.57/1.00  --trig_cnt_out                          false
% 3.57/1.00  --trig_cnt_out_tolerance                1.
% 3.57/1.00  --trig_cnt_out_sk_spl                   false
% 3.57/1.00  --abstr_cl_out                          false
% 3.57/1.00  
% 3.57/1.00  ------ Global Options
% 3.57/1.00  
% 3.57/1.00  --schedule                              default
% 3.57/1.00  --add_important_lit                     false
% 3.57/1.00  --prop_solver_per_cl                    1000
% 3.57/1.00  --min_unsat_core                        false
% 3.57/1.00  --soft_assumptions                      false
% 3.57/1.00  --soft_lemma_size                       3
% 3.57/1.00  --prop_impl_unit_size                   0
% 3.57/1.00  --prop_impl_unit                        []
% 3.57/1.00  --share_sel_clauses                     true
% 3.57/1.00  --reset_solvers                         false
% 3.57/1.00  --bc_imp_inh                            [conj_cone]
% 3.57/1.00  --conj_cone_tolerance                   3.
% 3.57/1.00  --extra_neg_conj                        none
% 3.57/1.00  --large_theory_mode                     true
% 3.57/1.00  --prolific_symb_bound                   200
% 3.57/1.00  --lt_threshold                          2000
% 3.57/1.00  --clause_weak_htbl                      true
% 3.57/1.00  --gc_record_bc_elim                     false
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing Options
% 3.57/1.00  
% 3.57/1.00  --preprocessing_flag                    true
% 3.57/1.00  --time_out_prep_mult                    0.1
% 3.57/1.00  --splitting_mode                        input
% 3.57/1.00  --splitting_grd                         true
% 3.57/1.00  --splitting_cvd                         false
% 3.57/1.00  --splitting_cvd_svl                     false
% 3.57/1.00  --splitting_nvd                         32
% 3.57/1.00  --sub_typing                            true
% 3.57/1.00  --prep_gs_sim                           true
% 3.57/1.00  --prep_unflatten                        true
% 3.57/1.00  --prep_res_sim                          true
% 3.57/1.00  --prep_upred                            true
% 3.57/1.00  --prep_sem_filter                       exhaustive
% 3.57/1.00  --prep_sem_filter_out                   false
% 3.57/1.00  --pred_elim                             true
% 3.57/1.00  --res_sim_input                         true
% 3.57/1.00  --eq_ax_congr_red                       true
% 3.57/1.00  --pure_diseq_elim                       true
% 3.57/1.00  --brand_transform                       false
% 3.57/1.00  --non_eq_to_eq                          false
% 3.57/1.00  --prep_def_merge                        true
% 3.57/1.00  --prep_def_merge_prop_impl              false
% 3.57/1.00  --prep_def_merge_mbd                    true
% 3.57/1.00  --prep_def_merge_tr_red                 false
% 3.57/1.00  --prep_def_merge_tr_cl                  false
% 3.57/1.00  --smt_preprocessing                     true
% 3.57/1.00  --smt_ac_axioms                         fast
% 3.57/1.00  --preprocessed_out                      false
% 3.57/1.00  --preprocessed_stats                    false
% 3.57/1.00  
% 3.57/1.00  ------ Abstraction refinement Options
% 3.57/1.00  
% 3.57/1.00  --abstr_ref                             []
% 3.57/1.00  --abstr_ref_prep                        false
% 3.57/1.00  --abstr_ref_until_sat                   false
% 3.57/1.00  --abstr_ref_sig_restrict                funpre
% 3.57/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.57/1.00  --abstr_ref_under                       []
% 3.57/1.00  
% 3.57/1.00  ------ SAT Options
% 3.57/1.00  
% 3.57/1.00  --sat_mode                              false
% 3.57/1.00  --sat_fm_restart_options                ""
% 3.57/1.00  --sat_gr_def                            false
% 3.57/1.00  --sat_epr_types                         true
% 3.57/1.00  --sat_non_cyclic_types                  false
% 3.57/1.00  --sat_finite_models                     false
% 3.57/1.00  --sat_fm_lemmas                         false
% 3.57/1.00  --sat_fm_prep                           false
% 3.57/1.00  --sat_fm_uc_incr                        true
% 3.57/1.00  --sat_out_model                         small
% 3.57/1.00  --sat_out_clauses                       false
% 3.57/1.00  
% 3.57/1.00  ------ QBF Options
% 3.57/1.00  
% 3.57/1.00  --qbf_mode                              false
% 3.57/1.00  --qbf_elim_univ                         false
% 3.57/1.00  --qbf_dom_inst                          none
% 3.57/1.00  --qbf_dom_pre_inst                      false
% 3.57/1.00  --qbf_sk_in                             false
% 3.57/1.00  --qbf_pred_elim                         true
% 3.57/1.00  --qbf_split                             512
% 3.57/1.00  
% 3.57/1.00  ------ BMC1 Options
% 3.57/1.00  
% 3.57/1.00  --bmc1_incremental                      false
% 3.57/1.00  --bmc1_axioms                           reachable_all
% 3.57/1.00  --bmc1_min_bound                        0
% 3.57/1.00  --bmc1_max_bound                        -1
% 3.57/1.00  --bmc1_max_bound_default                -1
% 3.57/1.00  --bmc1_symbol_reachability              true
% 3.57/1.00  --bmc1_property_lemmas                  false
% 3.57/1.00  --bmc1_k_induction                      false
% 3.57/1.00  --bmc1_non_equiv_states                 false
% 3.57/1.00  --bmc1_deadlock                         false
% 3.57/1.00  --bmc1_ucm                              false
% 3.57/1.00  --bmc1_add_unsat_core                   none
% 3.57/1.00  --bmc1_unsat_core_children              false
% 3.57/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.57/1.00  --bmc1_out_stat                         full
% 3.57/1.00  --bmc1_ground_init                      false
% 3.57/1.00  --bmc1_pre_inst_next_state              false
% 3.57/1.00  --bmc1_pre_inst_state                   false
% 3.57/1.00  --bmc1_pre_inst_reach_state             false
% 3.57/1.00  --bmc1_out_unsat_core                   false
% 3.57/1.00  --bmc1_aig_witness_out                  false
% 3.57/1.00  --bmc1_verbose                          false
% 3.57/1.00  --bmc1_dump_clauses_tptp                false
% 3.57/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.57/1.00  --bmc1_dump_file                        -
% 3.57/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.57/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.57/1.00  --bmc1_ucm_extend_mode                  1
% 3.57/1.00  --bmc1_ucm_init_mode                    2
% 3.57/1.00  --bmc1_ucm_cone_mode                    none
% 3.57/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.57/1.00  --bmc1_ucm_relax_model                  4
% 3.57/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.57/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.57/1.00  --bmc1_ucm_layered_model                none
% 3.57/1.00  --bmc1_ucm_max_lemma_size               10
% 3.57/1.00  
% 3.57/1.00  ------ AIG Options
% 3.57/1.00  
% 3.57/1.00  --aig_mode                              false
% 3.57/1.00  
% 3.57/1.00  ------ Instantiation Options
% 3.57/1.00  
% 3.57/1.00  --instantiation_flag                    true
% 3.57/1.00  --inst_sos_flag                         true
% 3.57/1.00  --inst_sos_phase                        true
% 3.57/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.57/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.57/1.00  --inst_lit_sel_side                     none
% 3.57/1.00  --inst_solver_per_active                1400
% 3.57/1.00  --inst_solver_calls_frac                1.
% 3.57/1.00  --inst_passive_queue_type               priority_queues
% 3.57/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.57/1.00  --inst_passive_queues_freq              [25;2]
% 3.57/1.00  --inst_dismatching                      true
% 3.57/1.00  --inst_eager_unprocessed_to_passive     true
% 3.57/1.00  --inst_prop_sim_given                   true
% 3.57/1.00  --inst_prop_sim_new                     false
% 3.57/1.00  --inst_subs_new                         false
% 3.57/1.00  --inst_eq_res_simp                      false
% 3.57/1.00  --inst_subs_given                       false
% 3.57/1.00  --inst_orphan_elimination               true
% 3.57/1.00  --inst_learning_loop_flag               true
% 3.57/1.00  --inst_learning_start                   3000
% 3.57/1.00  --inst_learning_factor                  2
% 3.57/1.00  --inst_start_prop_sim_after_learn       3
% 3.57/1.00  --inst_sel_renew                        solver
% 3.57/1.00  --inst_lit_activity_flag                true
% 3.57/1.00  --inst_restr_to_given                   false
% 3.57/1.00  --inst_activity_threshold               500
% 3.57/1.00  --inst_out_proof                        true
% 3.57/1.00  
% 3.57/1.00  ------ Resolution Options
% 3.57/1.00  
% 3.57/1.00  --resolution_flag                       false
% 3.57/1.00  --res_lit_sel                           adaptive
% 3.57/1.00  --res_lit_sel_side                      none
% 3.57/1.00  --res_ordering                          kbo
% 3.57/1.00  --res_to_prop_solver                    active
% 3.57/1.00  --res_prop_simpl_new                    false
% 3.57/1.00  --res_prop_simpl_given                  true
% 3.57/1.00  --res_passive_queue_type                priority_queues
% 3.57/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.57/1.00  --res_passive_queues_freq               [15;5]
% 3.57/1.00  --res_forward_subs                      full
% 3.57/1.00  --res_backward_subs                     full
% 3.57/1.00  --res_forward_subs_resolution           true
% 3.57/1.00  --res_backward_subs_resolution          true
% 3.57/1.00  --res_orphan_elimination                true
% 3.57/1.00  --res_time_limit                        2.
% 3.57/1.00  --res_out_proof                         true
% 3.57/1.00  
% 3.57/1.00  ------ Superposition Options
% 3.57/1.00  
% 3.57/1.00  --superposition_flag                    true
% 3.57/1.00  --sup_passive_queue_type                priority_queues
% 3.57/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.57/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.57/1.00  --demod_completeness_check              fast
% 3.57/1.00  --demod_use_ground                      true
% 3.57/1.00  --sup_to_prop_solver                    passive
% 3.57/1.00  --sup_prop_simpl_new                    true
% 3.57/1.00  --sup_prop_simpl_given                  true
% 3.57/1.00  --sup_fun_splitting                     true
% 3.57/1.00  --sup_smt_interval                      50000
% 3.57/1.00  
% 3.57/1.00  ------ Superposition Simplification Setup
% 3.57/1.00  
% 3.57/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.57/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.57/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.57/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.57/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.57/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.57/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.57/1.00  --sup_immed_triv                        [TrivRules]
% 3.57/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/1.00  --sup_immed_bw_main                     []
% 3.57/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.57/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.57/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.57/1.00  --sup_input_bw                          []
% 3.57/1.00  
% 3.57/1.00  ------ Combination Options
% 3.57/1.00  
% 3.57/1.00  --comb_res_mult                         3
% 3.57/1.00  --comb_sup_mult                         2
% 3.57/1.00  --comb_inst_mult                        10
% 3.57/1.00  
% 3.57/1.00  ------ Debug Options
% 3.57/1.00  
% 3.57/1.00  --dbg_backtrace                         false
% 3.57/1.00  --dbg_dump_prop_clauses                 false
% 3.57/1.00  --dbg_dump_prop_clauses_file            -
% 3.57/1.00  --dbg_out_stat                          false
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  ------ Proving...
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  % SZS status Theorem for theBenchmark.p
% 3.57/1.00  
% 3.57/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.57/1.00  
% 3.57/1.00  fof(f2,axiom,(
% 3.57/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f11,plain,(
% 3.57/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.57/1.00    inference(ennf_transformation,[],[f2])).
% 3.57/1.00  
% 3.57/1.00  fof(f18,plain,(
% 3.57/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.57/1.00    inference(nnf_transformation,[],[f11])).
% 3.57/1.00  
% 3.57/1.00  fof(f19,plain,(
% 3.57/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 3.57/1.00    introduced(choice_axiom,[])).
% 3.57/1.00  
% 3.57/1.00  fof(f20,plain,(
% 3.57/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 3.57/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).
% 3.57/1.00  
% 3.57/1.00  fof(f32,plain,(
% 3.57/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f20])).
% 3.57/1.00  
% 3.57/1.00  fof(f4,axiom,(
% 3.57/1.00    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f37,plain,(
% 3.57/1.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f4])).
% 3.57/1.00  
% 3.57/1.00  fof(f7,axiom,(
% 3.57/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f25,plain,(
% 3.57/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.57/1.00    inference(nnf_transformation,[],[f7])).
% 3.57/1.00  
% 3.57/1.00  fof(f26,plain,(
% 3.57/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.57/1.00    inference(flattening,[],[f25])).
% 3.57/1.00  
% 3.57/1.00  fof(f43,plain,(
% 3.57/1.00    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f26])).
% 3.57/1.00  
% 3.57/1.00  fof(f5,axiom,(
% 3.57/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f38,plain,(
% 3.57/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f5])).
% 3.57/1.00  
% 3.57/1.00  fof(f50,plain,(
% 3.57/1.00    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X2)))) )),
% 3.57/1.00    inference(definition_unfolding,[],[f43,f38])).
% 3.57/1.00  
% 3.57/1.00  fof(f54,plain,(
% 3.57/1.00    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_tarski(X2,X2)))) )),
% 3.57/1.00    inference(equality_resolution,[],[f50])).
% 3.57/1.00  
% 3.57/1.00  fof(f1,axiom,(
% 3.57/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f10,plain,(
% 3.57/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.57/1.00    inference(ennf_transformation,[],[f1])).
% 3.57/1.00  
% 3.57/1.00  fof(f14,plain,(
% 3.57/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.57/1.00    inference(nnf_transformation,[],[f10])).
% 3.57/1.00  
% 3.57/1.00  fof(f15,plain,(
% 3.57/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.57/1.00    inference(rectify,[],[f14])).
% 3.57/1.00  
% 3.57/1.00  fof(f16,plain,(
% 3.57/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.57/1.00    introduced(choice_axiom,[])).
% 3.57/1.00  
% 3.57/1.00  fof(f17,plain,(
% 3.57/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.57/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 3.57/1.00  
% 3.57/1.00  fof(f30,plain,(
% 3.57/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f17])).
% 3.57/1.00  
% 3.57/1.00  fof(f8,conjecture,(
% 3.57/1.00    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f9,negated_conjecture,(
% 3.57/1.00    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.57/1.00    inference(negated_conjecture,[],[f8])).
% 3.57/1.00  
% 3.57/1.00  fof(f12,plain,(
% 3.57/1.00    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 3.57/1.00    inference(ennf_transformation,[],[f9])).
% 3.57/1.00  
% 3.57/1.00  fof(f13,plain,(
% 3.57/1.00    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 3.57/1.00    inference(flattening,[],[f12])).
% 3.57/1.00  
% 3.57/1.00  fof(f27,plain,(
% 3.57/1.00    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK3 != sK5 | sK2 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5))),
% 3.57/1.00    introduced(choice_axiom,[])).
% 3.57/1.00  
% 3.57/1.00  fof(f28,plain,(
% 3.57/1.00    (sK3 != sK5 | sK2 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5)),
% 3.57/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f13,f27])).
% 3.57/1.00  
% 3.57/1.00  fof(f45,plain,(
% 3.57/1.00    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5)),
% 3.57/1.00    inference(cnf_transformation,[],[f28])).
% 3.57/1.00  
% 3.57/1.00  fof(f6,axiom,(
% 3.57/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f23,plain,(
% 3.57/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.57/1.00    inference(nnf_transformation,[],[f6])).
% 3.57/1.00  
% 3.57/1.00  fof(f24,plain,(
% 3.57/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.57/1.00    inference(flattening,[],[f23])).
% 3.57/1.00  
% 3.57/1.00  fof(f41,plain,(
% 3.57/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f24])).
% 3.57/1.00  
% 3.57/1.00  fof(f39,plain,(
% 3.57/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f24])).
% 3.57/1.00  
% 3.57/1.00  fof(f47,plain,(
% 3.57/1.00    k1_xboole_0 != sK3),
% 3.57/1.00    inference(cnf_transformation,[],[f28])).
% 3.57/1.00  
% 3.57/1.00  fof(f3,axiom,(
% 3.57/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.57/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.57/1.00  
% 3.57/1.00  fof(f21,plain,(
% 3.57/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.57/1.00    inference(nnf_transformation,[],[f3])).
% 3.57/1.00  
% 3.57/1.00  fof(f22,plain,(
% 3.57/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.57/1.00    inference(flattening,[],[f21])).
% 3.57/1.00  
% 3.57/1.00  fof(f34,plain,(
% 3.57/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.57/1.00    inference(cnf_transformation,[],[f22])).
% 3.57/1.00  
% 3.57/1.00  fof(f53,plain,(
% 3.57/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.57/1.00    inference(equality_resolution,[],[f34])).
% 3.57/1.00  
% 3.57/1.00  fof(f36,plain,(
% 3.57/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f22])).
% 3.57/1.00  
% 3.57/1.00  fof(f40,plain,(
% 3.57/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.57/1.00    inference(cnf_transformation,[],[f24])).
% 3.57/1.00  
% 3.57/1.00  fof(f46,plain,(
% 3.57/1.00    k1_xboole_0 != sK2),
% 3.57/1.00    inference(cnf_transformation,[],[f28])).
% 3.57/1.00  
% 3.57/1.00  fof(f31,plain,(
% 3.57/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.57/1.00    inference(cnf_transformation,[],[f17])).
% 3.57/1.00  
% 3.57/1.00  fof(f48,plain,(
% 3.57/1.00    sK3 != sK5 | sK2 != sK4),
% 3.57/1.00    inference(cnf_transformation,[],[f28])).
% 3.57/1.00  
% 3.57/1.00  cnf(c_4,plain,
% 3.57/1.00      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 3.57/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_456,plain,
% 3.57/1.00      ( X0 = X1
% 3.57/1.00      | r2_hidden(sK1(X1,X0),X0) = iProver_top
% 3.57/1.00      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_8,plain,
% 3.57/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.57/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_13,plain,
% 3.57/1.00      ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X0,X0))) ),
% 3.57/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_449,plain,
% 3.57/1.00      ( r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X0,X0))) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_891,plain,
% 3.57/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_8,c_449]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1991,plain,
% 3.57/1.00      ( k1_xboole_0 = X0
% 3.57/1.00      | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_456,c_891]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1,plain,
% 3.57/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.57/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_459,plain,
% 3.57/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.57/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_18,negated_conjecture,
% 3.57/1.00      ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
% 3.57/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_9,plain,
% 3.57/1.00      ( ~ r2_hidden(X0,X1)
% 3.57/1.00      | ~ r2_hidden(X2,X3)
% 3.57/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.57/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_453,plain,
% 3.57/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.57/1.00      | r2_hidden(X2,X3) != iProver_top
% 3.57/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1971,plain,
% 3.57/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 3.57/1.00      | r2_hidden(X1,sK5) != iProver_top
% 3.57/1.00      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_18,c_453]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_11,plain,
% 3.57/1.00      ( r2_hidden(X0,X1)
% 3.57/1.00      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.57/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_451,plain,
% 3.57/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.57/1.00      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2047,plain,
% 3.57/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 3.57/1.00      | r2_hidden(X0,sK2) = iProver_top
% 3.57/1.00      | r2_hidden(X1,sK5) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1971,c_451]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2202,plain,
% 3.57/1.00      ( r2_hidden(X0,sK5) != iProver_top
% 3.57/1.00      | r2_hidden(sK0(sK4,X1),sK2) = iProver_top
% 3.57/1.00      | r1_tarski(sK4,X1) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_459,c_2047]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3145,plain,
% 3.57/1.00      ( sK5 = k1_xboole_0
% 3.57/1.00      | r2_hidden(sK0(sK4,X0),sK2) = iProver_top
% 3.57/1.00      | r1_tarski(sK4,X0) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1991,c_2202]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_16,negated_conjecture,
% 3.57/1.00      ( k1_xboole_0 != sK3 ),
% 3.57/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_7,plain,
% 3.57/1.00      ( r1_tarski(X0,X0) ),
% 3.57/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_37,plain,
% 3.57/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_5,plain,
% 3.57/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.57/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_41,plain,
% 3.57/1.00      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.57/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_532,plain,
% 3.57/1.00      ( ~ r1_tarski(sK5,sK3) | ~ r1_tarski(sK3,sK5) | sK3 = sK5 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_533,plain,
% 3.57/1.00      ( sK3 = sK5
% 3.57/1.00      | r1_tarski(sK5,sK3) != iProver_top
% 3.57/1.00      | r1_tarski(sK3,sK5) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_532]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_248,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_500,plain,
% 3.57/1.00      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_248]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_723,plain,
% 3.57/1.00      ( sK3 != sK5 | k1_xboole_0 != sK5 | k1_xboole_0 = sK3 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_500]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_854,plain,
% 3.57/1.00      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_248]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_855,plain,
% 3.57/1.00      ( sK5 != k1_xboole_0
% 3.57/1.00      | k1_xboole_0 = sK5
% 3.57/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_854]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_10,plain,
% 3.57/1.00      ( r2_hidden(X0,X1)
% 3.57/1.00      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.57/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_452,plain,
% 3.57/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.57/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1322,plain,
% 3.57/1.00      ( r2_hidden(X0,sK5) = iProver_top
% 3.57/1.00      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK2,sK3)) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_18,c_452]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1976,plain,
% 3.57/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 3.57/1.00      | r2_hidden(X1,sK5) = iProver_top
% 3.57/1.00      | r2_hidden(X1,sK3) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_453,c_1322]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2120,plain,
% 3.57/1.00      ( sK2 = k1_xboole_0
% 3.57/1.00      | r2_hidden(X0,sK5) = iProver_top
% 3.57/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1991,c_1976]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_17,negated_conjecture,
% 3.57/1.00      ( k1_xboole_0 != sK2 ),
% 3.57/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_524,plain,
% 3.57/1.00      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_248]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_525,plain,
% 3.57/1.00      ( sK2 != k1_xboole_0
% 3.57/1.00      | k1_xboole_0 = sK2
% 3.57/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_524]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2262,plain,
% 3.57/1.00      ( r2_hidden(X0,sK5) = iProver_top
% 3.57/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_2120,c_17,c_37,c_41,c_525]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2268,plain,
% 3.57/1.00      ( r2_hidden(sK0(sK3,X0),sK5) = iProver_top
% 3.57/1.00      | r1_tarski(sK3,X0) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_459,c_2262]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_0,plain,
% 3.57/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.57/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_460,plain,
% 3.57/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.57/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2484,plain,
% 3.57/1.00      ( r1_tarski(sK3,sK5) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_2268,c_460]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1156,plain,
% 3.57/1.00      ( r2_hidden(X0,sK4) = iProver_top
% 3.57/1.00      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK2,sK3)) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_18,c_451]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_1975,plain,
% 3.57/1.00      ( r2_hidden(X0,sK4) = iProver_top
% 3.57/1.00      | r2_hidden(X0,sK2) != iProver_top
% 3.57/1.00      | r2_hidden(X1,sK3) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_453,c_1156]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2094,plain,
% 3.57/1.00      ( sK2 = k1_xboole_0
% 3.57/1.00      | r2_hidden(X0,sK3) != iProver_top
% 3.57/1.00      | r2_hidden(sK1(k1_xboole_0,sK2),sK4) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1991,c_1975]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2419,plain,
% 3.57/1.00      ( r2_hidden(X0,sK3) != iProver_top
% 3.57/1.00      | r2_hidden(sK1(k1_xboole_0,sK2),sK4) = iProver_top ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_2094,c_17,c_37,c_41,c_525]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2425,plain,
% 3.57/1.00      ( r2_hidden(sK1(k1_xboole_0,sK2),sK4) = iProver_top
% 3.57/1.00      | r1_tarski(sK3,X0) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_459,c_2419]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_501,plain,
% 3.57/1.00      ( sK3 != k1_xboole_0
% 3.57/1.00      | k1_xboole_0 = sK3
% 3.57/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_500]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2428,plain,
% 3.57/1.00      ( sK3 = k1_xboole_0
% 3.57/1.00      | r2_hidden(sK1(k1_xboole_0,sK2),sK4) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1991,c_2419]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3247,plain,
% 3.57/1.00      ( r2_hidden(sK1(k1_xboole_0,sK2),sK4) = iProver_top ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_2425,c_16,c_37,c_41,c_501,c_2428]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2046,plain,
% 3.57/1.00      ( r2_hidden(X0,sK4) != iProver_top
% 3.57/1.00      | r2_hidden(X1,sK5) != iProver_top
% 3.57/1.00      | r2_hidden(X1,sK3) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1971,c_452]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3253,plain,
% 3.57/1.00      ( r2_hidden(X0,sK5) != iProver_top
% 3.57/1.00      | r2_hidden(X0,sK3) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_3247,c_2046]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3510,plain,
% 3.57/1.00      ( r2_hidden(sK0(sK5,X0),sK3) = iProver_top
% 3.57/1.00      | r1_tarski(sK5,X0) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_459,c_3253]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3922,plain,
% 3.57/1.00      ( r1_tarski(sK5,sK3) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_3510,c_460]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_8653,plain,
% 3.57/1.00      ( r2_hidden(sK0(sK4,X0),sK2) = iProver_top
% 3.57/1.00      | r1_tarski(sK4,X0) = iProver_top ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_3145,c_16,c_37,c_41,c_533,c_723,c_855,c_2484,c_3922]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_8659,plain,
% 3.57/1.00      ( r1_tarski(sK4,sK2) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_8653,c_460]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2271,plain,
% 3.57/1.00      ( sK3 = k1_xboole_0
% 3.57/1.00      | r2_hidden(sK1(k1_xboole_0,sK3),sK5) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_1991,c_2262]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_5130,plain,
% 3.57/1.00      ( r2_hidden(sK1(k1_xboole_0,sK3),sK5) = iProver_top ),
% 3.57/1.00      inference(global_propositional_subsumption,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_2271,c_16,c_37,c_41,c_501]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_455,plain,
% 3.57/1.00      ( X0 = X1
% 3.57/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.57/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2574,plain,
% 3.57/1.00      ( sK5 = sK3 | r1_tarski(sK5,sK3) != iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_2484,c_455]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_3935,plain,
% 3.57/1.00      ( sK5 = sK3 ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_3922,c_2574]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_5134,plain,
% 3.57/1.00      ( r2_hidden(sK1(k1_xboole_0,sK3),sK3) = iProver_top ),
% 3.57/1.00      inference(light_normalisation,[status(thm)],[c_5130,c_3935]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_2091,plain,
% 3.57/1.00      ( r2_hidden(X0,sK3) != iProver_top
% 3.57/1.00      | r2_hidden(sK0(sK2,X1),sK4) = iProver_top
% 3.57/1.00      | r1_tarski(sK2,X1) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_459,c_1975]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_5138,plain,
% 3.57/1.00      ( r2_hidden(sK0(sK2,X0),sK4) = iProver_top
% 3.57/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_5134,c_2091]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_6706,plain,
% 3.57/1.00      ( r1_tarski(sK2,sK4) = iProver_top ),
% 3.57/1.00      inference(superposition,[status(thm)],[c_5138,c_460]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_476,plain,
% 3.57/1.00      ( ~ r1_tarski(sK4,sK2) | ~ r1_tarski(sK2,sK4) | sK2 = sK4 ),
% 3.57/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_477,plain,
% 3.57/1.00      ( sK2 = sK4
% 3.57/1.00      | r1_tarski(sK4,sK2) != iProver_top
% 3.57/1.00      | r1_tarski(sK2,sK4) != iProver_top ),
% 3.57/1.00      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(c_15,negated_conjecture,
% 3.57/1.00      ( sK2 != sK4 | sK3 != sK5 ),
% 3.57/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.57/1.00  
% 3.57/1.00  cnf(contradiction,plain,
% 3.57/1.00      ( $false ),
% 3.57/1.00      inference(minisat,
% 3.57/1.00                [status(thm)],
% 3.57/1.00                [c_8659,c_6706,c_3922,c_2484,c_533,c_477,c_15]) ).
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.57/1.00  
% 3.57/1.00  ------                               Statistics
% 3.57/1.00  
% 3.57/1.00  ------ General
% 3.57/1.00  
% 3.57/1.00  abstr_ref_over_cycles:                  0
% 3.57/1.00  abstr_ref_under_cycles:                 0
% 3.57/1.00  gc_basic_clause_elim:                   0
% 3.57/1.00  forced_gc_time:                         0
% 3.57/1.00  parsing_time:                           0.008
% 3.57/1.00  unif_index_cands_time:                  0.
% 3.57/1.00  unif_index_add_time:                    0.
% 3.57/1.00  orderings_time:                         0.
% 3.57/1.00  out_proof_time:                         0.008
% 3.57/1.00  total_time:                             0.3
% 3.57/1.00  num_of_symbols:                         44
% 3.57/1.00  num_of_terms:                           8348
% 3.57/1.00  
% 3.57/1.00  ------ Preprocessing
% 3.57/1.00  
% 3.57/1.00  num_of_splits:                          0
% 3.57/1.00  num_of_split_atoms:                     0
% 3.57/1.00  num_of_reused_defs:                     0
% 3.57/1.00  num_eq_ax_congr_red:                    30
% 3.57/1.00  num_of_sem_filtered_clauses:            1
% 3.57/1.00  num_of_subtypes:                        0
% 3.57/1.00  monotx_restored_types:                  0
% 3.57/1.00  sat_num_of_epr_types:                   0
% 3.57/1.00  sat_num_of_non_cyclic_types:            0
% 3.57/1.00  sat_guarded_non_collapsed_types:        0
% 3.57/1.00  num_pure_diseq_elim:                    0
% 3.57/1.00  simp_replaced_by:                       0
% 3.57/1.00  res_preprocessed:                       83
% 3.57/1.00  prep_upred:                             0
% 3.57/1.00  prep_unflattend:                        0
% 3.57/1.00  smt_new_axioms:                         0
% 3.57/1.00  pred_elim_cands:                        2
% 3.57/1.00  pred_elim:                              0
% 3.57/1.00  pred_elim_cl:                           0
% 3.57/1.00  pred_elim_cycles:                       2
% 3.57/1.00  merged_defs:                            0
% 3.57/1.00  merged_defs_ncl:                        0
% 3.57/1.00  bin_hyper_res:                          0
% 3.57/1.00  prep_cycles:                            4
% 3.57/1.00  pred_elim_time:                         0.
% 3.57/1.00  splitting_time:                         0.
% 3.57/1.00  sem_filter_time:                        0.
% 3.57/1.00  monotx_time:                            0.001
% 3.57/1.00  subtype_inf_time:                       0.
% 3.57/1.00  
% 3.57/1.00  ------ Problem properties
% 3.57/1.00  
% 3.57/1.00  clauses:                                18
% 3.57/1.00  conjectures:                            4
% 3.57/1.00  epr:                                    6
% 3.57/1.00  horn:                                   15
% 3.57/1.00  ground:                                 4
% 3.57/1.00  unary:                                  6
% 3.57/1.00  binary:                                 6
% 3.57/1.00  lits:                                   36
% 3.57/1.00  lits_eq:                                10
% 3.57/1.00  fd_pure:                                0
% 3.57/1.00  fd_pseudo:                              0
% 3.57/1.00  fd_cond:                                0
% 3.57/1.00  fd_pseudo_cond:                         4
% 3.57/1.00  ac_symbols:                             0
% 3.57/1.00  
% 3.57/1.00  ------ Propositional Solver
% 3.57/1.00  
% 3.57/1.00  prop_solver_calls:                      29
% 3.57/1.00  prop_fast_solver_calls:                 704
% 3.57/1.00  smt_solver_calls:                       0
% 3.57/1.00  smt_fast_solver_calls:                  0
% 3.57/1.00  prop_num_of_clauses:                    4196
% 3.57/1.00  prop_preprocess_simplified:             10766
% 3.57/1.00  prop_fo_subsumed:                       30
% 3.57/1.00  prop_solver_time:                       0.
% 3.57/1.00  smt_solver_time:                        0.
% 3.57/1.00  smt_fast_solver_time:                   0.
% 3.57/1.00  prop_fast_solver_time:                  0.
% 3.57/1.00  prop_unsat_core_time:                   0.
% 3.57/1.00  
% 3.57/1.00  ------ QBF
% 3.57/1.00  
% 3.57/1.00  qbf_q_res:                              0
% 3.57/1.00  qbf_num_tautologies:                    0
% 3.57/1.00  qbf_prep_cycles:                        0
% 3.57/1.00  
% 3.57/1.00  ------ BMC1
% 3.57/1.00  
% 3.57/1.00  bmc1_current_bound:                     -1
% 3.57/1.00  bmc1_last_solved_bound:                 -1
% 3.57/1.00  bmc1_unsat_core_size:                   -1
% 3.57/1.00  bmc1_unsat_core_parents_size:           -1
% 3.57/1.00  bmc1_merge_next_fun:                    0
% 3.57/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.57/1.00  
% 3.57/1.00  ------ Instantiation
% 3.57/1.00  
% 3.57/1.00  inst_num_of_clauses:                    1162
% 3.57/1.00  inst_num_in_passive:                    773
% 3.57/1.00  inst_num_in_active:                     371
% 3.57/1.00  inst_num_in_unprocessed:                18
% 3.57/1.00  inst_num_of_loops:                      510
% 3.57/1.00  inst_num_of_learning_restarts:          0
% 3.57/1.00  inst_num_moves_active_passive:          139
% 3.57/1.00  inst_lit_activity:                      0
% 3.57/1.00  inst_lit_activity_moves:                0
% 3.57/1.00  inst_num_tautologies:                   0
% 3.57/1.00  inst_num_prop_implied:                  0
% 3.57/1.00  inst_num_existing_simplified:           0
% 3.57/1.00  inst_num_eq_res_simplified:             0
% 3.57/1.00  inst_num_child_elim:                    0
% 3.57/1.00  inst_num_of_dismatching_blockings:      323
% 3.57/1.00  inst_num_of_non_proper_insts:           768
% 3.57/1.00  inst_num_of_duplicates:                 0
% 3.57/1.00  inst_inst_num_from_inst_to_res:         0
% 3.57/1.00  inst_dismatching_checking_time:         0.
% 3.57/1.00  
% 3.57/1.00  ------ Resolution
% 3.57/1.00  
% 3.57/1.00  res_num_of_clauses:                     0
% 3.57/1.00  res_num_in_passive:                     0
% 3.57/1.00  res_num_in_active:                      0
% 3.57/1.00  res_num_of_loops:                       87
% 3.57/1.00  res_forward_subset_subsumed:            46
% 3.57/1.00  res_backward_subset_subsumed:           0
% 3.57/1.00  res_forward_subsumed:                   0
% 3.57/1.00  res_backward_subsumed:                  0
% 3.57/1.00  res_forward_subsumption_resolution:     0
% 3.57/1.00  res_backward_subsumption_resolution:    0
% 3.57/1.00  res_clause_to_clause_subsumption:       1743
% 3.57/1.00  res_orphan_elimination:                 0
% 3.57/1.00  res_tautology_del:                      43
% 3.57/1.00  res_num_eq_res_simplified:              0
% 3.57/1.00  res_num_sel_changes:                    0
% 3.57/1.00  res_moves_from_active_to_pass:          0
% 3.57/1.00  
% 3.57/1.00  ------ Superposition
% 3.57/1.00  
% 3.57/1.00  sup_time_total:                         0.
% 3.57/1.00  sup_time_generating:                    0.
% 3.57/1.00  sup_time_sim_full:                      0.
% 3.57/1.00  sup_time_sim_immed:                     0.
% 3.57/1.00  
% 3.57/1.00  sup_num_of_clauses:                     240
% 3.57/1.00  sup_num_in_active:                      80
% 3.57/1.00  sup_num_in_passive:                     160
% 3.57/1.00  sup_num_of_loops:                       100
% 3.57/1.00  sup_fw_superposition:                   308
% 3.57/1.00  sup_bw_superposition:                   299
% 3.57/1.00  sup_immediate_simplified:               133
% 3.57/1.00  sup_given_eliminated:                   8
% 3.57/1.00  comparisons_done:                       0
% 3.57/1.00  comparisons_avoided:                    0
% 3.57/1.00  
% 3.57/1.00  ------ Simplifications
% 3.57/1.00  
% 3.57/1.00  
% 3.57/1.00  sim_fw_subset_subsumed:                 68
% 3.57/1.00  sim_bw_subset_subsumed:                 67
% 3.57/1.00  sim_fw_subsumed:                        53
% 3.57/1.00  sim_bw_subsumed:                        58
% 3.57/1.00  sim_fw_subsumption_res:                 0
% 3.57/1.00  sim_bw_subsumption_res:                 0
% 3.57/1.00  sim_tautology_del:                      11
% 3.57/1.00  sim_eq_tautology_del:                   30
% 3.57/1.00  sim_eq_res_simp:                        0
% 3.57/1.00  sim_fw_demodulated:                     1
% 3.57/1.00  sim_bw_demodulated:                     1
% 3.57/1.00  sim_light_normalised:                   52
% 3.57/1.00  sim_joinable_taut:                      0
% 3.57/1.00  sim_joinable_simp:                      0
% 3.57/1.00  sim_ac_normalised:                      0
% 3.57/1.00  sim_smt_subsumption:                    0
% 3.57/1.00  
%------------------------------------------------------------------------------
