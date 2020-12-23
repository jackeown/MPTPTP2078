%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:40 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 335 expanded)
%              Number of clauses        :   32 (  80 expanded)
%              Number of leaves         :    9 (  77 expanded)
%              Depth                    :   21
%              Number of atoms          :  255 (1332 expanded)
%              Number of equality atoms :  159 ( 825 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f18])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK0(X0,X1,X2) = X1
      | sK0(X0,X1,X2) = X0
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f29,f22])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2
      | sK0(X0,X1,X2) = X1
      | sK0(X0,X1,X2) = X0
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f26,f38])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,conjecture,(
    ! [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) = k1_zfmisc_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) = k1_zfmisc_1(k1_tarski(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ? [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) != k1_zfmisc_1(k1_tarski(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,
    ( ? [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) != k1_zfmisc_1(k1_tarski(X0))
   => k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k1_zfmisc_1(k1_tarski(sK2)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k1_zfmisc_1(k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f20])).

fof(f37,plain,(
    k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k1_zfmisc_1(k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    k5_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_tarski(k1_tarski(sK2)),k1_tarski(k1_xboole_0))) != k1_zfmisc_1(k1_tarski(sK2)) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK0(X0,X1,X2) != X1
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2
      | sK0(X0,X1,X2) != X1
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f36])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK0(X0,X1,X2) != X0
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2
      | sK0(X0,X1,X2) != X0
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f27,f38])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1144,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(X0))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_tarski(X0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_11629,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK2))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK2))) ),
    inference(instantiation,[status(thm)],[c_1144])).

cnf(c_11,plain,
    ( r1_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11330,plain,
    ( r1_tarski(k1_xboole_0,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1042,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | sK0(X0,X1,X2) = X1
    | sK0(X0,X1,X2) = X0
    | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1048,plain,
    ( sK0(X0,X1,X2) = X1
    | sK0(X0,X1,X2) = X0
    | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1041,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2031,plain,
    ( sK0(X0,X1,k1_zfmisc_1(X2)) = X0
    | sK0(X0,X1,k1_zfmisc_1(X2)) = X1
    | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k1_zfmisc_1(X2)
    | r1_tarski(sK0(X0,X1,k1_zfmisc_1(X2)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1048,c_1041])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1038,plain,
    ( k1_tarski(X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3011,plain,
    ( sK0(X0,X1,k1_zfmisc_1(k1_tarski(X2))) = X0
    | sK0(X0,X1,k1_zfmisc_1(k1_tarski(X2))) = X1
    | sK0(X0,X1,k1_zfmisc_1(k1_tarski(X2))) = k1_tarski(X2)
    | sK0(X0,X1,k1_zfmisc_1(k1_tarski(X2))) = k1_xboole_0
    | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k1_zfmisc_1(k1_tarski(X2)) ),
    inference(superposition,[status(thm)],[c_2031,c_1038])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_tarski(k1_tarski(sK2)),k1_tarski(k1_xboole_0))) != k1_zfmisc_1(k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3631,plain,
    ( sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(X0))) = k1_tarski(X0)
    | sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(X0))) = k1_tarski(sK2)
    | sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(X0))) = k1_xboole_0
    | k1_zfmisc_1(k1_tarski(X0)) != k1_zfmisc_1(k1_tarski(sK2)) ),
    inference(superposition,[status(thm)],[c_3011,c_13])).

cnf(c_4263,plain,
    ( sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) = k1_tarski(sK2)
    | sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_3631])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | sK0(X0,X1,X2) != X1
    | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1050,plain,
    ( sK0(X0,X1,X2) != X1
    | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4289,plain,
    ( sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) = k1_xboole_0
    | k5_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_tarski(k1_tarski(sK2)),k1_tarski(k1_xboole_0))) = k1_zfmisc_1(k1_tarski(sK2))
    | r2_hidden(sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))),k1_zfmisc_1(k1_tarski(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4263,c_1050])).

cnf(c_4450,plain,
    ( sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))),k1_zfmisc_1(k1_tarski(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4289,c_13])).

cnf(c_4461,plain,
    ( sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) = k1_xboole_0
    | r2_hidden(k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4263,c_4450])).

cnf(c_4643,plain,
    ( sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) = k1_xboole_0
    | r1_tarski(k1_tarski(sK2),k1_tarski(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_4461])).

cnf(c_10,plain,
    ( r1_tarski(k1_tarski(X0),k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1040,plain,
    ( r1_tarski(k1_tarski(X0),k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4911,plain,
    ( sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4643,c_1040])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | sK0(X0,X1,X2) != X0
    | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1049,plain,
    ( sK0(X0,X1,X2) != X0
    | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4917,plain,
    ( k5_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_tarski(k1_tarski(sK2)),k1_tarski(k1_xboole_0))) = k1_zfmisc_1(k1_tarski(sK2))
    | r2_hidden(sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))),k1_zfmisc_1(k1_tarski(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4911,c_1049])).

cnf(c_4923,plain,
    ( k5_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_tarski(k1_tarski(sK2)),k1_tarski(k1_xboole_0))) = k1_zfmisc_1(k1_tarski(sK2))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4917,c_4911])).

cnf(c_4933,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK2)))
    | k5_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_tarski(k1_tarski(sK2)),k1_tarski(k1_xboole_0))) = k1_zfmisc_1(k1_tarski(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4923])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11629,c_11330,c_4933,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:04:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.50/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/0.98  
% 3.50/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/0.98  
% 3.50/0.98  ------  iProver source info
% 3.50/0.98  
% 3.50/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.50/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/0.98  git: non_committed_changes: false
% 3.50/0.98  git: last_make_outside_of_git: false
% 3.50/0.98  
% 3.50/0.98  ------ 
% 3.50/0.98  
% 3.50/0.98  ------ Input Options
% 3.50/0.98  
% 3.50/0.98  --out_options                           all
% 3.50/0.98  --tptp_safe_out                         true
% 3.50/0.98  --problem_path                          ""
% 3.50/0.98  --include_path                          ""
% 3.50/0.98  --clausifier                            res/vclausify_rel
% 3.50/0.98  --clausifier_options                    --mode clausify
% 3.50/0.98  --stdin                                 false
% 3.50/0.98  --stats_out                             all
% 3.50/0.98  
% 3.50/0.98  ------ General Options
% 3.50/0.98  
% 3.50/0.98  --fof                                   false
% 3.50/0.98  --time_out_real                         305.
% 3.50/0.98  --time_out_virtual                      -1.
% 3.50/0.98  --symbol_type_check                     false
% 3.50/0.98  --clausify_out                          false
% 3.50/0.98  --sig_cnt_out                           false
% 3.50/0.98  --trig_cnt_out                          false
% 3.50/0.98  --trig_cnt_out_tolerance                1.
% 3.50/0.98  --trig_cnt_out_sk_spl                   false
% 3.50/0.98  --abstr_cl_out                          false
% 3.50/0.98  
% 3.50/0.98  ------ Global Options
% 3.50/0.98  
% 3.50/0.98  --schedule                              default
% 3.50/0.98  --add_important_lit                     false
% 3.50/0.98  --prop_solver_per_cl                    1000
% 3.50/0.98  --min_unsat_core                        false
% 3.50/0.98  --soft_assumptions                      false
% 3.50/0.98  --soft_lemma_size                       3
% 3.50/0.98  --prop_impl_unit_size                   0
% 3.50/0.98  --prop_impl_unit                        []
% 3.50/0.98  --share_sel_clauses                     true
% 3.50/0.98  --reset_solvers                         false
% 3.50/0.98  --bc_imp_inh                            [conj_cone]
% 3.50/0.98  --conj_cone_tolerance                   3.
% 3.50/0.98  --extra_neg_conj                        none
% 3.50/0.98  --large_theory_mode                     true
% 3.50/0.98  --prolific_symb_bound                   200
% 3.50/0.98  --lt_threshold                          2000
% 3.50/0.98  --clause_weak_htbl                      true
% 3.50/0.98  --gc_record_bc_elim                     false
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing Options
% 3.50/0.98  
% 3.50/0.98  --preprocessing_flag                    true
% 3.50/0.98  --time_out_prep_mult                    0.1
% 3.50/0.98  --splitting_mode                        input
% 3.50/0.98  --splitting_grd                         true
% 3.50/0.98  --splitting_cvd                         false
% 3.50/0.98  --splitting_cvd_svl                     false
% 3.50/0.98  --splitting_nvd                         32
% 3.50/0.98  --sub_typing                            true
% 3.50/0.98  --prep_gs_sim                           true
% 3.50/0.98  --prep_unflatten                        true
% 3.50/0.98  --prep_res_sim                          true
% 3.50/0.98  --prep_upred                            true
% 3.50/0.98  --prep_sem_filter                       exhaustive
% 3.50/0.98  --prep_sem_filter_out                   false
% 3.50/0.98  --pred_elim                             true
% 3.50/0.98  --res_sim_input                         true
% 3.50/0.98  --eq_ax_congr_red                       true
% 3.50/0.98  --pure_diseq_elim                       true
% 3.50/0.98  --brand_transform                       false
% 3.50/0.98  --non_eq_to_eq                          false
% 3.50/0.98  --prep_def_merge                        true
% 3.50/0.98  --prep_def_merge_prop_impl              false
% 3.50/0.98  --prep_def_merge_mbd                    true
% 3.50/0.98  --prep_def_merge_tr_red                 false
% 3.50/0.98  --prep_def_merge_tr_cl                  false
% 3.50/0.98  --smt_preprocessing                     true
% 3.50/0.98  --smt_ac_axioms                         fast
% 3.50/0.98  --preprocessed_out                      false
% 3.50/0.98  --preprocessed_stats                    false
% 3.50/0.98  
% 3.50/0.98  ------ Abstraction refinement Options
% 3.50/0.98  
% 3.50/0.98  --abstr_ref                             []
% 3.50/0.98  --abstr_ref_prep                        false
% 3.50/0.98  --abstr_ref_until_sat                   false
% 3.50/0.98  --abstr_ref_sig_restrict                funpre
% 3.50/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.98  --abstr_ref_under                       []
% 3.50/0.98  
% 3.50/0.98  ------ SAT Options
% 3.50/0.98  
% 3.50/0.98  --sat_mode                              false
% 3.50/0.98  --sat_fm_restart_options                ""
% 3.50/0.98  --sat_gr_def                            false
% 3.50/0.98  --sat_epr_types                         true
% 3.50/0.98  --sat_non_cyclic_types                  false
% 3.50/0.98  --sat_finite_models                     false
% 3.50/0.98  --sat_fm_lemmas                         false
% 3.50/0.98  --sat_fm_prep                           false
% 3.50/0.98  --sat_fm_uc_incr                        true
% 3.50/0.98  --sat_out_model                         small
% 3.50/0.98  --sat_out_clauses                       false
% 3.50/0.98  
% 3.50/0.98  ------ QBF Options
% 3.50/0.98  
% 3.50/0.98  --qbf_mode                              false
% 3.50/0.98  --qbf_elim_univ                         false
% 3.50/0.98  --qbf_dom_inst                          none
% 3.50/0.98  --qbf_dom_pre_inst                      false
% 3.50/0.98  --qbf_sk_in                             false
% 3.50/0.98  --qbf_pred_elim                         true
% 3.50/0.98  --qbf_split                             512
% 3.50/0.98  
% 3.50/0.98  ------ BMC1 Options
% 3.50/0.98  
% 3.50/0.98  --bmc1_incremental                      false
% 3.50/0.98  --bmc1_axioms                           reachable_all
% 3.50/0.98  --bmc1_min_bound                        0
% 3.50/0.98  --bmc1_max_bound                        -1
% 3.50/0.98  --bmc1_max_bound_default                -1
% 3.50/0.98  --bmc1_symbol_reachability              true
% 3.50/0.98  --bmc1_property_lemmas                  false
% 3.50/0.98  --bmc1_k_induction                      false
% 3.50/0.98  --bmc1_non_equiv_states                 false
% 3.50/0.98  --bmc1_deadlock                         false
% 3.50/0.98  --bmc1_ucm                              false
% 3.50/0.98  --bmc1_add_unsat_core                   none
% 3.50/0.98  --bmc1_unsat_core_children              false
% 3.50/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.98  --bmc1_out_stat                         full
% 3.50/0.98  --bmc1_ground_init                      false
% 3.50/0.98  --bmc1_pre_inst_next_state              false
% 3.50/0.98  --bmc1_pre_inst_state                   false
% 3.50/0.98  --bmc1_pre_inst_reach_state             false
% 3.50/0.98  --bmc1_out_unsat_core                   false
% 3.50/0.98  --bmc1_aig_witness_out                  false
% 3.50/0.98  --bmc1_verbose                          false
% 3.50/0.98  --bmc1_dump_clauses_tptp                false
% 3.50/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.98  --bmc1_dump_file                        -
% 3.50/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.98  --bmc1_ucm_extend_mode                  1
% 3.50/0.98  --bmc1_ucm_init_mode                    2
% 3.50/0.98  --bmc1_ucm_cone_mode                    none
% 3.50/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.98  --bmc1_ucm_relax_model                  4
% 3.50/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.98  --bmc1_ucm_layered_model                none
% 3.50/0.98  --bmc1_ucm_max_lemma_size               10
% 3.50/0.98  
% 3.50/0.98  ------ AIG Options
% 3.50/0.98  
% 3.50/0.98  --aig_mode                              false
% 3.50/0.98  
% 3.50/0.98  ------ Instantiation Options
% 3.50/0.98  
% 3.50/0.98  --instantiation_flag                    true
% 3.50/0.98  --inst_sos_flag                         false
% 3.50/0.98  --inst_sos_phase                        true
% 3.50/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.98  --inst_lit_sel_side                     num_symb
% 3.50/0.98  --inst_solver_per_active                1400
% 3.50/0.98  --inst_solver_calls_frac                1.
% 3.50/0.98  --inst_passive_queue_type               priority_queues
% 3.50/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.98  --inst_passive_queues_freq              [25;2]
% 3.50/0.98  --inst_dismatching                      true
% 3.50/0.98  --inst_eager_unprocessed_to_passive     true
% 3.50/0.98  --inst_prop_sim_given                   true
% 3.50/0.98  --inst_prop_sim_new                     false
% 3.50/0.98  --inst_subs_new                         false
% 3.50/0.98  --inst_eq_res_simp                      false
% 3.50/0.98  --inst_subs_given                       false
% 3.50/0.98  --inst_orphan_elimination               true
% 3.50/0.98  --inst_learning_loop_flag               true
% 3.50/0.98  --inst_learning_start                   3000
% 3.50/0.98  --inst_learning_factor                  2
% 3.50/0.98  --inst_start_prop_sim_after_learn       3
% 3.50/0.98  --inst_sel_renew                        solver
% 3.50/0.98  --inst_lit_activity_flag                true
% 3.50/0.98  --inst_restr_to_given                   false
% 3.50/0.98  --inst_activity_threshold               500
% 3.50/0.98  --inst_out_proof                        true
% 3.50/0.98  
% 3.50/0.98  ------ Resolution Options
% 3.50/0.98  
% 3.50/0.98  --resolution_flag                       true
% 3.50/0.98  --res_lit_sel                           adaptive
% 3.50/0.98  --res_lit_sel_side                      none
% 3.50/0.98  --res_ordering                          kbo
% 3.50/0.98  --res_to_prop_solver                    active
% 3.50/0.98  --res_prop_simpl_new                    false
% 3.50/0.98  --res_prop_simpl_given                  true
% 3.50/0.98  --res_passive_queue_type                priority_queues
% 3.50/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.98  --res_passive_queues_freq               [15;5]
% 3.50/0.98  --res_forward_subs                      full
% 3.50/0.98  --res_backward_subs                     full
% 3.50/0.98  --res_forward_subs_resolution           true
% 3.50/0.98  --res_backward_subs_resolution          true
% 3.50/0.98  --res_orphan_elimination                true
% 3.50/0.98  --res_time_limit                        2.
% 3.50/0.98  --res_out_proof                         true
% 3.50/0.98  
% 3.50/0.98  ------ Superposition Options
% 3.50/0.98  
% 3.50/0.98  --superposition_flag                    true
% 3.50/0.98  --sup_passive_queue_type                priority_queues
% 3.50/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.98  --demod_completeness_check              fast
% 3.50/0.98  --demod_use_ground                      true
% 3.50/0.98  --sup_to_prop_solver                    passive
% 3.50/0.98  --sup_prop_simpl_new                    true
% 3.50/0.98  --sup_prop_simpl_given                  true
% 3.50/0.98  --sup_fun_splitting                     false
% 3.50/0.98  --sup_smt_interval                      50000
% 3.50/0.98  
% 3.50/0.98  ------ Superposition Simplification Setup
% 3.50/0.98  
% 3.50/0.98  --sup_indices_passive                   []
% 3.50/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.98  --sup_full_bw                           [BwDemod]
% 3.50/0.98  --sup_immed_triv                        [TrivRules]
% 3.50/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.98  --sup_immed_bw_main                     []
% 3.50/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.98  
% 3.50/0.98  ------ Combination Options
% 3.50/0.98  
% 3.50/0.98  --comb_res_mult                         3
% 3.50/0.98  --comb_sup_mult                         2
% 3.50/0.98  --comb_inst_mult                        10
% 3.50/0.98  
% 3.50/0.98  ------ Debug Options
% 3.50/0.98  
% 3.50/0.98  --dbg_backtrace                         false
% 3.50/0.98  --dbg_dump_prop_clauses                 false
% 3.50/0.98  --dbg_dump_prop_clauses_file            -
% 3.50/0.98  --dbg_out_stat                          false
% 3.50/0.98  ------ Parsing...
% 3.50/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/0.98  
% 3.50/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.98  ------ Proving...
% 3.50/0.98  ------ Problem Properties 
% 3.50/0.98  
% 3.50/0.98  
% 3.50/0.98  clauses                                 14
% 3.50/0.98  conjectures                             1
% 3.50/0.98  EPR                                     0
% 3.50/0.98  Horn                                    10
% 3.50/0.98  unary                                   5
% 3.50/0.98  binary                                  2
% 3.50/0.98  lits                                    31
% 3.50/0.98  lits eq                                 14
% 3.50/0.98  fd_pure                                 0
% 3.50/0.98  fd_pseudo                               0
% 3.50/0.98  fd_cond                                 0
% 3.50/0.98  fd_pseudo_cond                          6
% 3.50/0.98  AC symbols                              0
% 3.50/0.98  
% 3.50/0.98  ------ Schedule dynamic 5 is on 
% 3.50/0.98  
% 3.50/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.50/0.98  
% 3.50/0.98  
% 3.50/0.98  ------ 
% 3.50/0.98  Current options:
% 3.50/0.98  ------ 
% 3.50/0.98  
% 3.50/0.98  ------ Input Options
% 3.50/0.98  
% 3.50/0.98  --out_options                           all
% 3.50/0.98  --tptp_safe_out                         true
% 3.50/0.98  --problem_path                          ""
% 3.50/0.98  --include_path                          ""
% 3.50/0.98  --clausifier                            res/vclausify_rel
% 3.50/0.98  --clausifier_options                    --mode clausify
% 3.50/0.98  --stdin                                 false
% 3.50/0.98  --stats_out                             all
% 3.50/0.98  
% 3.50/0.98  ------ General Options
% 3.50/0.98  
% 3.50/0.98  --fof                                   false
% 3.50/0.99  --time_out_real                         305.
% 3.50/0.99  --time_out_virtual                      -1.
% 3.50/0.99  --symbol_type_check                     false
% 3.50/0.99  --clausify_out                          false
% 3.50/0.99  --sig_cnt_out                           false
% 3.50/0.99  --trig_cnt_out                          false
% 3.50/0.99  --trig_cnt_out_tolerance                1.
% 3.50/0.99  --trig_cnt_out_sk_spl                   false
% 3.50/0.99  --abstr_cl_out                          false
% 3.50/0.99  
% 3.50/0.99  ------ Global Options
% 3.50/0.99  
% 3.50/0.99  --schedule                              default
% 3.50/0.99  --add_important_lit                     false
% 3.50/0.99  --prop_solver_per_cl                    1000
% 3.50/0.99  --min_unsat_core                        false
% 3.50/0.99  --soft_assumptions                      false
% 3.50/0.99  --soft_lemma_size                       3
% 3.50/0.99  --prop_impl_unit_size                   0
% 3.50/0.99  --prop_impl_unit                        []
% 3.50/0.99  --share_sel_clauses                     true
% 3.50/0.99  --reset_solvers                         false
% 3.50/0.99  --bc_imp_inh                            [conj_cone]
% 3.50/0.99  --conj_cone_tolerance                   3.
% 3.50/0.99  --extra_neg_conj                        none
% 3.50/0.99  --large_theory_mode                     true
% 3.50/0.99  --prolific_symb_bound                   200
% 3.50/0.99  --lt_threshold                          2000
% 3.50/0.99  --clause_weak_htbl                      true
% 3.50/0.99  --gc_record_bc_elim                     false
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing Options
% 3.50/0.99  
% 3.50/0.99  --preprocessing_flag                    true
% 3.50/0.99  --time_out_prep_mult                    0.1
% 3.50/0.99  --splitting_mode                        input
% 3.50/0.99  --splitting_grd                         true
% 3.50/0.99  --splitting_cvd                         false
% 3.50/0.99  --splitting_cvd_svl                     false
% 3.50/0.99  --splitting_nvd                         32
% 3.50/0.99  --sub_typing                            true
% 3.50/0.99  --prep_gs_sim                           true
% 3.50/0.99  --prep_unflatten                        true
% 3.50/0.99  --prep_res_sim                          true
% 3.50/0.99  --prep_upred                            true
% 3.50/0.99  --prep_sem_filter                       exhaustive
% 3.50/0.99  --prep_sem_filter_out                   false
% 3.50/0.99  --pred_elim                             true
% 3.50/0.99  --res_sim_input                         true
% 3.50/0.99  --eq_ax_congr_red                       true
% 3.50/0.99  --pure_diseq_elim                       true
% 3.50/0.99  --brand_transform                       false
% 3.50/0.99  --non_eq_to_eq                          false
% 3.50/0.99  --prep_def_merge                        true
% 3.50/0.99  --prep_def_merge_prop_impl              false
% 3.50/0.99  --prep_def_merge_mbd                    true
% 3.50/0.99  --prep_def_merge_tr_red                 false
% 3.50/0.99  --prep_def_merge_tr_cl                  false
% 3.50/0.99  --smt_preprocessing                     true
% 3.50/0.99  --smt_ac_axioms                         fast
% 3.50/0.99  --preprocessed_out                      false
% 3.50/0.99  --preprocessed_stats                    false
% 3.50/0.99  
% 3.50/0.99  ------ Abstraction refinement Options
% 3.50/0.99  
% 3.50/0.99  --abstr_ref                             []
% 3.50/0.99  --abstr_ref_prep                        false
% 3.50/0.99  --abstr_ref_until_sat                   false
% 3.50/0.99  --abstr_ref_sig_restrict                funpre
% 3.50/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.99  --abstr_ref_under                       []
% 3.50/0.99  
% 3.50/0.99  ------ SAT Options
% 3.50/0.99  
% 3.50/0.99  --sat_mode                              false
% 3.50/0.99  --sat_fm_restart_options                ""
% 3.50/0.99  --sat_gr_def                            false
% 3.50/0.99  --sat_epr_types                         true
% 3.50/0.99  --sat_non_cyclic_types                  false
% 3.50/0.99  --sat_finite_models                     false
% 3.50/0.99  --sat_fm_lemmas                         false
% 3.50/0.99  --sat_fm_prep                           false
% 3.50/0.99  --sat_fm_uc_incr                        true
% 3.50/0.99  --sat_out_model                         small
% 3.50/0.99  --sat_out_clauses                       false
% 3.50/0.99  
% 3.50/0.99  ------ QBF Options
% 3.50/0.99  
% 3.50/0.99  --qbf_mode                              false
% 3.50/0.99  --qbf_elim_univ                         false
% 3.50/0.99  --qbf_dom_inst                          none
% 3.50/0.99  --qbf_dom_pre_inst                      false
% 3.50/0.99  --qbf_sk_in                             false
% 3.50/0.99  --qbf_pred_elim                         true
% 3.50/0.99  --qbf_split                             512
% 3.50/0.99  
% 3.50/0.99  ------ BMC1 Options
% 3.50/0.99  
% 3.50/0.99  --bmc1_incremental                      false
% 3.50/0.99  --bmc1_axioms                           reachable_all
% 3.50/0.99  --bmc1_min_bound                        0
% 3.50/0.99  --bmc1_max_bound                        -1
% 3.50/0.99  --bmc1_max_bound_default                -1
% 3.50/0.99  --bmc1_symbol_reachability              true
% 3.50/0.99  --bmc1_property_lemmas                  false
% 3.50/0.99  --bmc1_k_induction                      false
% 3.50/0.99  --bmc1_non_equiv_states                 false
% 3.50/0.99  --bmc1_deadlock                         false
% 3.50/0.99  --bmc1_ucm                              false
% 3.50/0.99  --bmc1_add_unsat_core                   none
% 3.50/0.99  --bmc1_unsat_core_children              false
% 3.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.99  --bmc1_out_stat                         full
% 3.50/0.99  --bmc1_ground_init                      false
% 3.50/0.99  --bmc1_pre_inst_next_state              false
% 3.50/0.99  --bmc1_pre_inst_state                   false
% 3.50/0.99  --bmc1_pre_inst_reach_state             false
% 3.50/0.99  --bmc1_out_unsat_core                   false
% 3.50/0.99  --bmc1_aig_witness_out                  false
% 3.50/0.99  --bmc1_verbose                          false
% 3.50/0.99  --bmc1_dump_clauses_tptp                false
% 3.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.99  --bmc1_dump_file                        -
% 3.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.99  --bmc1_ucm_extend_mode                  1
% 3.50/0.99  --bmc1_ucm_init_mode                    2
% 3.50/0.99  --bmc1_ucm_cone_mode                    none
% 3.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.99  --bmc1_ucm_relax_model                  4
% 3.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.99  --bmc1_ucm_layered_model                none
% 3.50/0.99  --bmc1_ucm_max_lemma_size               10
% 3.50/0.99  
% 3.50/0.99  ------ AIG Options
% 3.50/0.99  
% 3.50/0.99  --aig_mode                              false
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation Options
% 3.50/0.99  
% 3.50/0.99  --instantiation_flag                    true
% 3.50/0.99  --inst_sos_flag                         false
% 3.50/0.99  --inst_sos_phase                        true
% 3.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel_side                     none
% 3.50/0.99  --inst_solver_per_active                1400
% 3.50/0.99  --inst_solver_calls_frac                1.
% 3.50/0.99  --inst_passive_queue_type               priority_queues
% 3.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.99  --inst_passive_queues_freq              [25;2]
% 3.50/0.99  --inst_dismatching                      true
% 3.50/0.99  --inst_eager_unprocessed_to_passive     true
% 3.50/0.99  --inst_prop_sim_given                   true
% 3.50/0.99  --inst_prop_sim_new                     false
% 3.50/0.99  --inst_subs_new                         false
% 3.50/0.99  --inst_eq_res_simp                      false
% 3.50/0.99  --inst_subs_given                       false
% 3.50/0.99  --inst_orphan_elimination               true
% 3.50/0.99  --inst_learning_loop_flag               true
% 3.50/0.99  --inst_learning_start                   3000
% 3.50/0.99  --inst_learning_factor                  2
% 3.50/0.99  --inst_start_prop_sim_after_learn       3
% 3.50/0.99  --inst_sel_renew                        solver
% 3.50/0.99  --inst_lit_activity_flag                true
% 3.50/0.99  --inst_restr_to_given                   false
% 3.50/0.99  --inst_activity_threshold               500
% 3.50/0.99  --inst_out_proof                        true
% 3.50/0.99  
% 3.50/0.99  ------ Resolution Options
% 3.50/0.99  
% 3.50/0.99  --resolution_flag                       false
% 3.50/0.99  --res_lit_sel                           adaptive
% 3.50/0.99  --res_lit_sel_side                      none
% 3.50/0.99  --res_ordering                          kbo
% 3.50/0.99  --res_to_prop_solver                    active
% 3.50/0.99  --res_prop_simpl_new                    false
% 3.50/0.99  --res_prop_simpl_given                  true
% 3.50/0.99  --res_passive_queue_type                priority_queues
% 3.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.99  --res_passive_queues_freq               [15;5]
% 3.50/0.99  --res_forward_subs                      full
% 3.50/0.99  --res_backward_subs                     full
% 3.50/0.99  --res_forward_subs_resolution           true
% 3.50/0.99  --res_backward_subs_resolution          true
% 3.50/0.99  --res_orphan_elimination                true
% 3.50/0.99  --res_time_limit                        2.
% 3.50/0.99  --res_out_proof                         true
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Options
% 3.50/0.99  
% 3.50/0.99  --superposition_flag                    true
% 3.50/0.99  --sup_passive_queue_type                priority_queues
% 3.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.99  --demod_completeness_check              fast
% 3.50/0.99  --demod_use_ground                      true
% 3.50/0.99  --sup_to_prop_solver                    passive
% 3.50/0.99  --sup_prop_simpl_new                    true
% 3.50/0.99  --sup_prop_simpl_given                  true
% 3.50/0.99  --sup_fun_splitting                     false
% 3.50/0.99  --sup_smt_interval                      50000
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Simplification Setup
% 3.50/0.99  
% 3.50/0.99  --sup_indices_passive                   []
% 3.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_full_bw                           [BwDemod]
% 3.50/0.99  --sup_immed_triv                        [TrivRules]
% 3.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_immed_bw_main                     []
% 3.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  
% 3.50/0.99  ------ Combination Options
% 3.50/0.99  
% 3.50/0.99  --comb_res_mult                         3
% 3.50/0.99  --comb_sup_mult                         2
% 3.50/0.99  --comb_inst_mult                        10
% 3.50/0.99  
% 3.50/0.99  ------ Debug Options
% 3.50/0.99  
% 3.50/0.99  --dbg_backtrace                         false
% 3.50/0.99  --dbg_dump_prop_clauses                 false
% 3.50/0.99  --dbg_dump_prop_clauses_file            -
% 3.50/0.99  --dbg_out_stat                          false
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  ------ Proving...
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS status Theorem for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  fof(f4,axiom,(
% 3.50/0.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f14,plain,(
% 3.50/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.50/0.99    inference(nnf_transformation,[],[f4])).
% 3.50/0.99  
% 3.50/0.99  fof(f15,plain,(
% 3.50/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.50/0.99    inference(rectify,[],[f14])).
% 3.50/0.99  
% 3.50/0.99  fof(f16,plain,(
% 3.50/0.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f17,plain,(
% 3.50/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).
% 3.50/0.99  
% 3.50/0.99  fof(f31,plain,(
% 3.50/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.50/0.99    inference(cnf_transformation,[],[f17])).
% 3.50/0.99  
% 3.50/0.99  fof(f51,plain,(
% 3.50/0.99    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.50/0.99    inference(equality_resolution,[],[f31])).
% 3.50/0.99  
% 3.50/0.99  fof(f5,axiom,(
% 3.50/0.99    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f18,plain,(
% 3.50/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.50/0.99    inference(nnf_transformation,[],[f5])).
% 3.50/0.99  
% 3.50/0.99  fof(f19,plain,(
% 3.50/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.50/0.99    inference(flattening,[],[f18])).
% 3.50/0.99  
% 3.50/0.99  fof(f35,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 3.50/0.99    inference(cnf_transformation,[],[f19])).
% 3.50/0.99  
% 3.50/0.99  fof(f54,plain,(
% 3.50/0.99    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 3.50/0.99    inference(equality_resolution,[],[f35])).
% 3.50/0.99  
% 3.50/0.99  fof(f2,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f9,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.50/0.99    inference(nnf_transformation,[],[f2])).
% 3.50/0.99  
% 3.50/0.99  fof(f10,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.50/0.99    inference(flattening,[],[f9])).
% 3.50/0.99  
% 3.50/0.99  fof(f11,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.50/0.99    inference(rectify,[],[f10])).
% 3.50/0.99  
% 3.50/0.99  fof(f12,plain,(
% 3.50/0.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f13,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 3.50/0.99  
% 3.50/0.99  fof(f26,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f13])).
% 3.50/0.99  
% 3.50/0.99  fof(f3,axiom,(
% 3.50/0.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f29,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f3])).
% 3.50/0.99  
% 3.50/0.99  fof(f1,axiom,(
% 3.50/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f22,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f1])).
% 3.50/0.99  
% 3.50/0.99  fof(f38,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1)) )),
% 3.50/0.99    inference(definition_unfolding,[],[f29,f22])).
% 3.50/0.99  
% 3.50/0.99  fof(f41,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2 | sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.50/0.99    inference(definition_unfolding,[],[f26,f38])).
% 3.50/0.99  
% 3.50/0.99  fof(f30,plain,(
% 3.50/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.50/0.99    inference(cnf_transformation,[],[f17])).
% 3.50/0.99  
% 3.50/0.99  fof(f52,plain,(
% 3.50/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.50/0.99    inference(equality_resolution,[],[f30])).
% 3.50/0.99  
% 3.50/0.99  fof(f34,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f19])).
% 3.50/0.99  
% 3.50/0.99  fof(f6,conjecture,(
% 3.50/0.99    ! [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) = k1_zfmisc_1(k1_tarski(X0))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f7,negated_conjecture,(
% 3.50/0.99    ~! [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) = k1_zfmisc_1(k1_tarski(X0))),
% 3.50/0.99    inference(negated_conjecture,[],[f6])).
% 3.50/0.99  
% 3.50/0.99  fof(f8,plain,(
% 3.50/0.99    ? [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) != k1_zfmisc_1(k1_tarski(X0))),
% 3.50/0.99    inference(ennf_transformation,[],[f7])).
% 3.50/0.99  
% 3.50/0.99  fof(f20,plain,(
% 3.50/0.99    ? [X0] : k2_tarski(k1_xboole_0,k1_tarski(X0)) != k1_zfmisc_1(k1_tarski(X0)) => k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k1_zfmisc_1(k1_tarski(sK2))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f21,plain,(
% 3.50/0.99    k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k1_zfmisc_1(k1_tarski(sK2))),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f8,f20])).
% 3.50/0.99  
% 3.50/0.99  fof(f37,plain,(
% 3.50/0.99    k2_tarski(k1_xboole_0,k1_tarski(sK2)) != k1_zfmisc_1(k1_tarski(sK2))),
% 3.50/0.99    inference(cnf_transformation,[],[f21])).
% 3.50/0.99  
% 3.50/0.99  fof(f45,plain,(
% 3.50/0.99    k5_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_tarski(k1_tarski(sK2)),k1_tarski(k1_xboole_0))) != k1_zfmisc_1(k1_tarski(sK2))),
% 3.50/0.99    inference(definition_unfolding,[],[f37,f38])).
% 3.50/0.99  
% 3.50/0.99  fof(f28,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK0(X0,X1,X2) != X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f13])).
% 3.50/0.99  
% 3.50/0.99  fof(f39,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2 | sK0(X0,X1,X2) != X1 | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.50/0.99    inference(definition_unfolding,[],[f28,f38])).
% 3.50/0.99  
% 3.50/0.99  fof(f36,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 3.50/0.99    inference(cnf_transformation,[],[f19])).
% 3.50/0.99  
% 3.50/0.99  fof(f53,plain,(
% 3.50/0.99    ( ! [X1] : (r1_tarski(k1_tarski(X1),k1_tarski(X1))) )),
% 3.50/0.99    inference(equality_resolution,[],[f36])).
% 3.50/0.99  
% 3.50/0.99  fof(f27,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK0(X0,X1,X2) != X0 | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f13])).
% 3.50/0.99  
% 3.50/0.99  fof(f40,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2 | sK0(X0,X1,X2) != X0 | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.50/0.99    inference(definition_unfolding,[],[f27,f38])).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1144,plain,
% 3.50/0.99      ( ~ r1_tarski(k1_xboole_0,k1_tarski(X0))
% 3.50/0.99      | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_tarski(X0))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11629,plain,
% 3.50/0.99      ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK2))
% 3.50/0.99      | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK2))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1144]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11,plain,
% 3.50/0.99      ( r1_tarski(k1_xboole_0,k1_tarski(X0)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11330,plain,
% 3.50/0.99      ( r1_tarski(k1_xboole_0,k1_tarski(sK2)) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1042,plain,
% 3.50/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.50/0.99      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2,plain,
% 3.50/0.99      ( r2_hidden(sK0(X0,X1,X2),X2)
% 3.50/0.99      | sK0(X0,X1,X2) = X1
% 3.50/0.99      | sK0(X0,X1,X2) = X0
% 3.50/0.99      | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2 ),
% 3.50/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1048,plain,
% 3.50/0.99      ( sK0(X0,X1,X2) = X1
% 3.50/0.99      | sK0(X0,X1,X2) = X0
% 3.50/0.99      | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2
% 3.50/0.99      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9,plain,
% 3.50/0.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1041,plain,
% 3.50/0.99      ( r1_tarski(X0,X1) = iProver_top
% 3.50/0.99      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2031,plain,
% 3.50/0.99      ( sK0(X0,X1,k1_zfmisc_1(X2)) = X0
% 3.50/0.99      | sK0(X0,X1,k1_zfmisc_1(X2)) = X1
% 3.50/0.99      | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k1_zfmisc_1(X2)
% 3.50/0.99      | r1_tarski(sK0(X0,X1,k1_zfmisc_1(X2)),X2) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1048,c_1041]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_12,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,k1_tarski(X1))
% 3.50/0.99      | k1_tarski(X1) = X0
% 3.50/0.99      | k1_xboole_0 = X0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1038,plain,
% 3.50/0.99      ( k1_tarski(X0) = X1
% 3.50/0.99      | k1_xboole_0 = X1
% 3.50/0.99      | r1_tarski(X1,k1_tarski(X0)) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3011,plain,
% 3.50/0.99      ( sK0(X0,X1,k1_zfmisc_1(k1_tarski(X2))) = X0
% 3.50/0.99      | sK0(X0,X1,k1_zfmisc_1(k1_tarski(X2))) = X1
% 3.50/0.99      | sK0(X0,X1,k1_zfmisc_1(k1_tarski(X2))) = k1_tarski(X2)
% 3.50/0.99      | sK0(X0,X1,k1_zfmisc_1(k1_tarski(X2))) = k1_xboole_0
% 3.50/0.99      | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k1_zfmisc_1(k1_tarski(X2)) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_2031,c_1038]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13,negated_conjecture,
% 3.50/0.99      ( k5_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_tarski(k1_tarski(sK2)),k1_tarski(k1_xboole_0))) != k1_zfmisc_1(k1_tarski(sK2)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3631,plain,
% 3.50/0.99      ( sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(X0))) = k1_tarski(X0)
% 3.50/0.99      | sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(X0))) = k1_tarski(sK2)
% 3.50/0.99      | sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(X0))) = k1_xboole_0
% 3.50/0.99      | k1_zfmisc_1(k1_tarski(X0)) != k1_zfmisc_1(k1_tarski(sK2)) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_3011,c_13]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4263,plain,
% 3.50/0.99      ( sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) = k1_tarski(sK2)
% 3.50/0.99      | sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) = k1_xboole_0 ),
% 3.50/0.99      inference(equality_resolution,[status(thm)],[c_3631]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_0,plain,
% 3.50/0.99      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.50/0.99      | sK0(X0,X1,X2) != X1
% 3.50/0.99      | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2 ),
% 3.50/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1050,plain,
% 3.50/0.99      ( sK0(X0,X1,X2) != X1
% 3.50/0.99      | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2
% 3.50/0.99      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4289,plain,
% 3.50/0.99      ( sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) = k1_xboole_0
% 3.50/0.99      | k5_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_tarski(k1_tarski(sK2)),k1_tarski(k1_xboole_0))) = k1_zfmisc_1(k1_tarski(sK2))
% 3.50/0.99      | r2_hidden(sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))),k1_zfmisc_1(k1_tarski(sK2))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_4263,c_1050]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4450,plain,
% 3.50/0.99      ( sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) = k1_xboole_0
% 3.50/0.99      | r2_hidden(sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))),k1_zfmisc_1(k1_tarski(sK2))) != iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_4289,c_13]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4461,plain,
% 3.50/0.99      ( sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) = k1_xboole_0
% 3.50/0.99      | r2_hidden(k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_4263,c_4450]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4643,plain,
% 3.50/0.99      ( sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) = k1_xboole_0
% 3.50/0.99      | r1_tarski(k1_tarski(sK2),k1_tarski(sK2)) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1042,c_4461]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10,plain,
% 3.50/0.99      ( r1_tarski(k1_tarski(X0),k1_tarski(X0)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1040,plain,
% 3.50/0.99      ( r1_tarski(k1_tarski(X0),k1_tarski(X0)) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4911,plain,
% 3.50/0.99      ( sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))) = k1_xboole_0 ),
% 3.50/0.99      inference(forward_subsumption_resolution,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_4643,c_1040]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1,plain,
% 3.50/0.99      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.50/0.99      | sK0(X0,X1,X2) != X0
% 3.50/0.99      | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2 ),
% 3.50/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1049,plain,
% 3.50/0.99      ( sK0(X0,X1,X2) != X0
% 3.50/0.99      | k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = X2
% 3.50/0.99      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4917,plain,
% 3.50/0.99      ( k5_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_tarski(k1_tarski(sK2)),k1_tarski(k1_xboole_0))) = k1_zfmisc_1(k1_tarski(sK2))
% 3.50/0.99      | r2_hidden(sK0(k1_xboole_0,k1_tarski(sK2),k1_zfmisc_1(k1_tarski(sK2))),k1_zfmisc_1(k1_tarski(sK2))) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_4911,c_1049]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4923,plain,
% 3.50/0.99      ( k5_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_tarski(k1_tarski(sK2)),k1_tarski(k1_xboole_0))) = k1_zfmisc_1(k1_tarski(sK2))
% 3.50/0.99      | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK2))) != iProver_top ),
% 3.50/0.99      inference(light_normalisation,[status(thm)],[c_4917,c_4911]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4933,plain,
% 3.50/0.99      ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_tarski(sK2)))
% 3.50/0.99      | k5_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_tarski(k1_tarski(sK2)),k1_tarski(k1_xboole_0))) = k1_zfmisc_1(k1_tarski(sK2)) ),
% 3.50/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4923]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(contradiction,plain,
% 3.50/0.99      ( $false ),
% 3.50/0.99      inference(minisat,[status(thm)],[c_11629,c_11330,c_4933,c_13]) ).
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  ------                               Statistics
% 3.50/0.99  
% 3.50/0.99  ------ General
% 3.50/0.99  
% 3.50/0.99  abstr_ref_over_cycles:                  0
% 3.50/0.99  abstr_ref_under_cycles:                 0
% 3.50/0.99  gc_basic_clause_elim:                   0
% 3.50/0.99  forced_gc_time:                         0
% 3.50/0.99  parsing_time:                           0.008
% 3.50/0.99  unif_index_cands_time:                  0.
% 3.50/0.99  unif_index_add_time:                    0.
% 3.50/0.99  orderings_time:                         0.
% 3.50/0.99  out_proof_time:                         0.023
% 3.50/0.99  total_time:                             0.354
% 3.50/0.99  num_of_symbols:                         41
% 3.50/0.99  num_of_terms:                           8178
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing
% 3.50/0.99  
% 3.50/0.99  num_of_splits:                          0
% 3.50/0.99  num_of_split_atoms:                     0
% 3.50/0.99  num_of_reused_defs:                     0
% 3.50/0.99  num_eq_ax_congr_red:                    10
% 3.50/0.99  num_of_sem_filtered_clauses:            1
% 3.50/0.99  num_of_subtypes:                        0
% 3.50/0.99  monotx_restored_types:                  0
% 3.50/0.99  sat_num_of_epr_types:                   0
% 3.50/0.99  sat_num_of_non_cyclic_types:            0
% 3.50/0.99  sat_guarded_non_collapsed_types:        0
% 3.50/0.99  num_pure_diseq_elim:                    0
% 3.50/0.99  simp_replaced_by:                       0
% 3.50/0.99  res_preprocessed:                       59
% 3.50/0.99  prep_upred:                             0
% 3.50/0.99  prep_unflattend:                        44
% 3.50/0.99  smt_new_axioms:                         0
% 3.50/0.99  pred_elim_cands:                        2
% 3.50/0.99  pred_elim:                              0
% 3.50/0.99  pred_elim_cl:                           0
% 3.50/0.99  pred_elim_cycles:                       2
% 3.50/0.99  merged_defs:                            6
% 3.50/0.99  merged_defs_ncl:                        0
% 3.50/0.99  bin_hyper_res:                          6
% 3.50/0.99  prep_cycles:                            3
% 3.50/0.99  pred_elim_time:                         0.01
% 3.50/0.99  splitting_time:                         0.
% 3.50/0.99  sem_filter_time:                        0.
% 3.50/0.99  monotx_time:                            0.001
% 3.50/0.99  subtype_inf_time:                       0.
% 3.50/0.99  
% 3.50/0.99  ------ Problem properties
% 3.50/0.99  
% 3.50/0.99  clauses:                                14
% 3.50/0.99  conjectures:                            1
% 3.50/0.99  epr:                                    0
% 3.50/0.99  horn:                                   10
% 3.50/0.99  ground:                                 1
% 3.50/0.99  unary:                                  5
% 3.50/0.99  binary:                                 2
% 3.50/0.99  lits:                                   31
% 3.50/0.99  lits_eq:                                14
% 3.50/0.99  fd_pure:                                0
% 3.50/0.99  fd_pseudo:                              0
% 3.50/0.99  fd_cond:                                0
% 3.50/0.99  fd_pseudo_cond:                         6
% 3.50/0.99  ac_symbols:                             0
% 3.50/0.99  
% 3.50/0.99  ------ Propositional Solver
% 3.50/0.99  
% 3.50/0.99  prop_solver_calls:                      23
% 3.50/0.99  prop_fast_solver_calls:                 709
% 3.50/0.99  smt_solver_calls:                       0
% 3.50/0.99  smt_fast_solver_calls:                  0
% 3.50/0.99  prop_num_of_clauses:                    2224
% 3.50/0.99  prop_preprocess_simplified:             5697
% 3.50/0.99  prop_fo_subsumed:                       1
% 3.50/0.99  prop_solver_time:                       0.
% 3.50/0.99  smt_solver_time:                        0.
% 3.50/0.99  smt_fast_solver_time:                   0.
% 3.50/0.99  prop_fast_solver_time:                  0.
% 3.50/0.99  prop_unsat_core_time:                   0.
% 3.50/0.99  
% 3.50/0.99  ------ QBF
% 3.50/0.99  
% 3.50/0.99  qbf_q_res:                              0
% 3.50/0.99  qbf_num_tautologies:                    0
% 3.50/0.99  qbf_prep_cycles:                        0
% 3.50/0.99  
% 3.50/0.99  ------ BMC1
% 3.50/0.99  
% 3.50/0.99  bmc1_current_bound:                     -1
% 3.50/0.99  bmc1_last_solved_bound:                 -1
% 3.50/0.99  bmc1_unsat_core_size:                   -1
% 3.50/0.99  bmc1_unsat_core_parents_size:           -1
% 3.50/0.99  bmc1_merge_next_fun:                    0
% 3.50/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation
% 3.50/0.99  
% 3.50/0.99  inst_num_of_clauses:                    557
% 3.50/0.99  inst_num_in_passive:                    221
% 3.50/0.99  inst_num_in_active:                     247
% 3.50/0.99  inst_num_in_unprocessed:                88
% 3.50/0.99  inst_num_of_loops:                      311
% 3.50/0.99  inst_num_of_learning_restarts:          0
% 3.50/0.99  inst_num_moves_active_passive:          62
% 3.50/0.99  inst_lit_activity:                      0
% 3.50/0.99  inst_lit_activity_moves:                0
% 3.50/0.99  inst_num_tautologies:                   0
% 3.50/0.99  inst_num_prop_implied:                  0
% 3.50/0.99  inst_num_existing_simplified:           0
% 3.50/0.99  inst_num_eq_res_simplified:             0
% 3.50/0.99  inst_num_child_elim:                    0
% 3.50/0.99  inst_num_of_dismatching_blockings:      590
% 3.50/0.99  inst_num_of_non_proper_insts:           848
% 3.50/0.99  inst_num_of_duplicates:                 0
% 3.50/0.99  inst_inst_num_from_inst_to_res:         0
% 3.50/0.99  inst_dismatching_checking_time:         0.
% 3.50/0.99  
% 3.50/0.99  ------ Resolution
% 3.50/0.99  
% 3.50/0.99  res_num_of_clauses:                     0
% 3.50/0.99  res_num_in_passive:                     0
% 3.50/0.99  res_num_in_active:                      0
% 3.50/0.99  res_num_of_loops:                       62
% 3.50/0.99  res_forward_subset_subsumed:            69
% 3.50/0.99  res_backward_subset_subsumed:           0
% 3.50/0.99  res_forward_subsumed:                   0
% 3.50/0.99  res_backward_subsumed:                  0
% 3.50/0.99  res_forward_subsumption_resolution:     0
% 3.50/0.99  res_backward_subsumption_resolution:    0
% 3.50/0.99  res_clause_to_clause_subsumption:       5136
% 3.50/0.99  res_orphan_elimination:                 0
% 3.50/0.99  res_tautology_del:                      45
% 3.50/0.99  res_num_eq_res_simplified:              0
% 3.50/0.99  res_num_sel_changes:                    0
% 3.50/0.99  res_moves_from_active_to_pass:          0
% 3.50/0.99  
% 3.50/0.99  ------ Superposition
% 3.50/0.99  
% 3.50/0.99  sup_time_total:                         0.
% 3.50/0.99  sup_time_generating:                    0.
% 3.50/0.99  sup_time_sim_full:                      0.
% 3.50/0.99  sup_time_sim_immed:                     0.
% 3.50/0.99  
% 3.50/0.99  sup_num_of_clauses:                     274
% 3.50/0.99  sup_num_in_active:                      58
% 3.50/0.99  sup_num_in_passive:                     216
% 3.50/0.99  sup_num_of_loops:                       62
% 3.50/0.99  sup_fw_superposition:                   315
% 3.50/0.99  sup_bw_superposition:                   427
% 3.50/0.99  sup_immediate_simplified:               259
% 3.50/0.99  sup_given_eliminated:                   0
% 3.50/0.99  comparisons_done:                       0
% 3.50/0.99  comparisons_avoided:                    155
% 3.50/0.99  
% 3.50/0.99  ------ Simplifications
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  sim_fw_subset_subsumed:                 127
% 3.50/0.99  sim_bw_subset_subsumed:                 7
% 3.50/0.99  sim_fw_subsumed:                        123
% 3.50/0.99  sim_bw_subsumed:                        11
% 3.50/0.99  sim_fw_subsumption_res:                 8
% 3.50/0.99  sim_bw_subsumption_res:                 1
% 3.50/0.99  sim_tautology_del:                      12
% 3.50/0.99  sim_eq_tautology_del:                   28
% 3.50/0.99  sim_eq_res_simp:                        14
% 3.50/0.99  sim_fw_demodulated:                     0
% 3.50/0.99  sim_bw_demodulated:                     1
% 3.50/0.99  sim_light_normalised:                   2
% 3.50/0.99  sim_joinable_taut:                      0
% 3.50/0.99  sim_joinable_simp:                      0
% 3.50/0.99  sim_ac_normalised:                      0
% 3.50/0.99  sim_smt_subsumption:                    0
% 3.50/0.99  
%------------------------------------------------------------------------------
