%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:50 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 290 expanded)
%              Number of clauses        :   48 (  98 expanded)
%              Number of leaves         :    8 (  54 expanded)
%              Depth                    :   24
%              Number of atoms          :  239 (1023 expanded)
%              Number of equality atoms :  123 ( 266 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f9])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK2,sK4)
        | ~ r1_tarski(sK1,sK3) )
      & k1_xboole_0 != k2_zfmisc_1(sK1,sK2)
      & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( ~ r1_tarski(sK2,sK4)
      | ~ r1_tarski(sK1,sK3) )
    & k1_xboole_0 != k2_zfmisc_1(sK1,sK2)
    & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f10,f21])).

fof(f36,plain,(
    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,
    ( ~ r1_tarski(sK2,sK4)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3613,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_3622,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3617,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_3621,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3848,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),X4) = iProver_top
    | r1_tarski(k2_zfmisc_1(X3,X1),X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3617,c_3621])).

cnf(c_4071,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(X1,sK2) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3613,c_3848])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3616,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4116,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top
    | r2_hidden(X1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4071,c_3616])).

cnf(c_4170,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r1_tarski(sK1,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3622,c_4116])).

cnf(c_4579,plain,
    ( r2_hidden(sK0(sK2,X0),sK4) = iProver_top
    | r1_tarski(sK1,X1) = iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3622,c_4170])).

cnf(c_4613,plain,
    ( r2_hidden(sK0(sK2,X0),X1) = iProver_top
    | r1_tarski(sK1,X2) = iProver_top
    | r1_tarski(sK4,X1) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4579,c_3621])).

cnf(c_8734,plain,
    ( r2_hidden(sK0(sK2,X0),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK1,X3) = iProver_top
    | r1_tarski(sK4,X2) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4613,c_3621])).

cnf(c_16226,plain,
    ( r2_hidden(sK0(sK2,X0),k2_zfmisc_1(sK3,sK4)) = iProver_top
    | r1_tarski(sK1,X1) = iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3613,c_8734])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_3618,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3620,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3797,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3618,c_3620])).

cnf(c_16592,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(sK0(sK2,X0),k2_zfmisc_1(sK3,sK4)) = iProver_top
    | r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_16226,c_3797])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_3623,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4608,plain,
    ( r1_tarski(sK1,X0) = iProver_top
    | r1_tarski(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4579,c_3623])).

cnf(c_5574,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4608,c_3797])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3615,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4117,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK1) != iProver_top
    | r2_hidden(X1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4071,c_3615])).

cnf(c_4195,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(sK0(sK1,X1),sK3) = iProver_top
    | r1_tarski(sK1,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3622,c_4117])).

cnf(c_5655,plain,
    ( r2_hidden(sK0(sK1,X0),sK3) = iProver_top
    | r1_tarski(sK1,X0) = iProver_top
    | r1_tarski(sK2,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3622,c_4195])).

cnf(c_6102,plain,
    ( r1_tarski(sK1,sK3) = iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5655,c_3623])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3614,plain,
    ( r1_tarski(sK1,sK3) != iProver_top
    | r1_tarski(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6206,plain,
    ( r1_tarski(sK2,X0) = iProver_top
    | r1_tarski(sK2,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6102,c_3614])).

cnf(c_16780,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16592,c_5574,c_6206])).

cnf(c_16792,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16780,c_3797])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16965,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16792,c_14])).

cnf(c_11,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_16968,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16965,c_11])).

cnf(c_16969,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_16968])).

cnf(c_17072,plain,
    ( k2_zfmisc_1(sK1,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16969,c_14])).

cnf(c_10,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17074,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_17072,c_10])).

cnf(c_17075,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_17074])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:44:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.73/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.00  
% 3.73/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/1.00  
% 3.73/1.00  ------  iProver source info
% 3.73/1.00  
% 3.73/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.73/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/1.00  git: non_committed_changes: false
% 3.73/1.00  git: last_make_outside_of_git: false
% 3.73/1.00  
% 3.73/1.00  ------ 
% 3.73/1.00  ------ Parsing...
% 3.73/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  ------ Proving...
% 3.73/1.00  ------ Problem Properties 
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  clauses                                 15
% 3.73/1.00  conjectures                             3
% 3.73/1.00  EPR                                     5
% 3.73/1.00  Horn                                    13
% 3.73/1.00  unary                                   6
% 3.73/1.00  binary                                  5
% 3.73/1.00  lits                                    28
% 3.73/1.00  lits eq                                 7
% 3.73/1.00  fd_pure                                 0
% 3.73/1.00  fd_pseudo                               0
% 3.73/1.00  fd_cond                                 1
% 3.73/1.00  fd_pseudo_cond                          1
% 3.73/1.00  AC symbols                              0
% 3.73/1.00  
% 3.73/1.00  ------ Input Options Time Limit: Unbounded
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing...
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.73/1.00  Current options:
% 3.73/1.00  ------ 
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing...
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing...
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.73/1.00  
% 3.73/1.00  ------ Proving...
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  % SZS status Theorem for theBenchmark.p
% 3.73/1.00  
% 3.73/1.00   Resolution empty clause
% 3.73/1.00  
% 3.73/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/1.00  
% 3.73/1.00  fof(f6,conjecture,(
% 3.73/1.00    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f7,negated_conjecture,(
% 3.73/1.00    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.73/1.00    inference(negated_conjecture,[],[f6])).
% 3.73/1.00  
% 3.73/1.00  fof(f9,plain,(
% 3.73/1.00    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.73/1.00    inference(ennf_transformation,[],[f7])).
% 3.73/1.00  
% 3.73/1.00  fof(f10,plain,(
% 3.73/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.73/1.00    inference(flattening,[],[f9])).
% 3.73/1.00  
% 3.73/1.00  fof(f21,plain,(
% 3.73/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)) & k1_xboole_0 != k2_zfmisc_1(sK1,sK2) & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))),
% 3.73/1.00    introduced(choice_axiom,[])).
% 3.73/1.00  
% 3.73/1.00  fof(f22,plain,(
% 3.73/1.00    (~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)) & k1_xboole_0 != k2_zfmisc_1(sK1,sK2) & r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 3.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f10,f21])).
% 3.73/1.00  
% 3.73/1.00  fof(f36,plain,(
% 3.73/1.00    r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))),
% 3.73/1.00    inference(cnf_transformation,[],[f22])).
% 3.73/1.00  
% 3.73/1.00  fof(f1,axiom,(
% 3.73/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f8,plain,(
% 3.73/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.73/1.00    inference(ennf_transformation,[],[f1])).
% 3.73/1.00  
% 3.73/1.00  fof(f11,plain,(
% 3.73/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.73/1.00    inference(nnf_transformation,[],[f8])).
% 3.73/1.00  
% 3.73/1.00  fof(f12,plain,(
% 3.73/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.73/1.00    inference(rectify,[],[f11])).
% 3.73/1.00  
% 3.73/1.00  fof(f13,plain,(
% 3.73/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.73/1.00    introduced(choice_axiom,[])).
% 3.73/1.00  
% 3.73/1.00  fof(f14,plain,(
% 3.73/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.73/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).
% 3.73/1.00  
% 3.73/1.00  fof(f24,plain,(
% 3.73/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f14])).
% 3.73/1.00  
% 3.73/1.00  fof(f4,axiom,(
% 3.73/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f17,plain,(
% 3.73/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.73/1.00    inference(nnf_transformation,[],[f4])).
% 3.73/1.00  
% 3.73/1.00  fof(f18,plain,(
% 3.73/1.00    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.73/1.00    inference(flattening,[],[f17])).
% 3.73/1.00  
% 3.73/1.00  fof(f32,plain,(
% 3.73/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f18])).
% 3.73/1.00  
% 3.73/1.00  fof(f23,plain,(
% 3.73/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f14])).
% 3.73/1.00  
% 3.73/1.00  fof(f31,plain,(
% 3.73/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.73/1.00    inference(cnf_transformation,[],[f18])).
% 3.73/1.00  
% 3.73/1.00  fof(f3,axiom,(
% 3.73/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f29,plain,(
% 3.73/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f3])).
% 3.73/1.00  
% 3.73/1.00  fof(f2,axiom,(
% 3.73/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f15,plain,(
% 3.73/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/1.00    inference(nnf_transformation,[],[f2])).
% 3.73/1.00  
% 3.73/1.00  fof(f16,plain,(
% 3.73/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/1.00    inference(flattening,[],[f15])).
% 3.73/1.00  
% 3.73/1.00  fof(f28,plain,(
% 3.73/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f16])).
% 3.73/1.00  
% 3.73/1.00  fof(f25,plain,(
% 3.73/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.73/1.00    inference(cnf_transformation,[],[f14])).
% 3.73/1.00  
% 3.73/1.00  fof(f30,plain,(
% 3.73/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.73/1.00    inference(cnf_transformation,[],[f18])).
% 3.73/1.00  
% 3.73/1.00  fof(f38,plain,(
% 3.73/1.00    ~r1_tarski(sK2,sK4) | ~r1_tarski(sK1,sK3)),
% 3.73/1.00    inference(cnf_transformation,[],[f22])).
% 3.73/1.00  
% 3.73/1.00  fof(f37,plain,(
% 3.73/1.00    k1_xboole_0 != k2_zfmisc_1(sK1,sK2)),
% 3.73/1.00    inference(cnf_transformation,[],[f22])).
% 3.73/1.00  
% 3.73/1.00  fof(f5,axiom,(
% 3.73/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.73/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.00  
% 3.73/1.00  fof(f19,plain,(
% 3.73/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.73/1.00    inference(nnf_transformation,[],[f5])).
% 3.73/1.00  
% 3.73/1.00  fof(f20,plain,(
% 3.73/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.73/1.00    inference(flattening,[],[f19])).
% 3.73/1.00  
% 3.73/1.00  fof(f34,plain,(
% 3.73/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.73/1.00    inference(cnf_transformation,[],[f20])).
% 3.73/1.00  
% 3.73/1.00  fof(f42,plain,(
% 3.73/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.73/1.00    inference(equality_resolution,[],[f34])).
% 3.73/1.00  
% 3.73/1.00  fof(f35,plain,(
% 3.73/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.73/1.00    inference(cnf_transformation,[],[f20])).
% 3.73/1.00  
% 3.73/1.00  fof(f41,plain,(
% 3.73/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.73/1.00    inference(equality_resolution,[],[f35])).
% 3.73/1.00  
% 3.73/1.00  cnf(c_15,negated_conjecture,
% 3.73/1.00      ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) ),
% 3.73/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3613,plain,
% 3.73/1.00      ( r1_tarski(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_1,plain,
% 3.73/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.73/1.00      inference(cnf_transformation,[],[f24]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3622,plain,
% 3.73/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.73/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_7,plain,
% 3.73/1.00      ( ~ r2_hidden(X0,X1)
% 3.73/1.00      | ~ r2_hidden(X2,X3)
% 3.73/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.73/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3617,plain,
% 3.73/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.73/1.00      | r2_hidden(X2,X3) != iProver_top
% 3.73/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_2,plain,
% 3.73/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.73/1.00      inference(cnf_transformation,[],[f23]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3621,plain,
% 3.73/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.73/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.73/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3848,plain,
% 3.73/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.73/1.00      | r2_hidden(X2,X3) != iProver_top
% 3.73/1.00      | r2_hidden(k4_tarski(X2,X0),X4) = iProver_top
% 3.73/1.00      | r1_tarski(k2_zfmisc_1(X3,X1),X4) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_3617,c_3621]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4071,plain,
% 3.73/1.00      ( r2_hidden(X0,sK1) != iProver_top
% 3.73/1.00      | r2_hidden(X1,sK2) != iProver_top
% 3.73/1.00      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_3613,c_3848]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_8,plain,
% 3.73/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.73/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3616,plain,
% 3.73/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.73/1.00      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4116,plain,
% 3.73/1.00      ( r2_hidden(X0,sK1) != iProver_top
% 3.73/1.00      | r2_hidden(X1,sK4) = iProver_top
% 3.73/1.00      | r2_hidden(X1,sK2) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_4071,c_3616]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4170,plain,
% 3.73/1.00      ( r2_hidden(X0,sK4) = iProver_top
% 3.73/1.00      | r2_hidden(X0,sK2) != iProver_top
% 3.73/1.00      | r1_tarski(sK1,X1) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_3622,c_4116]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4579,plain,
% 3.73/1.00      ( r2_hidden(sK0(sK2,X0),sK4) = iProver_top
% 3.73/1.00      | r1_tarski(sK1,X1) = iProver_top
% 3.73/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_3622,c_4170]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4613,plain,
% 3.73/1.00      ( r2_hidden(sK0(sK2,X0),X1) = iProver_top
% 3.73/1.00      | r1_tarski(sK1,X2) = iProver_top
% 3.73/1.00      | r1_tarski(sK4,X1) != iProver_top
% 3.73/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_4579,c_3621]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_8734,plain,
% 3.73/1.00      ( r2_hidden(sK0(sK2,X0),X1) = iProver_top
% 3.73/1.00      | r1_tarski(X2,X1) != iProver_top
% 3.73/1.00      | r1_tarski(sK1,X3) = iProver_top
% 3.73/1.00      | r1_tarski(sK4,X2) != iProver_top
% 3.73/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_4613,c_3621]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_16226,plain,
% 3.73/1.00      ( r2_hidden(sK0(sK2,X0),k2_zfmisc_1(sK3,sK4)) = iProver_top
% 3.73/1.00      | r1_tarski(sK1,X1) = iProver_top
% 3.73/1.00      | r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.73/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_3613,c_8734]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6,plain,
% 3.73/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.73/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3618,plain,
% 3.73/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3,plain,
% 3.73/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.73/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3620,plain,
% 3.73/1.00      ( X0 = X1
% 3.73/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.73/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3797,plain,
% 3.73/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_3618,c_3620]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_16592,plain,
% 3.73/1.00      ( sK1 = k1_xboole_0
% 3.73/1.00      | r2_hidden(sK0(sK2,X0),k2_zfmisc_1(sK3,sK4)) = iProver_top
% 3.73/1.00      | r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.73/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_16226,c_3797]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_0,plain,
% 3.73/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.73/1.00      inference(cnf_transformation,[],[f25]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3623,plain,
% 3.73/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.73/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4608,plain,
% 3.73/1.00      ( r1_tarski(sK1,X0) = iProver_top | r1_tarski(sK2,sK4) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_4579,c_3623]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_5574,plain,
% 3.73/1.00      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK4) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_4608,c_3797]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_9,plain,
% 3.73/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.73/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3615,plain,
% 3.73/1.00      ( r2_hidden(X0,X1) = iProver_top
% 3.73/1.00      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4117,plain,
% 3.73/1.00      ( r2_hidden(X0,sK3) = iProver_top
% 3.73/1.00      | r2_hidden(X0,sK1) != iProver_top
% 3.73/1.00      | r2_hidden(X1,sK2) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_4071,c_3615]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_4195,plain,
% 3.73/1.00      ( r2_hidden(X0,sK2) != iProver_top
% 3.73/1.00      | r2_hidden(sK0(sK1,X1),sK3) = iProver_top
% 3.73/1.00      | r1_tarski(sK1,X1) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_3622,c_4117]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_5655,plain,
% 3.73/1.00      ( r2_hidden(sK0(sK1,X0),sK3) = iProver_top
% 3.73/1.00      | r1_tarski(sK1,X0) = iProver_top
% 3.73/1.00      | r1_tarski(sK2,X1) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_3622,c_4195]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6102,plain,
% 3.73/1.00      ( r1_tarski(sK1,sK3) = iProver_top | r1_tarski(sK2,X0) = iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_5655,c_3623]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_13,negated_conjecture,
% 3.73/1.00      ( ~ r1_tarski(sK1,sK3) | ~ r1_tarski(sK2,sK4) ),
% 3.73/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_3614,plain,
% 3.73/1.00      ( r1_tarski(sK1,sK3) != iProver_top | r1_tarski(sK2,sK4) != iProver_top ),
% 3.73/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_6206,plain,
% 3.73/1.00      ( r1_tarski(sK2,X0) = iProver_top | r1_tarski(sK2,sK4) != iProver_top ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_6102,c_3614]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_16780,plain,
% 3.73/1.00      ( sK1 = k1_xboole_0 | r1_tarski(sK2,X0) = iProver_top ),
% 3.73/1.00      inference(global_propositional_subsumption,
% 3.73/1.00                [status(thm)],
% 3.73/1.00                [c_16592,c_5574,c_6206]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_16792,plain,
% 3.73/1.00      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_16780,c_3797]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_14,negated_conjecture,
% 3.73/1.00      ( k1_xboole_0 != k2_zfmisc_1(sK1,sK2) ),
% 3.73/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_16965,plain,
% 3.73/1.00      ( k2_zfmisc_1(k1_xboole_0,sK2) != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.73/1.00      inference(superposition,[status(thm)],[c_16792,c_14]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_11,plain,
% 3.73/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.73/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_16968,plain,
% 3.73/1.00      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.73/1.00      inference(demodulation,[status(thm)],[c_16965,c_11]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_16969,plain,
% 3.73/1.00      ( sK2 = k1_xboole_0 ),
% 3.73/1.00      inference(equality_resolution_simp,[status(thm)],[c_16968]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_17072,plain,
% 3.73/1.00      ( k2_zfmisc_1(sK1,k1_xboole_0) != k1_xboole_0 ),
% 3.73/1.00      inference(demodulation,[status(thm)],[c_16969,c_14]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_10,plain,
% 3.73/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.73/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_17074,plain,
% 3.73/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 3.73/1.00      inference(demodulation,[status(thm)],[c_17072,c_10]) ).
% 3.73/1.00  
% 3.73/1.00  cnf(c_17075,plain,
% 3.73/1.00      ( $false ),
% 3.73/1.00      inference(equality_resolution_simp,[status(thm)],[c_17074]) ).
% 3.73/1.00  
% 3.73/1.00  
% 3.73/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/1.00  
% 3.73/1.00  ------                               Statistics
% 3.73/1.00  
% 3.73/1.00  ------ Selected
% 3.73/1.00  
% 3.73/1.00  total_time:                             0.403
% 3.73/1.00  
%------------------------------------------------------------------------------
