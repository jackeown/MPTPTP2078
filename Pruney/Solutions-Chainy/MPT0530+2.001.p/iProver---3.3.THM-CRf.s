%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:45:36 EST 2020

% Result     : Theorem 23.34s
% Output     : CNFRefutation 23.34s
% Verified   : 
% Statistics : Number of formulae       :  123 (2161 expanded)
%              Number of clauses        :   76 ( 647 expanded)
%              Number of leaves         :   13 ( 448 expanded)
%              Depth                    :   37
%              Number of atoms          :  334 (12310 expanded)
%              Number of equality atoms :  169 (2697 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5))
      & r1_tarski(sK3,sK4)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5))
    & r1_tarski(sK3,sK4)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f34])).

fof(f58,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f45,f52])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f56,f52])).

fof(f59,plain,(
    k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_14,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_530,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_527,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_529,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_537,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_538,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2014,plain,
    ( k4_xboole_0(X0,X0) = X1
    | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_538])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_540,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2252,plain,
    ( k4_xboole_0(X0,X0) = X1
    | r2_hidden(sK1(X0,X0,X1),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2014,c_540])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_535,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2256,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
    | r2_hidden(sK1(X0,X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2014,c_535])).

cnf(c_2891,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X1,X1)
    | r2_hidden(sK1(X1,X1,X0),k4_xboole_0(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_2256])).

cnf(c_2894,plain,
    ( k4_xboole_0(X0,X0) = X1
    | r2_hidden(sK1(X0,X0,X1),k4_xboole_0(X1,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2891,c_9])).

cnf(c_3938,plain,
    ( k4_xboole_0(X0,X0) = X1
    | r1_tarski(X1,k4_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2252,c_2894])).

cnf(c_3976,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_529,c_3938])).

cnf(c_1864,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X3) = iProver_top
    | r1_tarski(X0,X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_540])).

cnf(c_7663,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1864,c_538])).

cnf(c_8684,plain,
    ( k4_xboole_0(X0,X1) = k4_xboole_0(X2,X3)
    | r2_hidden(sK1(X2,X3,k4_xboole_0(X0,X1)),X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7663,c_535])).

cnf(c_17587,plain,
    ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X2)
    | r2_hidden(sK1(X1,X2,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_8684])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_534,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_26247,plain,
    ( k4_xboole_0(X0,X1) = k4_xboole_0(X2,X0)
    | r2_hidden(sK1(X0,X1,k4_xboole_0(X2,X0)),X2) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_17587,c_534])).

cnf(c_4156,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_3976,c_9])).

cnf(c_1865,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = X3
    | r2_hidden(sK1(k4_xboole_0(X0,X1),X2,X3),X3) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(X0,X1),X2,X3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_534])).

cnf(c_38459,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = X2
    | r2_hidden(sK1(k4_xboole_0(X0,X1),X0,X2),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1865,c_538])).

cnf(c_38968,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X2,X3)
    | r2_hidden(sK1(k4_xboole_0(X0,X1),X0,k4_xboole_0(X2,X3)),X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_38459,c_535])).

cnf(c_39340,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X2,k1_xboole_0)
    | r2_hidden(sK1(k4_xboole_0(X0,X1),X0,X2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4156,c_38968])).

cnf(c_39343,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = X2
    | r2_hidden(sK1(k4_xboole_0(X0,X1),X0,X2),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_39340,c_4156])).

cnf(c_39427,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) = X1
    | r2_hidden(sK1(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1865,c_39343])).

cnf(c_39447,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = X1
    | r2_hidden(sK1(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0,X1),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_39427,c_4156])).

cnf(c_40101,plain,
    ( k4_xboole_0(X0,X1) = k4_xboole_0(k1_xboole_0,X2)
    | r2_hidden(sK1(k4_xboole_0(k1_xboole_0,X2),k1_xboole_0,k4_xboole_0(X0,X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_39447,c_535])).

cnf(c_40683,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X1)
    | r2_hidden(sK1(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4156,c_40101])).

cnf(c_40686,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = X1
    | r2_hidden(sK1(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0,X1),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_40683,c_4156])).

cnf(c_41266,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0)
    | r1_tarski(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_26247,c_40686])).

cnf(c_41281,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0)
    | r1_tarski(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_41266,c_4156])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_541,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1018,plain,
    ( r2_hidden(sK0(k4_xboole_0(X0,X1),X2),X0) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_541,c_534])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_542,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1830,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1018,c_542])).

cnf(c_41312,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_41281,c_1830])).

cnf(c_41413,plain,
    ( r2_hidden(X0,k4_xboole_0(k1_xboole_0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_41312,c_535])).

cnf(c_42374,plain,
    ( k4_xboole_0(X0,X1) = k4_xboole_0(k1_xboole_0,X2)
    | r2_hidden(sK1(X0,X1,k4_xboole_0(k1_xboole_0,X2)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_537,c_41413])).

cnf(c_43531,plain,
    ( k4_xboole_0(X0,X1) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | r2_hidden(sK1(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3976,c_42374])).

cnf(c_43579,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK1(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_43531,c_4156])).

cnf(c_43818,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK1(X0,X1,k1_xboole_0),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_43579,c_540])).

cnf(c_44989,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK1(X0,X1,k1_xboole_0),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_43818,c_540])).

cnf(c_57424,plain,
    ( k4_xboole_0(sK3,X0) = k1_xboole_0
    | r2_hidden(sK1(sK3,X0,k1_xboole_0),X1) = iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_527,c_44989])).

cnf(c_57463,plain,
    ( k4_xboole_0(sK3,X0) = k1_xboole_0
    | r2_hidden(sK1(sK3,X0,k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_57424,c_538])).

cnf(c_43822,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k1_xboole_0
    | r2_hidden(sK1(k4_xboole_0(X0,X1),X2,k1_xboole_0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_43579,c_535])).

cnf(c_44144,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) = k1_xboole_0
    | r2_hidden(sK1(X0,X1,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4156,c_43822])).

cnf(c_44151,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK1(X0,X1,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_44144,c_4156])).

cnf(c_57783,plain,
    ( k4_xboole_0(sK3,X0) = k1_xboole_0
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_57463,c_44151])).

cnf(c_57785,plain,
    ( k4_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_530,c_57783])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_526,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0) = k8_relat_1(X1,k8_relat_1(X2,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_528,plain,
    ( k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_734,plain,
    ( k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK5) = k8_relat_1(X0,k8_relat_1(X1,sK5)) ),
    inference(superposition,[status(thm)],[c_526,c_528])).

cnf(c_58229,plain,
    ( k8_relat_1(k4_xboole_0(sK3,k1_xboole_0),sK5) = k8_relat_1(sK3,k8_relat_1(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_57785,c_734])).

cnf(c_58541,plain,
    ( k8_relat_1(sK3,k8_relat_1(sK4,sK5)) = k8_relat_1(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_58229,c_4156])).

cnf(c_243,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_836,plain,
    ( k8_relat_1(sK3,sK5) = k8_relat_1(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_243])).

cnf(c_244,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_695,plain,
    ( k8_relat_1(sK3,k8_relat_1(sK4,sK5)) != X0
    | k8_relat_1(sK3,sK5) != X0
    | k8_relat_1(sK3,sK5) = k8_relat_1(sK3,k8_relat_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_244])).

cnf(c_835,plain,
    ( k8_relat_1(sK3,k8_relat_1(sK4,sK5)) != k8_relat_1(sK3,sK5)
    | k8_relat_1(sK3,sK5) = k8_relat_1(sK3,k8_relat_1(sK4,sK5))
    | k8_relat_1(sK3,sK5) != k8_relat_1(sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_18,negated_conjecture,
    ( k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_58541,c_836,c_835,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.34/3.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.34/3.48  
% 23.34/3.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.34/3.48  
% 23.34/3.48  ------  iProver source info
% 23.34/3.48  
% 23.34/3.48  git: date: 2020-06-30 10:37:57 +0100
% 23.34/3.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.34/3.48  git: non_committed_changes: false
% 23.34/3.48  git: last_make_outside_of_git: false
% 23.34/3.48  
% 23.34/3.48  ------ 
% 23.34/3.48  
% 23.34/3.48  ------ Input Options
% 23.34/3.48  
% 23.34/3.48  --out_options                           all
% 23.34/3.48  --tptp_safe_out                         true
% 23.34/3.48  --problem_path                          ""
% 23.34/3.48  --include_path                          ""
% 23.34/3.48  --clausifier                            res/vclausify_rel
% 23.34/3.48  --clausifier_options                    --mode clausify
% 23.34/3.48  --stdin                                 false
% 23.34/3.48  --stats_out                             sel
% 23.34/3.48  
% 23.34/3.48  ------ General Options
% 23.34/3.48  
% 23.34/3.48  --fof                                   false
% 23.34/3.48  --time_out_real                         604.99
% 23.34/3.48  --time_out_virtual                      -1.
% 23.34/3.48  --symbol_type_check                     false
% 23.34/3.48  --clausify_out                          false
% 23.34/3.48  --sig_cnt_out                           false
% 23.34/3.48  --trig_cnt_out                          false
% 23.34/3.48  --trig_cnt_out_tolerance                1.
% 23.34/3.48  --trig_cnt_out_sk_spl                   false
% 23.34/3.48  --abstr_cl_out                          false
% 23.34/3.48  
% 23.34/3.48  ------ Global Options
% 23.34/3.48  
% 23.34/3.48  --schedule                              none
% 23.34/3.48  --add_important_lit                     false
% 23.34/3.48  --prop_solver_per_cl                    1000
% 23.34/3.48  --min_unsat_core                        false
% 23.34/3.48  --soft_assumptions                      false
% 23.34/3.48  --soft_lemma_size                       3
% 23.34/3.48  --prop_impl_unit_size                   0
% 23.34/3.48  --prop_impl_unit                        []
% 23.34/3.48  --share_sel_clauses                     true
% 23.34/3.48  --reset_solvers                         false
% 23.34/3.48  --bc_imp_inh                            [conj_cone]
% 23.34/3.48  --conj_cone_tolerance                   3.
% 23.34/3.48  --extra_neg_conj                        none
% 23.34/3.48  --large_theory_mode                     true
% 23.34/3.48  --prolific_symb_bound                   200
% 23.34/3.48  --lt_threshold                          2000
% 23.34/3.48  --clause_weak_htbl                      true
% 23.34/3.48  --gc_record_bc_elim                     false
% 23.34/3.48  
% 23.34/3.48  ------ Preprocessing Options
% 23.34/3.48  
% 23.34/3.48  --preprocessing_flag                    true
% 23.34/3.48  --time_out_prep_mult                    0.1
% 23.34/3.48  --splitting_mode                        input
% 23.34/3.48  --splitting_grd                         true
% 23.34/3.48  --splitting_cvd                         false
% 23.34/3.48  --splitting_cvd_svl                     false
% 23.34/3.48  --splitting_nvd                         32
% 23.34/3.48  --sub_typing                            true
% 23.34/3.48  --prep_gs_sim                           false
% 23.34/3.48  --prep_unflatten                        true
% 23.34/3.48  --prep_res_sim                          true
% 23.34/3.48  --prep_upred                            true
% 23.34/3.48  --prep_sem_filter                       exhaustive
% 23.34/3.48  --prep_sem_filter_out                   false
% 23.34/3.48  --pred_elim                             false
% 23.34/3.48  --res_sim_input                         true
% 23.34/3.48  --eq_ax_congr_red                       true
% 23.34/3.48  --pure_diseq_elim                       true
% 23.34/3.48  --brand_transform                       false
% 23.34/3.48  --non_eq_to_eq                          false
% 23.34/3.48  --prep_def_merge                        true
% 23.34/3.48  --prep_def_merge_prop_impl              false
% 23.34/3.48  --prep_def_merge_mbd                    true
% 23.34/3.48  --prep_def_merge_tr_red                 false
% 23.34/3.48  --prep_def_merge_tr_cl                  false
% 23.34/3.48  --smt_preprocessing                     true
% 23.34/3.48  --smt_ac_axioms                         fast
% 23.34/3.48  --preprocessed_out                      false
% 23.34/3.48  --preprocessed_stats                    false
% 23.34/3.48  
% 23.34/3.48  ------ Abstraction refinement Options
% 23.34/3.48  
% 23.34/3.48  --abstr_ref                             []
% 23.34/3.48  --abstr_ref_prep                        false
% 23.34/3.48  --abstr_ref_until_sat                   false
% 23.34/3.48  --abstr_ref_sig_restrict                funpre
% 23.34/3.48  --abstr_ref_af_restrict_to_split_sk     false
% 23.34/3.48  --abstr_ref_under                       []
% 23.34/3.48  
% 23.34/3.48  ------ SAT Options
% 23.34/3.48  
% 23.34/3.48  --sat_mode                              false
% 23.34/3.48  --sat_fm_restart_options                ""
% 23.34/3.48  --sat_gr_def                            false
% 23.34/3.48  --sat_epr_types                         true
% 23.34/3.48  --sat_non_cyclic_types                  false
% 23.34/3.48  --sat_finite_models                     false
% 23.34/3.48  --sat_fm_lemmas                         false
% 23.34/3.48  --sat_fm_prep                           false
% 23.34/3.48  --sat_fm_uc_incr                        true
% 23.34/3.48  --sat_out_model                         small
% 23.34/3.48  --sat_out_clauses                       false
% 23.34/3.48  
% 23.34/3.48  ------ QBF Options
% 23.34/3.48  
% 23.34/3.48  --qbf_mode                              false
% 23.34/3.48  --qbf_elim_univ                         false
% 23.34/3.48  --qbf_dom_inst                          none
% 23.34/3.48  --qbf_dom_pre_inst                      false
% 23.34/3.48  --qbf_sk_in                             false
% 23.34/3.48  --qbf_pred_elim                         true
% 23.34/3.48  --qbf_split                             512
% 23.34/3.48  
% 23.34/3.48  ------ BMC1 Options
% 23.34/3.48  
% 23.34/3.48  --bmc1_incremental                      false
% 23.34/3.48  --bmc1_axioms                           reachable_all
% 23.34/3.48  --bmc1_min_bound                        0
% 23.34/3.48  --bmc1_max_bound                        -1
% 23.34/3.48  --bmc1_max_bound_default                -1
% 23.34/3.48  --bmc1_symbol_reachability              true
% 23.34/3.48  --bmc1_property_lemmas                  false
% 23.34/3.48  --bmc1_k_induction                      false
% 23.34/3.48  --bmc1_non_equiv_states                 false
% 23.34/3.48  --bmc1_deadlock                         false
% 23.34/3.48  --bmc1_ucm                              false
% 23.34/3.48  --bmc1_add_unsat_core                   none
% 23.34/3.48  --bmc1_unsat_core_children              false
% 23.34/3.48  --bmc1_unsat_core_extrapolate_axioms    false
% 23.34/3.48  --bmc1_out_stat                         full
% 23.34/3.48  --bmc1_ground_init                      false
% 23.34/3.48  --bmc1_pre_inst_next_state              false
% 23.34/3.48  --bmc1_pre_inst_state                   false
% 23.34/3.48  --bmc1_pre_inst_reach_state             false
% 23.34/3.48  --bmc1_out_unsat_core                   false
% 23.34/3.48  --bmc1_aig_witness_out                  false
% 23.34/3.48  --bmc1_verbose                          false
% 23.34/3.48  --bmc1_dump_clauses_tptp                false
% 23.34/3.48  --bmc1_dump_unsat_core_tptp             false
% 23.34/3.48  --bmc1_dump_file                        -
% 23.34/3.48  --bmc1_ucm_expand_uc_limit              128
% 23.34/3.48  --bmc1_ucm_n_expand_iterations          6
% 23.34/3.48  --bmc1_ucm_extend_mode                  1
% 23.34/3.48  --bmc1_ucm_init_mode                    2
% 23.34/3.48  --bmc1_ucm_cone_mode                    none
% 23.34/3.48  --bmc1_ucm_reduced_relation_type        0
% 23.34/3.48  --bmc1_ucm_relax_model                  4
% 23.34/3.48  --bmc1_ucm_full_tr_after_sat            true
% 23.34/3.48  --bmc1_ucm_expand_neg_assumptions       false
% 23.34/3.48  --bmc1_ucm_layered_model                none
% 23.34/3.48  --bmc1_ucm_max_lemma_size               10
% 23.34/3.48  
% 23.34/3.48  ------ AIG Options
% 23.34/3.48  
% 23.34/3.48  --aig_mode                              false
% 23.34/3.48  
% 23.34/3.48  ------ Instantiation Options
% 23.34/3.48  
% 23.34/3.48  --instantiation_flag                    true
% 23.34/3.48  --inst_sos_flag                         false
% 23.34/3.48  --inst_sos_phase                        true
% 23.34/3.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.34/3.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.34/3.48  --inst_lit_sel_side                     num_symb
% 23.34/3.48  --inst_solver_per_active                1400
% 23.34/3.48  --inst_solver_calls_frac                1.
% 23.34/3.48  --inst_passive_queue_type               priority_queues
% 23.34/3.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.34/3.48  --inst_passive_queues_freq              [25;2]
% 23.34/3.48  --inst_dismatching                      true
% 23.34/3.48  --inst_eager_unprocessed_to_passive     true
% 23.34/3.48  --inst_prop_sim_given                   true
% 23.34/3.48  --inst_prop_sim_new                     false
% 23.34/3.48  --inst_subs_new                         false
% 23.34/3.48  --inst_eq_res_simp                      false
% 23.34/3.48  --inst_subs_given                       false
% 23.34/3.48  --inst_orphan_elimination               true
% 23.34/3.48  --inst_learning_loop_flag               true
% 23.34/3.48  --inst_learning_start                   3000
% 23.34/3.48  --inst_learning_factor                  2
% 23.34/3.48  --inst_start_prop_sim_after_learn       3
% 23.34/3.48  --inst_sel_renew                        solver
% 23.34/3.48  --inst_lit_activity_flag                true
% 23.34/3.48  --inst_restr_to_given                   false
% 23.34/3.48  --inst_activity_threshold               500
% 23.34/3.48  --inst_out_proof                        true
% 23.34/3.48  
% 23.34/3.48  ------ Resolution Options
% 23.34/3.48  
% 23.34/3.48  --resolution_flag                       true
% 23.34/3.48  --res_lit_sel                           adaptive
% 23.34/3.48  --res_lit_sel_side                      none
% 23.34/3.48  --res_ordering                          kbo
% 23.34/3.48  --res_to_prop_solver                    active
% 23.34/3.48  --res_prop_simpl_new                    false
% 23.34/3.48  --res_prop_simpl_given                  true
% 23.34/3.48  --res_passive_queue_type                priority_queues
% 23.34/3.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.34/3.48  --res_passive_queues_freq               [15;5]
% 23.34/3.48  --res_forward_subs                      full
% 23.34/3.48  --res_backward_subs                     full
% 23.34/3.48  --res_forward_subs_resolution           true
% 23.34/3.48  --res_backward_subs_resolution          true
% 23.34/3.48  --res_orphan_elimination                true
% 23.34/3.48  --res_time_limit                        2.
% 23.34/3.48  --res_out_proof                         true
% 23.34/3.48  
% 23.34/3.48  ------ Superposition Options
% 23.34/3.48  
% 23.34/3.48  --superposition_flag                    true
% 23.34/3.48  --sup_passive_queue_type                priority_queues
% 23.34/3.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.34/3.48  --sup_passive_queues_freq               [1;4]
% 23.34/3.48  --demod_completeness_check              fast
% 23.34/3.48  --demod_use_ground                      true
% 23.34/3.48  --sup_to_prop_solver                    passive
% 23.34/3.48  --sup_prop_simpl_new                    true
% 23.34/3.48  --sup_prop_simpl_given                  true
% 23.34/3.48  --sup_fun_splitting                     false
% 23.34/3.48  --sup_smt_interval                      50000
% 23.34/3.48  
% 23.34/3.48  ------ Superposition Simplification Setup
% 23.34/3.48  
% 23.34/3.48  --sup_indices_passive                   []
% 23.34/3.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.34/3.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.34/3.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.34/3.48  --sup_full_triv                         [TrivRules;PropSubs]
% 23.34/3.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.34/3.48  --sup_full_bw                           [BwDemod]
% 23.34/3.48  --sup_immed_triv                        [TrivRules]
% 23.34/3.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.34/3.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.34/3.48  --sup_immed_bw_main                     []
% 23.34/3.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.34/3.48  --sup_input_triv                        [Unflattening;TrivRules]
% 23.34/3.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.34/3.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.34/3.48  
% 23.34/3.48  ------ Combination Options
% 23.34/3.48  
% 23.34/3.48  --comb_res_mult                         3
% 23.34/3.48  --comb_sup_mult                         2
% 23.34/3.48  --comb_inst_mult                        10
% 23.34/3.48  
% 23.34/3.48  ------ Debug Options
% 23.34/3.48  
% 23.34/3.48  --dbg_backtrace                         false
% 23.34/3.48  --dbg_dump_prop_clauses                 false
% 23.34/3.48  --dbg_dump_prop_clauses_file            -
% 23.34/3.48  --dbg_out_stat                          false
% 23.34/3.48  ------ Parsing...
% 23.34/3.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.34/3.48  
% 23.34/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.34/3.48  
% 23.34/3.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.34/3.48  
% 23.34/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.34/3.48  ------ Proving...
% 23.34/3.48  ------ Problem Properties 
% 23.34/3.48  
% 23.34/3.48  
% 23.34/3.48  clauses                                 20
% 23.34/3.48  conjectures                             3
% 23.34/3.48  EPR                                     6
% 23.34/3.48  Horn                                    14
% 23.34/3.48  unary                                   7
% 23.34/3.48  binary                                  5
% 23.34/3.48  lits                                    42
% 23.34/3.48  lits eq                                 10
% 23.34/3.48  fd_pure                                 0
% 23.34/3.48  fd_pseudo                               0
% 23.34/3.48  fd_cond                                 0
% 23.34/3.48  fd_pseudo_cond                          6
% 23.34/3.48  AC symbols                              0
% 23.34/3.48  
% 23.34/3.48  ------ Input Options Time Limit: Unbounded
% 23.34/3.48  
% 23.34/3.48  
% 23.34/3.48  ------ 
% 23.34/3.48  Current options:
% 23.34/3.48  ------ 
% 23.34/3.48  
% 23.34/3.48  ------ Input Options
% 23.34/3.48  
% 23.34/3.48  --out_options                           all
% 23.34/3.48  --tptp_safe_out                         true
% 23.34/3.48  --problem_path                          ""
% 23.34/3.48  --include_path                          ""
% 23.34/3.48  --clausifier                            res/vclausify_rel
% 23.34/3.48  --clausifier_options                    --mode clausify
% 23.34/3.48  --stdin                                 false
% 23.34/3.48  --stats_out                             sel
% 23.34/3.48  
% 23.34/3.48  ------ General Options
% 23.34/3.48  
% 23.34/3.48  --fof                                   false
% 23.34/3.48  --time_out_real                         604.99
% 23.34/3.48  --time_out_virtual                      -1.
% 23.34/3.48  --symbol_type_check                     false
% 23.34/3.48  --clausify_out                          false
% 23.34/3.48  --sig_cnt_out                           false
% 23.34/3.48  --trig_cnt_out                          false
% 23.34/3.48  --trig_cnt_out_tolerance                1.
% 23.34/3.48  --trig_cnt_out_sk_spl                   false
% 23.34/3.48  --abstr_cl_out                          false
% 23.34/3.48  
% 23.34/3.48  ------ Global Options
% 23.34/3.48  
% 23.34/3.48  --schedule                              none
% 23.34/3.48  --add_important_lit                     false
% 23.34/3.48  --prop_solver_per_cl                    1000
% 23.34/3.48  --min_unsat_core                        false
% 23.34/3.48  --soft_assumptions                      false
% 23.34/3.48  --soft_lemma_size                       3
% 23.34/3.48  --prop_impl_unit_size                   0
% 23.34/3.48  --prop_impl_unit                        []
% 23.34/3.48  --share_sel_clauses                     true
% 23.34/3.48  --reset_solvers                         false
% 23.34/3.48  --bc_imp_inh                            [conj_cone]
% 23.34/3.48  --conj_cone_tolerance                   3.
% 23.34/3.48  --extra_neg_conj                        none
% 23.34/3.48  --large_theory_mode                     true
% 23.34/3.48  --prolific_symb_bound                   200
% 23.34/3.48  --lt_threshold                          2000
% 23.34/3.48  --clause_weak_htbl                      true
% 23.34/3.48  --gc_record_bc_elim                     false
% 23.34/3.48  
% 23.34/3.48  ------ Preprocessing Options
% 23.34/3.48  
% 23.34/3.48  --preprocessing_flag                    true
% 23.34/3.48  --time_out_prep_mult                    0.1
% 23.34/3.48  --splitting_mode                        input
% 23.34/3.48  --splitting_grd                         true
% 23.34/3.48  --splitting_cvd                         false
% 23.34/3.48  --splitting_cvd_svl                     false
% 23.34/3.48  --splitting_nvd                         32
% 23.34/3.48  --sub_typing                            true
% 23.34/3.48  --prep_gs_sim                           false
% 23.34/3.48  --prep_unflatten                        true
% 23.34/3.48  --prep_res_sim                          true
% 23.34/3.48  --prep_upred                            true
% 23.34/3.48  --prep_sem_filter                       exhaustive
% 23.34/3.48  --prep_sem_filter_out                   false
% 23.34/3.48  --pred_elim                             false
% 23.34/3.48  --res_sim_input                         true
% 23.34/3.48  --eq_ax_congr_red                       true
% 23.34/3.48  --pure_diseq_elim                       true
% 23.34/3.48  --brand_transform                       false
% 23.34/3.48  --non_eq_to_eq                          false
% 23.34/3.48  --prep_def_merge                        true
% 23.34/3.48  --prep_def_merge_prop_impl              false
% 23.34/3.48  --prep_def_merge_mbd                    true
% 23.34/3.48  --prep_def_merge_tr_red                 false
% 23.34/3.48  --prep_def_merge_tr_cl                  false
% 23.34/3.48  --smt_preprocessing                     true
% 23.34/3.48  --smt_ac_axioms                         fast
% 23.34/3.48  --preprocessed_out                      false
% 23.34/3.48  --preprocessed_stats                    false
% 23.34/3.48  
% 23.34/3.48  ------ Abstraction refinement Options
% 23.34/3.48  
% 23.34/3.48  --abstr_ref                             []
% 23.34/3.48  --abstr_ref_prep                        false
% 23.34/3.48  --abstr_ref_until_sat                   false
% 23.34/3.48  --abstr_ref_sig_restrict                funpre
% 23.34/3.48  --abstr_ref_af_restrict_to_split_sk     false
% 23.34/3.48  --abstr_ref_under                       []
% 23.34/3.48  
% 23.34/3.48  ------ SAT Options
% 23.34/3.48  
% 23.34/3.48  --sat_mode                              false
% 23.34/3.48  --sat_fm_restart_options                ""
% 23.34/3.48  --sat_gr_def                            false
% 23.34/3.48  --sat_epr_types                         true
% 23.34/3.48  --sat_non_cyclic_types                  false
% 23.34/3.48  --sat_finite_models                     false
% 23.34/3.48  --sat_fm_lemmas                         false
% 23.34/3.48  --sat_fm_prep                           false
% 23.34/3.48  --sat_fm_uc_incr                        true
% 23.34/3.48  --sat_out_model                         small
% 23.34/3.48  --sat_out_clauses                       false
% 23.34/3.48  
% 23.34/3.48  ------ QBF Options
% 23.34/3.48  
% 23.34/3.48  --qbf_mode                              false
% 23.34/3.48  --qbf_elim_univ                         false
% 23.34/3.48  --qbf_dom_inst                          none
% 23.34/3.48  --qbf_dom_pre_inst                      false
% 23.34/3.48  --qbf_sk_in                             false
% 23.34/3.48  --qbf_pred_elim                         true
% 23.34/3.48  --qbf_split                             512
% 23.34/3.48  
% 23.34/3.48  ------ BMC1 Options
% 23.34/3.48  
% 23.34/3.48  --bmc1_incremental                      false
% 23.34/3.48  --bmc1_axioms                           reachable_all
% 23.34/3.48  --bmc1_min_bound                        0
% 23.34/3.48  --bmc1_max_bound                        -1
% 23.34/3.48  --bmc1_max_bound_default                -1
% 23.34/3.48  --bmc1_symbol_reachability              true
% 23.34/3.48  --bmc1_property_lemmas                  false
% 23.34/3.48  --bmc1_k_induction                      false
% 23.34/3.48  --bmc1_non_equiv_states                 false
% 23.34/3.48  --bmc1_deadlock                         false
% 23.34/3.48  --bmc1_ucm                              false
% 23.34/3.48  --bmc1_add_unsat_core                   none
% 23.34/3.48  --bmc1_unsat_core_children              false
% 23.34/3.48  --bmc1_unsat_core_extrapolate_axioms    false
% 23.34/3.48  --bmc1_out_stat                         full
% 23.34/3.48  --bmc1_ground_init                      false
% 23.34/3.48  --bmc1_pre_inst_next_state              false
% 23.34/3.48  --bmc1_pre_inst_state                   false
% 23.34/3.48  --bmc1_pre_inst_reach_state             false
% 23.34/3.48  --bmc1_out_unsat_core                   false
% 23.34/3.48  --bmc1_aig_witness_out                  false
% 23.34/3.48  --bmc1_verbose                          false
% 23.34/3.48  --bmc1_dump_clauses_tptp                false
% 23.34/3.48  --bmc1_dump_unsat_core_tptp             false
% 23.34/3.48  --bmc1_dump_file                        -
% 23.34/3.48  --bmc1_ucm_expand_uc_limit              128
% 23.34/3.48  --bmc1_ucm_n_expand_iterations          6
% 23.34/3.48  --bmc1_ucm_extend_mode                  1
% 23.34/3.48  --bmc1_ucm_init_mode                    2
% 23.34/3.48  --bmc1_ucm_cone_mode                    none
% 23.34/3.48  --bmc1_ucm_reduced_relation_type        0
% 23.34/3.48  --bmc1_ucm_relax_model                  4
% 23.34/3.48  --bmc1_ucm_full_tr_after_sat            true
% 23.34/3.48  --bmc1_ucm_expand_neg_assumptions       false
% 23.34/3.48  --bmc1_ucm_layered_model                none
% 23.34/3.48  --bmc1_ucm_max_lemma_size               10
% 23.34/3.48  
% 23.34/3.48  ------ AIG Options
% 23.34/3.48  
% 23.34/3.48  --aig_mode                              false
% 23.34/3.48  
% 23.34/3.48  ------ Instantiation Options
% 23.34/3.48  
% 23.34/3.48  --instantiation_flag                    true
% 23.34/3.48  --inst_sos_flag                         false
% 23.34/3.48  --inst_sos_phase                        true
% 23.34/3.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.34/3.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.34/3.48  --inst_lit_sel_side                     num_symb
% 23.34/3.48  --inst_solver_per_active                1400
% 23.34/3.48  --inst_solver_calls_frac                1.
% 23.34/3.48  --inst_passive_queue_type               priority_queues
% 23.34/3.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.34/3.48  --inst_passive_queues_freq              [25;2]
% 23.34/3.48  --inst_dismatching                      true
% 23.34/3.48  --inst_eager_unprocessed_to_passive     true
% 23.34/3.48  --inst_prop_sim_given                   true
% 23.34/3.48  --inst_prop_sim_new                     false
% 23.34/3.48  --inst_subs_new                         false
% 23.34/3.48  --inst_eq_res_simp                      false
% 23.34/3.48  --inst_subs_given                       false
% 23.34/3.48  --inst_orphan_elimination               true
% 23.34/3.48  --inst_learning_loop_flag               true
% 23.34/3.48  --inst_learning_start                   3000
% 23.34/3.48  --inst_learning_factor                  2
% 23.34/3.48  --inst_start_prop_sim_after_learn       3
% 23.34/3.48  --inst_sel_renew                        solver
% 23.34/3.48  --inst_lit_activity_flag                true
% 23.34/3.48  --inst_restr_to_given                   false
% 23.34/3.48  --inst_activity_threshold               500
% 23.34/3.48  --inst_out_proof                        true
% 23.34/3.48  
% 23.34/3.48  ------ Resolution Options
% 23.34/3.48  
% 23.34/3.48  --resolution_flag                       true
% 23.34/3.48  --res_lit_sel                           adaptive
% 23.34/3.48  --res_lit_sel_side                      none
% 23.34/3.48  --res_ordering                          kbo
% 23.34/3.48  --res_to_prop_solver                    active
% 23.34/3.48  --res_prop_simpl_new                    false
% 23.34/3.48  --res_prop_simpl_given                  true
% 23.34/3.48  --res_passive_queue_type                priority_queues
% 23.34/3.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.34/3.48  --res_passive_queues_freq               [15;5]
% 23.34/3.48  --res_forward_subs                      full
% 23.34/3.48  --res_backward_subs                     full
% 23.34/3.48  --res_forward_subs_resolution           true
% 23.34/3.48  --res_backward_subs_resolution          true
% 23.34/3.48  --res_orphan_elimination                true
% 23.34/3.48  --res_time_limit                        2.
% 23.34/3.48  --res_out_proof                         true
% 23.34/3.48  
% 23.34/3.48  ------ Superposition Options
% 23.34/3.48  
% 23.34/3.48  --superposition_flag                    true
% 23.34/3.48  --sup_passive_queue_type                priority_queues
% 23.34/3.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.34/3.48  --sup_passive_queues_freq               [1;4]
% 23.34/3.48  --demod_completeness_check              fast
% 23.34/3.48  --demod_use_ground                      true
% 23.34/3.48  --sup_to_prop_solver                    passive
% 23.34/3.48  --sup_prop_simpl_new                    true
% 23.34/3.48  --sup_prop_simpl_given                  true
% 23.34/3.48  --sup_fun_splitting                     false
% 23.34/3.48  --sup_smt_interval                      50000
% 23.34/3.48  
% 23.34/3.48  ------ Superposition Simplification Setup
% 23.34/3.48  
% 23.34/3.48  --sup_indices_passive                   []
% 23.34/3.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.34/3.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.34/3.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.34/3.48  --sup_full_triv                         [TrivRules;PropSubs]
% 23.34/3.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.34/3.48  --sup_full_bw                           [BwDemod]
% 23.34/3.48  --sup_immed_triv                        [TrivRules]
% 23.34/3.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.34/3.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.34/3.48  --sup_immed_bw_main                     []
% 23.34/3.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.34/3.48  --sup_input_triv                        [Unflattening;TrivRules]
% 23.34/3.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.34/3.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.34/3.48  
% 23.34/3.48  ------ Combination Options
% 23.34/3.48  
% 23.34/3.48  --comb_res_mult                         3
% 23.34/3.48  --comb_sup_mult                         2
% 23.34/3.48  --comb_inst_mult                        10
% 23.34/3.48  
% 23.34/3.48  ------ Debug Options
% 23.34/3.48  
% 23.34/3.48  --dbg_backtrace                         false
% 23.34/3.48  --dbg_dump_prop_clauses                 false
% 23.34/3.48  --dbg_dump_prop_clauses_file            -
% 23.34/3.48  --dbg_out_stat                          false
% 23.34/3.48  
% 23.34/3.48  
% 23.34/3.48  
% 23.34/3.48  
% 23.34/3.48  ------ Proving...
% 23.34/3.48  
% 23.34/3.48  
% 23.34/3.48  % SZS status Theorem for theBenchmark.p
% 23.34/3.48  
% 23.34/3.48  % SZS output start CNFRefutation for theBenchmark.p
% 23.34/3.48  
% 23.34/3.48  fof(f5,axiom,(
% 23.34/3.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.34/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.48  
% 23.34/3.48  fof(f32,plain,(
% 23.34/3.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.34/3.48    inference(nnf_transformation,[],[f5])).
% 23.34/3.48  
% 23.34/3.48  fof(f33,plain,(
% 23.34/3.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.34/3.48    inference(flattening,[],[f32])).
% 23.34/3.48  
% 23.34/3.48  fof(f48,plain,(
% 23.34/3.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.34/3.48    inference(cnf_transformation,[],[f33])).
% 23.34/3.48  
% 23.34/3.48  fof(f68,plain,(
% 23.34/3.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.34/3.48    inference(equality_resolution,[],[f48])).
% 23.34/3.48  
% 23.34/3.48  fof(f12,conjecture,(
% 23.34/3.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))))),
% 23.34/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.48  
% 23.34/3.48  fof(f13,negated_conjecture,(
% 23.34/3.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))))),
% 23.34/3.48    inference(negated_conjecture,[],[f12])).
% 23.34/3.48  
% 23.34/3.48  fof(f18,plain,(
% 23.34/3.48    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 23.34/3.48    inference(ennf_transformation,[],[f13])).
% 23.34/3.48  
% 23.34/3.48  fof(f19,plain,(
% 23.34/3.48    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 23.34/3.48    inference(flattening,[],[f18])).
% 23.34/3.48  
% 23.34/3.48  fof(f34,plain,(
% 23.34/3.48    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5)) & r1_tarski(sK3,sK4) & v1_relat_1(sK5))),
% 23.34/3.48    introduced(choice_axiom,[])).
% 23.34/3.48  
% 23.34/3.48  fof(f35,plain,(
% 23.34/3.48    k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5)) & r1_tarski(sK3,sK4) & v1_relat_1(sK5)),
% 23.34/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f34])).
% 23.34/3.48  
% 23.34/3.48  fof(f58,plain,(
% 23.34/3.48    r1_tarski(sK3,sK4)),
% 23.34/3.48    inference(cnf_transformation,[],[f35])).
% 23.34/3.48  
% 23.34/3.48  fof(f6,axiom,(
% 23.34/3.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 23.34/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.48  
% 23.34/3.48  fof(f51,plain,(
% 23.34/3.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 23.34/3.48    inference(cnf_transformation,[],[f6])).
% 23.34/3.48  
% 23.34/3.48  fof(f2,axiom,(
% 23.34/3.48    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 23.34/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.48  
% 23.34/3.48  fof(f24,plain,(
% 23.34/3.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.34/3.48    inference(nnf_transformation,[],[f2])).
% 23.34/3.48  
% 23.34/3.48  fof(f25,plain,(
% 23.34/3.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.34/3.48    inference(flattening,[],[f24])).
% 23.34/3.48  
% 23.34/3.48  fof(f26,plain,(
% 23.34/3.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.34/3.48    inference(rectify,[],[f25])).
% 23.34/3.48  
% 23.34/3.48  fof(f27,plain,(
% 23.34/3.48    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 23.34/3.48    introduced(choice_axiom,[])).
% 23.34/3.48  
% 23.34/3.48  fof(f28,plain,(
% 23.34/3.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 23.34/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 23.34/3.48  
% 23.34/3.48  fof(f42,plain,(
% 23.34/3.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 23.34/3.48    inference(cnf_transformation,[],[f28])).
% 23.34/3.48  
% 23.34/3.48  fof(f43,plain,(
% 23.34/3.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 23.34/3.48    inference(cnf_transformation,[],[f28])).
% 23.34/3.48  
% 23.34/3.48  fof(f1,axiom,(
% 23.34/3.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 23.34/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.48  
% 23.34/3.48  fof(f15,plain,(
% 23.34/3.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 23.34/3.48    inference(ennf_transformation,[],[f1])).
% 23.34/3.48  
% 23.34/3.48  fof(f20,plain,(
% 23.34/3.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 23.34/3.48    inference(nnf_transformation,[],[f15])).
% 23.34/3.48  
% 23.34/3.48  fof(f21,plain,(
% 23.34/3.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.34/3.48    inference(rectify,[],[f20])).
% 23.34/3.48  
% 23.34/3.48  fof(f22,plain,(
% 23.34/3.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.34/3.48    introduced(choice_axiom,[])).
% 23.34/3.48  
% 23.34/3.48  fof(f23,plain,(
% 23.34/3.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.34/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 23.34/3.48  
% 23.34/3.48  fof(f36,plain,(
% 23.34/3.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 23.34/3.48    inference(cnf_transformation,[],[f23])).
% 23.34/3.48  
% 23.34/3.48  fof(f3,axiom,(
% 23.34/3.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 23.34/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.48  
% 23.34/3.48  fof(f14,plain,(
% 23.34/3.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 23.34/3.48    inference(rectify,[],[f3])).
% 23.34/3.48  
% 23.34/3.48  fof(f45,plain,(
% 23.34/3.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 23.34/3.48    inference(cnf_transformation,[],[f14])).
% 23.34/3.48  
% 23.34/3.48  fof(f7,axiom,(
% 23.34/3.48    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 23.34/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.48  
% 23.34/3.48  fof(f52,plain,(
% 23.34/3.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 23.34/3.48    inference(cnf_transformation,[],[f7])).
% 23.34/3.48  
% 23.34/3.48  fof(f61,plain,(
% 23.34/3.48    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 23.34/3.48    inference(definition_unfolding,[],[f45,f52])).
% 23.34/3.48  
% 23.34/3.48  fof(f40,plain,(
% 23.34/3.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 23.34/3.48    inference(cnf_transformation,[],[f28])).
% 23.34/3.48  
% 23.34/3.48  fof(f65,plain,(
% 23.34/3.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 23.34/3.48    inference(equality_resolution,[],[f40])).
% 23.34/3.48  
% 23.34/3.48  fof(f39,plain,(
% 23.34/3.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 23.34/3.48    inference(cnf_transformation,[],[f28])).
% 23.34/3.48  
% 23.34/3.48  fof(f66,plain,(
% 23.34/3.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 23.34/3.48    inference(equality_resolution,[],[f39])).
% 23.34/3.48  
% 23.34/3.48  fof(f37,plain,(
% 23.34/3.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 23.34/3.48    inference(cnf_transformation,[],[f23])).
% 23.34/3.48  
% 23.34/3.48  fof(f38,plain,(
% 23.34/3.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 23.34/3.48    inference(cnf_transformation,[],[f23])).
% 23.34/3.48  
% 23.34/3.48  fof(f57,plain,(
% 23.34/3.48    v1_relat_1(sK5)),
% 23.34/3.48    inference(cnf_transformation,[],[f35])).
% 23.34/3.48  
% 23.34/3.48  fof(f11,axiom,(
% 23.34/3.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 23.34/3.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.34/3.48  
% 23.34/3.48  fof(f17,plain,(
% 23.34/3.48    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 23.34/3.48    inference(ennf_transformation,[],[f11])).
% 23.34/3.48  
% 23.34/3.48  fof(f56,plain,(
% 23.34/3.48    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 23.34/3.48    inference(cnf_transformation,[],[f17])).
% 23.34/3.48  
% 23.34/3.48  fof(f63,plain,(
% 23.34/3.48    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) | ~v1_relat_1(X2)) )),
% 23.34/3.48    inference(definition_unfolding,[],[f56,f52])).
% 23.34/3.48  
% 23.34/3.48  fof(f59,plain,(
% 23.34/3.48    k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5))),
% 23.34/3.48    inference(cnf_transformation,[],[f35])).
% 23.34/3.48  
% 23.34/3.48  cnf(c_14,plain,
% 23.34/3.48      ( r1_tarski(X0,X0) ),
% 23.34/3.48      inference(cnf_transformation,[],[f68]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_530,plain,
% 23.34/3.48      ( r1_tarski(X0,X0) = iProver_top ),
% 23.34/3.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_19,negated_conjecture,
% 23.34/3.48      ( r1_tarski(sK3,sK4) ),
% 23.34/3.48      inference(cnf_transformation,[],[f58]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_527,plain,
% 23.34/3.48      ( r1_tarski(sK3,sK4) = iProver_top ),
% 23.34/3.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_15,plain,
% 23.34/3.48      ( r1_tarski(k1_xboole_0,X0) ),
% 23.34/3.48      inference(cnf_transformation,[],[f51]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_529,plain,
% 23.34/3.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 23.34/3.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_5,plain,
% 23.34/3.48      ( r2_hidden(sK1(X0,X1,X2),X0)
% 23.34/3.48      | r2_hidden(sK1(X0,X1,X2),X2)
% 23.34/3.48      | k4_xboole_0(X0,X1) = X2 ),
% 23.34/3.48      inference(cnf_transformation,[],[f42]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_537,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X1) = X2
% 23.34/3.48      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 23.34/3.48      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 23.34/3.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_4,plain,
% 23.34/3.48      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 23.34/3.48      | r2_hidden(sK1(X0,X1,X2),X2)
% 23.34/3.48      | k4_xboole_0(X0,X1) = X2 ),
% 23.34/3.48      inference(cnf_transformation,[],[f43]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_538,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X1) = X2
% 23.34/3.48      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
% 23.34/3.48      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 23.34/3.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_2014,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X0) = X1
% 23.34/3.48      | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_537,c_538]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_2,plain,
% 23.34/3.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 23.34/3.48      inference(cnf_transformation,[],[f36]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_540,plain,
% 23.34/3.48      ( r2_hidden(X0,X1) != iProver_top
% 23.34/3.48      | r2_hidden(X0,X2) = iProver_top
% 23.34/3.48      | r1_tarski(X1,X2) != iProver_top ),
% 23.34/3.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_2252,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X0) = X1
% 23.34/3.48      | r2_hidden(sK1(X0,X0,X1),X2) = iProver_top
% 23.34/3.48      | r1_tarski(X1,X2) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_2014,c_540]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_9,plain,
% 23.34/3.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 23.34/3.48      inference(cnf_transformation,[],[f61]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_7,plain,
% 23.34/3.48      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 23.34/3.48      inference(cnf_transformation,[],[f65]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_535,plain,
% 23.34/3.48      ( r2_hidden(X0,X1) != iProver_top
% 23.34/3.48      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 23.34/3.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_2256,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X2)
% 23.34/3.48      | r2_hidden(sK1(X0,X0,k4_xboole_0(X1,X2)),X2) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_2014,c_535]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_2891,plain,
% 23.34/3.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X1,X1)
% 23.34/3.48      | r2_hidden(sK1(X1,X1,X0),k4_xboole_0(X0,X0)) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_9,c_2256]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_2894,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X0) = X1
% 23.34/3.48      | r2_hidden(sK1(X0,X0,X1),k4_xboole_0(X1,X1)) != iProver_top ),
% 23.34/3.48      inference(demodulation,[status(thm)],[c_2891,c_9]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_3938,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X0) = X1
% 23.34/3.48      | r1_tarski(X1,k4_xboole_0(X1,X1)) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_2252,c_2894]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_3976,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_529,c_3938]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_1864,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X1) = X2
% 23.34/3.48      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 23.34/3.48      | r2_hidden(sK1(X0,X1,X2),X3) = iProver_top
% 23.34/3.48      | r1_tarski(X0,X3) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_537,c_540]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_7663,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X1) = X2
% 23.34/3.48      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 23.34/3.48      | r1_tarski(X0,X1) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_1864,c_538]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_8684,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X1) = k4_xboole_0(X2,X3)
% 23.34/3.48      | r2_hidden(sK1(X2,X3,k4_xboole_0(X0,X1)),X1) != iProver_top
% 23.34/3.48      | r1_tarski(X2,X3) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_7663,c_535]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_17587,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X2)
% 23.34/3.48      | r2_hidden(sK1(X1,X2,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = iProver_top
% 23.34/3.48      | r1_tarski(X1,X2) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_537,c_8684]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_8,plain,
% 23.34/3.48      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 23.34/3.48      inference(cnf_transformation,[],[f66]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_534,plain,
% 23.34/3.48      ( r2_hidden(X0,X1) = iProver_top
% 23.34/3.48      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 23.34/3.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_26247,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X1) = k4_xboole_0(X2,X0)
% 23.34/3.48      | r2_hidden(sK1(X0,X1,k4_xboole_0(X2,X0)),X2) = iProver_top
% 23.34/3.48      | r1_tarski(X0,X1) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_17587,c_534]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_4156,plain,
% 23.34/3.48      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.34/3.48      inference(demodulation,[status(thm)],[c_3976,c_9]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_1865,plain,
% 23.34/3.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = X3
% 23.34/3.48      | r2_hidden(sK1(k4_xboole_0(X0,X1),X2,X3),X3) = iProver_top
% 23.34/3.48      | r2_hidden(sK1(k4_xboole_0(X0,X1),X2,X3),X0) = iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_537,c_534]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_38459,plain,
% 23.34/3.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = X2
% 23.34/3.48      | r2_hidden(sK1(k4_xboole_0(X0,X1),X0,X2),X2) = iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_1865,c_538]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_38968,plain,
% 23.34/3.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X2,X3)
% 23.34/3.48      | r2_hidden(sK1(k4_xboole_0(X0,X1),X0,k4_xboole_0(X2,X3)),X3) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_38459,c_535]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_39340,plain,
% 23.34/3.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X2,k1_xboole_0)
% 23.34/3.48      | r2_hidden(sK1(k4_xboole_0(X0,X1),X0,X2),k1_xboole_0) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_4156,c_38968]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_39343,plain,
% 23.34/3.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = X2
% 23.34/3.48      | r2_hidden(sK1(k4_xboole_0(X0,X1),X0,X2),k1_xboole_0) != iProver_top ),
% 23.34/3.48      inference(demodulation,[status(thm)],[c_39340,c_4156]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_39427,plain,
% 23.34/3.48      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) = X1
% 23.34/3.48      | r2_hidden(sK1(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0,X1),X1) = iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_1865,c_39343]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_39447,plain,
% 23.34/3.48      ( k4_xboole_0(k1_xboole_0,X0) = X1
% 23.34/3.48      | r2_hidden(sK1(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0,X1),X1) = iProver_top ),
% 23.34/3.48      inference(demodulation,[status(thm)],[c_39427,c_4156]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_40101,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X1) = k4_xboole_0(k1_xboole_0,X2)
% 23.34/3.48      | r2_hidden(sK1(k4_xboole_0(k1_xboole_0,X2),k1_xboole_0,k4_xboole_0(X0,X1)),X1) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_39447,c_535]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_40683,plain,
% 23.34/3.48      ( k4_xboole_0(X0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X1)
% 23.34/3.48      | r2_hidden(sK1(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_4156,c_40101]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_40686,plain,
% 23.34/3.48      ( k4_xboole_0(k1_xboole_0,X0) = X1
% 23.34/3.48      | r2_hidden(sK1(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0,X1),k1_xboole_0) != iProver_top ),
% 23.34/3.48      inference(demodulation,[status(thm)],[c_40683,c_4156]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_41266,plain,
% 23.34/3.48      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)
% 23.34/3.48      | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0)
% 23.34/3.48      | r1_tarski(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_26247,c_40686]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_41281,plain,
% 23.34/3.48      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0)
% 23.34/3.48      | r1_tarski(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) != iProver_top ),
% 23.34/3.48      inference(demodulation,[status(thm)],[c_41266,c_4156]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_1,plain,
% 23.34/3.48      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 23.34/3.48      inference(cnf_transformation,[],[f37]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_541,plain,
% 23.34/3.48      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 23.34/3.48      | r1_tarski(X0,X1) = iProver_top ),
% 23.34/3.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_1018,plain,
% 23.34/3.48      ( r2_hidden(sK0(k4_xboole_0(X0,X1),X2),X0) = iProver_top
% 23.34/3.48      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_541,c_534]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_0,plain,
% 23.34/3.48      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 23.34/3.48      inference(cnf_transformation,[],[f38]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_542,plain,
% 23.34/3.48      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 23.34/3.48      | r1_tarski(X0,X1) = iProver_top ),
% 23.34/3.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_1830,plain,
% 23.34/3.48      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_1018,c_542]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_41312,plain,
% 23.34/3.48      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 23.34/3.48      inference(forward_subsumption_resolution,
% 23.34/3.48                [status(thm)],
% 23.34/3.48                [c_41281,c_1830]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_41413,plain,
% 23.34/3.48      ( r2_hidden(X0,k4_xboole_0(k1_xboole_0,X1)) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_41312,c_535]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_42374,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X1) = k4_xboole_0(k1_xboole_0,X2)
% 23.34/3.48      | r2_hidden(sK1(X0,X1,k4_xboole_0(k1_xboole_0,X2)),X0) = iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_537,c_41413]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_43531,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X1) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
% 23.34/3.48      | r2_hidden(sK1(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_3976,c_42374]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_43579,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 23.34/3.48      | r2_hidden(sK1(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 23.34/3.48      inference(demodulation,[status(thm)],[c_43531,c_4156]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_43818,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 23.34/3.48      | r2_hidden(sK1(X0,X1,k1_xboole_0),X2) = iProver_top
% 23.34/3.48      | r1_tarski(X0,X2) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_43579,c_540]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_44989,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 23.34/3.48      | r2_hidden(sK1(X0,X1,k1_xboole_0),X2) = iProver_top
% 23.34/3.48      | r1_tarski(X0,X3) != iProver_top
% 23.34/3.48      | r1_tarski(X3,X2) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_43818,c_540]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_57424,plain,
% 23.34/3.48      ( k4_xboole_0(sK3,X0) = k1_xboole_0
% 23.34/3.48      | r2_hidden(sK1(sK3,X0,k1_xboole_0),X1) = iProver_top
% 23.34/3.48      | r1_tarski(sK4,X1) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_527,c_44989]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_57463,plain,
% 23.34/3.48      ( k4_xboole_0(sK3,X0) = k1_xboole_0
% 23.34/3.48      | r2_hidden(sK1(sK3,X0,k1_xboole_0),k1_xboole_0) = iProver_top
% 23.34/3.48      | r1_tarski(sK4,X0) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_57424,c_538]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_43822,plain,
% 23.34/3.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k1_xboole_0
% 23.34/3.48      | r2_hidden(sK1(k4_xboole_0(X0,X1),X2,k1_xboole_0),X1) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_43579,c_535]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_44144,plain,
% 23.34/3.48      ( k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) = k1_xboole_0
% 23.34/3.48      | r2_hidden(sK1(X0,X1,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_4156,c_43822]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_44151,plain,
% 23.34/3.48      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 23.34/3.48      | r2_hidden(sK1(X0,X1,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 23.34/3.48      inference(light_normalisation,[status(thm)],[c_44144,c_4156]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_57783,plain,
% 23.34/3.48      ( k4_xboole_0(sK3,X0) = k1_xboole_0
% 23.34/3.48      | r1_tarski(sK4,X0) != iProver_top ),
% 23.34/3.48      inference(forward_subsumption_resolution,
% 23.34/3.48                [status(thm)],
% 23.34/3.48                [c_57463,c_44151]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_57785,plain,
% 23.34/3.48      ( k4_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_530,c_57783]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_20,negated_conjecture,
% 23.34/3.48      ( v1_relat_1(sK5) ),
% 23.34/3.48      inference(cnf_transformation,[],[f57]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_526,plain,
% 23.34/3.48      ( v1_relat_1(sK5) = iProver_top ),
% 23.34/3.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_17,plain,
% 23.34/3.48      ( ~ v1_relat_1(X0)
% 23.34/3.48      | k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X0) = k8_relat_1(X1,k8_relat_1(X2,X0)) ),
% 23.34/3.48      inference(cnf_transformation,[],[f63]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_528,plain,
% 23.34/3.48      ( k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
% 23.34/3.48      | v1_relat_1(X2) != iProver_top ),
% 23.34/3.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_734,plain,
% 23.34/3.48      ( k8_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),sK5) = k8_relat_1(X0,k8_relat_1(X1,sK5)) ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_526,c_528]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_58229,plain,
% 23.34/3.48      ( k8_relat_1(k4_xboole_0(sK3,k1_xboole_0),sK5) = k8_relat_1(sK3,k8_relat_1(sK4,sK5)) ),
% 23.34/3.48      inference(superposition,[status(thm)],[c_57785,c_734]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_58541,plain,
% 23.34/3.48      ( k8_relat_1(sK3,k8_relat_1(sK4,sK5)) = k8_relat_1(sK3,sK5) ),
% 23.34/3.48      inference(demodulation,[status(thm)],[c_58229,c_4156]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_243,plain,( X0 = X0 ),theory(equality) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_836,plain,
% 23.34/3.48      ( k8_relat_1(sK3,sK5) = k8_relat_1(sK3,sK5) ),
% 23.34/3.48      inference(instantiation,[status(thm)],[c_243]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_244,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_695,plain,
% 23.34/3.48      ( k8_relat_1(sK3,k8_relat_1(sK4,sK5)) != X0
% 23.34/3.48      | k8_relat_1(sK3,sK5) != X0
% 23.34/3.48      | k8_relat_1(sK3,sK5) = k8_relat_1(sK3,k8_relat_1(sK4,sK5)) ),
% 23.34/3.48      inference(instantiation,[status(thm)],[c_244]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_835,plain,
% 23.34/3.48      ( k8_relat_1(sK3,k8_relat_1(sK4,sK5)) != k8_relat_1(sK3,sK5)
% 23.34/3.48      | k8_relat_1(sK3,sK5) = k8_relat_1(sK3,k8_relat_1(sK4,sK5))
% 23.34/3.48      | k8_relat_1(sK3,sK5) != k8_relat_1(sK3,sK5) ),
% 23.34/3.48      inference(instantiation,[status(thm)],[c_695]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(c_18,negated_conjecture,
% 23.34/3.48      ( k8_relat_1(sK3,sK5) != k8_relat_1(sK3,k8_relat_1(sK4,sK5)) ),
% 23.34/3.48      inference(cnf_transformation,[],[f59]) ).
% 23.34/3.48  
% 23.34/3.48  cnf(contradiction,plain,
% 23.34/3.48      ( $false ),
% 23.34/3.48      inference(minisat,[status(thm)],[c_58541,c_836,c_835,c_18]) ).
% 23.34/3.48  
% 23.34/3.48  
% 23.34/3.48  % SZS output end CNFRefutation for theBenchmark.p
% 23.34/3.48  
% 23.34/3.48  ------                               Statistics
% 23.34/3.48  
% 23.34/3.48  ------ Selected
% 23.34/3.48  
% 23.34/3.48  total_time:                             2.55
% 23.34/3.48  
%------------------------------------------------------------------------------
