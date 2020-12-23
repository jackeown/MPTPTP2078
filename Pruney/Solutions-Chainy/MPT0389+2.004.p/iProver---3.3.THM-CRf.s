%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:27 EST 2020

% Result     : Theorem 11.82s
% Output     : CNFRefutation 11.82s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 431 expanded)
%              Number of clauses        :   90 ( 208 expanded)
%              Number of leaves         :   20 (  81 expanded)
%              Depth                    :   20
%              Number of atoms          :  362 (1000 expanded)
%              Number of equality atoms :  172 ( 380 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2))
      & k1_xboole_0 != sK2
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2))
    & k1_xboole_0 != sK2
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f33])).

fof(f56,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f21])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK1(X0,X1))
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f36,f46])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f58,plain,(
    ~ r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_741,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_748,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1667,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_741,c_748])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_734,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_744,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2577,plain,
    ( r1_xboole_0(sK2,X0) = iProver_top
    | r1_xboole_0(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_744])).

cnf(c_2700,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(X0,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1667,c_2577])).

cnf(c_16,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_739,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2717,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_2700,c_739])).

cnf(c_9,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_745,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_746,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1991,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_745,c_746])).

cnf(c_2281,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1991,c_746])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_747,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5220,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X4),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2281,c_747])).

cnf(c_8208,plain,
    ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),X3),X4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5220,c_748])).

cnf(c_9138,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),X3),X4)) = X0 ),
    inference(superposition,[status(thm)],[c_8208,c_739])).

cnf(c_9247,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK3),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X1),X2),X3)) = k4_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_2717,c_9138])).

cnf(c_5221,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2281,c_746])).

cnf(c_8944,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X4),X5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5221,c_746])).

cnf(c_19846,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X4),X5),X6),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8944,c_747])).

cnf(c_31264,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),sK3),X3),X4),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9247,c_19846])).

cnf(c_33221,plain,
    ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),sK3),X3),X4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31264,c_748])).

cnf(c_34238,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),sK3),X3),X4)) = X0 ),
    inference(superposition,[status(thm)],[c_33221,c_739])).

cnf(c_9127,plain,
    ( r1_xboole_0(k4_xboole_0(X0,sK3),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X1),X2),X3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2717,c_8208])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_743,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9717,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9127,c_743])).

cnf(c_19,plain,
    ( r1_tarski(X0,k1_setfam_1(X1))
    | r2_hidden(sK1(X1,X0),X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_736,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_750,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2191,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_750])).

cnf(c_10921,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),sK3)) = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),sK3)))) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),k1_xboole_0),X2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_9717,c_2191])).

cnf(c_11077,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),k1_xboole_0) = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),k1_xboole_0))) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),k1_xboole_0),X2),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10921,c_9717])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_11078,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,X0),X1) = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(k4_xboole_0(k4_xboole_0(sK2,X0),X1))) = iProver_top
    | r2_hidden(sK1(k4_xboole_0(k4_xboole_0(sK2,X0),X1),X2),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11077,c_10])).

cnf(c_17,plain,
    ( r1_tarski(k1_setfam_1(X0),X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_738,plain,
    ( r1_tarski(k1_setfam_1(X0),X1) = iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,sK1(X1,X0))
    | r1_tarski(X0,k1_setfam_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_737,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X1,sK1(X0,X1)) != iProver_top
    | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1988,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top
    | r2_hidden(sK1(X0,k1_setfam_1(X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_738,c_737])).

cnf(c_11255,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,X0),X1) = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(k4_xboole_0(k4_xboole_0(sK2,X0),X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11078,c_1988])).

cnf(c_53566,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),X1),sK3),X2),X3)),X4) = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(k4_xboole_0(sK2,X4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_34238,c_11255])).

cnf(c_2089,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_745,c_747])).

cnf(c_2297,plain,
    ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2089,c_748])).

cnf(c_2701,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,sK3),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2297,c_2577])).

cnf(c_2731,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,sK3),X1)) = sK2 ),
    inference(superposition,[status(thm)],[c_2701,c_739])).

cnf(c_1783,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1667,c_739])).

cnf(c_2296,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1783,c_2089])).

cnf(c_2385,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2296,c_748])).

cnf(c_2966,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2731,c_2385])).

cnf(c_3507,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),X1),X2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2966,c_739])).

cnf(c_53572,plain,
    ( k4_xboole_0(sK2,X0) = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(k4_xboole_0(sK2,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_53566,c_3507])).

cnf(c_53623,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(k4_xboole_0(sK2,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_53572])).

cnf(c_285,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_786,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2))
    | k1_setfam_1(sK2) != X1
    | k1_setfam_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_887,plain,
    ( ~ r1_tarski(X0,k1_setfam_1(X1))
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2))
    | k1_setfam_1(sK2) != k1_setfam_1(X1)
    | k1_setfam_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_1089,plain,
    ( ~ r1_tarski(k1_setfam_1(sK3),k1_setfam_1(X0))
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2))
    | k1_setfam_1(sK2) != k1_setfam_1(X0)
    | k1_setfam_1(sK3) != k1_setfam_1(sK3) ),
    inference(instantiation,[status(thm)],[c_887])).

cnf(c_9518,plain,
    ( ~ r1_tarski(k1_setfam_1(sK3),k1_setfam_1(k4_xboole_0(sK2,k1_xboole_0)))
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2))
    | k1_setfam_1(sK2) != k1_setfam_1(k4_xboole_0(sK2,k1_xboole_0))
    | k1_setfam_1(sK3) != k1_setfam_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1089])).

cnf(c_9521,plain,
    ( k1_setfam_1(sK2) != k1_setfam_1(k4_xboole_0(sK2,k1_xboole_0))
    | k1_setfam_1(sK3) != k1_setfam_1(sK3)
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(k4_xboole_0(sK2,k1_xboole_0))) != iProver_top
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9518])).

cnf(c_281,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_7390,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_7391,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7390])).

cnf(c_286,plain,
    ( X0 != X1
    | k1_setfam_1(X0) = k1_setfam_1(X1) ),
    theory(equality)).

cnf(c_1553,plain,
    ( k1_setfam_1(sK2) = k1_setfam_1(X0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_5422,plain,
    ( k1_setfam_1(sK2) = k1_setfam_1(k4_xboole_0(sK2,k1_xboole_0))
    | sK2 != k4_xboole_0(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_804,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_5428,plain,
    ( sK2 != k4_xboole_0(sK2,k1_xboole_0)
    | k1_xboole_0 != k4_xboole_0(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_3111,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = sK2 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_865,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_1100,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_2143,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) != sK2
    | sK2 = k4_xboole_0(sK2,k1_xboole_0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1100])).

cnf(c_280,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1506,plain,
    ( k1_setfam_1(sK3) = k1_setfam_1(sK3) ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_1422,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_45,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_13,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,plain,
    ( r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_53623,c_9521,c_7391,c_5422,c_5428,c_3111,c_2143,c_1506,c_1422,c_45,c_13,c_24,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.33  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 14:55:21 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 11.82/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.82/2.00  
% 11.82/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.82/2.00  
% 11.82/2.00  ------  iProver source info
% 11.82/2.00  
% 11.82/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.82/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.82/2.00  git: non_committed_changes: false
% 11.82/2.00  git: last_make_outside_of_git: false
% 11.82/2.00  
% 11.82/2.00  ------ 
% 11.82/2.00  
% 11.82/2.00  ------ Input Options
% 11.82/2.00  
% 11.82/2.00  --out_options                           all
% 11.82/2.00  --tptp_safe_out                         true
% 11.82/2.00  --problem_path                          ""
% 11.82/2.00  --include_path                          ""
% 11.82/2.00  --clausifier                            res/vclausify_rel
% 11.82/2.00  --clausifier_options                    ""
% 11.82/2.00  --stdin                                 false
% 11.82/2.00  --stats_out                             all
% 11.82/2.00  
% 11.82/2.00  ------ General Options
% 11.82/2.00  
% 11.82/2.00  --fof                                   false
% 11.82/2.00  --time_out_real                         305.
% 11.82/2.00  --time_out_virtual                      -1.
% 11.82/2.00  --symbol_type_check                     false
% 11.82/2.00  --clausify_out                          false
% 11.82/2.00  --sig_cnt_out                           false
% 11.82/2.00  --trig_cnt_out                          false
% 11.82/2.00  --trig_cnt_out_tolerance                1.
% 11.82/2.00  --trig_cnt_out_sk_spl                   false
% 11.82/2.00  --abstr_cl_out                          false
% 11.82/2.00  
% 11.82/2.00  ------ Global Options
% 11.82/2.00  
% 11.82/2.00  --schedule                              default
% 11.82/2.00  --add_important_lit                     false
% 11.82/2.00  --prop_solver_per_cl                    1000
% 11.82/2.00  --min_unsat_core                        false
% 11.82/2.00  --soft_assumptions                      false
% 11.82/2.00  --soft_lemma_size                       3
% 11.82/2.00  --prop_impl_unit_size                   0
% 11.82/2.00  --prop_impl_unit                        []
% 11.82/2.00  --share_sel_clauses                     true
% 11.82/2.00  --reset_solvers                         false
% 11.82/2.00  --bc_imp_inh                            [conj_cone]
% 11.82/2.00  --conj_cone_tolerance                   3.
% 11.82/2.00  --extra_neg_conj                        none
% 11.82/2.00  --large_theory_mode                     true
% 11.82/2.00  --prolific_symb_bound                   200
% 11.82/2.00  --lt_threshold                          2000
% 11.82/2.00  --clause_weak_htbl                      true
% 11.82/2.00  --gc_record_bc_elim                     false
% 11.82/2.00  
% 11.82/2.00  ------ Preprocessing Options
% 11.82/2.00  
% 11.82/2.00  --preprocessing_flag                    true
% 11.82/2.00  --time_out_prep_mult                    0.1
% 11.82/2.00  --splitting_mode                        input
% 11.82/2.00  --splitting_grd                         true
% 11.82/2.00  --splitting_cvd                         false
% 11.82/2.00  --splitting_cvd_svl                     false
% 11.82/2.00  --splitting_nvd                         32
% 11.82/2.00  --sub_typing                            true
% 11.82/2.00  --prep_gs_sim                           true
% 11.82/2.00  --prep_unflatten                        true
% 11.82/2.00  --prep_res_sim                          true
% 11.82/2.00  --prep_upred                            true
% 11.82/2.00  --prep_sem_filter                       exhaustive
% 11.82/2.00  --prep_sem_filter_out                   false
% 11.82/2.00  --pred_elim                             true
% 11.82/2.00  --res_sim_input                         true
% 11.82/2.00  --eq_ax_congr_red                       true
% 11.82/2.00  --pure_diseq_elim                       true
% 11.82/2.00  --brand_transform                       false
% 11.82/2.00  --non_eq_to_eq                          false
% 11.82/2.00  --prep_def_merge                        true
% 11.82/2.00  --prep_def_merge_prop_impl              false
% 11.82/2.00  --prep_def_merge_mbd                    true
% 11.82/2.00  --prep_def_merge_tr_red                 false
% 11.82/2.00  --prep_def_merge_tr_cl                  false
% 11.82/2.00  --smt_preprocessing                     true
% 11.82/2.00  --smt_ac_axioms                         fast
% 11.82/2.00  --preprocessed_out                      false
% 11.82/2.00  --preprocessed_stats                    false
% 11.82/2.00  
% 11.82/2.00  ------ Abstraction refinement Options
% 11.82/2.00  
% 11.82/2.00  --abstr_ref                             []
% 11.82/2.00  --abstr_ref_prep                        false
% 11.82/2.00  --abstr_ref_until_sat                   false
% 11.82/2.00  --abstr_ref_sig_restrict                funpre
% 11.82/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.82/2.00  --abstr_ref_under                       []
% 11.82/2.00  
% 11.82/2.00  ------ SAT Options
% 11.82/2.00  
% 11.82/2.00  --sat_mode                              false
% 11.82/2.00  --sat_fm_restart_options                ""
% 11.82/2.00  --sat_gr_def                            false
% 11.82/2.00  --sat_epr_types                         true
% 11.82/2.00  --sat_non_cyclic_types                  false
% 11.82/2.00  --sat_finite_models                     false
% 11.82/2.00  --sat_fm_lemmas                         false
% 11.82/2.00  --sat_fm_prep                           false
% 11.82/2.00  --sat_fm_uc_incr                        true
% 11.82/2.00  --sat_out_model                         small
% 11.82/2.00  --sat_out_clauses                       false
% 11.82/2.00  
% 11.82/2.00  ------ QBF Options
% 11.82/2.00  
% 11.82/2.00  --qbf_mode                              false
% 11.82/2.00  --qbf_elim_univ                         false
% 11.82/2.00  --qbf_dom_inst                          none
% 11.82/2.00  --qbf_dom_pre_inst                      false
% 11.82/2.00  --qbf_sk_in                             false
% 11.82/2.00  --qbf_pred_elim                         true
% 11.82/2.00  --qbf_split                             512
% 11.82/2.00  
% 11.82/2.00  ------ BMC1 Options
% 11.82/2.00  
% 11.82/2.00  --bmc1_incremental                      false
% 11.82/2.00  --bmc1_axioms                           reachable_all
% 11.82/2.00  --bmc1_min_bound                        0
% 11.82/2.00  --bmc1_max_bound                        -1
% 11.82/2.00  --bmc1_max_bound_default                -1
% 11.82/2.00  --bmc1_symbol_reachability              true
% 11.82/2.00  --bmc1_property_lemmas                  false
% 11.82/2.00  --bmc1_k_induction                      false
% 11.82/2.00  --bmc1_non_equiv_states                 false
% 11.82/2.00  --bmc1_deadlock                         false
% 11.82/2.00  --bmc1_ucm                              false
% 11.82/2.00  --bmc1_add_unsat_core                   none
% 11.82/2.00  --bmc1_unsat_core_children              false
% 11.82/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.82/2.00  --bmc1_out_stat                         full
% 11.82/2.00  --bmc1_ground_init                      false
% 11.82/2.00  --bmc1_pre_inst_next_state              false
% 11.82/2.00  --bmc1_pre_inst_state                   false
% 11.82/2.00  --bmc1_pre_inst_reach_state             false
% 11.82/2.00  --bmc1_out_unsat_core                   false
% 11.82/2.00  --bmc1_aig_witness_out                  false
% 11.82/2.00  --bmc1_verbose                          false
% 11.82/2.00  --bmc1_dump_clauses_tptp                false
% 11.82/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.82/2.00  --bmc1_dump_file                        -
% 11.82/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.82/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.82/2.00  --bmc1_ucm_extend_mode                  1
% 11.82/2.00  --bmc1_ucm_init_mode                    2
% 11.82/2.00  --bmc1_ucm_cone_mode                    none
% 11.82/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.82/2.00  --bmc1_ucm_relax_model                  4
% 11.82/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.82/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.82/2.00  --bmc1_ucm_layered_model                none
% 11.82/2.00  --bmc1_ucm_max_lemma_size               10
% 11.82/2.00  
% 11.82/2.00  ------ AIG Options
% 11.82/2.00  
% 11.82/2.00  --aig_mode                              false
% 11.82/2.00  
% 11.82/2.00  ------ Instantiation Options
% 11.82/2.00  
% 11.82/2.00  --instantiation_flag                    true
% 11.82/2.00  --inst_sos_flag                         true
% 11.82/2.00  --inst_sos_phase                        true
% 11.82/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.82/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.82/2.00  --inst_lit_sel_side                     num_symb
% 11.82/2.00  --inst_solver_per_active                1400
% 11.82/2.00  --inst_solver_calls_frac                1.
% 11.82/2.00  --inst_passive_queue_type               priority_queues
% 11.82/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.82/2.00  --inst_passive_queues_freq              [25;2]
% 11.82/2.00  --inst_dismatching                      true
% 11.82/2.00  --inst_eager_unprocessed_to_passive     true
% 11.82/2.00  --inst_prop_sim_given                   true
% 11.82/2.00  --inst_prop_sim_new                     false
% 11.82/2.00  --inst_subs_new                         false
% 11.82/2.00  --inst_eq_res_simp                      false
% 11.82/2.00  --inst_subs_given                       false
% 11.82/2.00  --inst_orphan_elimination               true
% 11.82/2.00  --inst_learning_loop_flag               true
% 11.82/2.00  --inst_learning_start                   3000
% 11.82/2.00  --inst_learning_factor                  2
% 11.82/2.00  --inst_start_prop_sim_after_learn       3
% 11.82/2.00  --inst_sel_renew                        solver
% 11.82/2.00  --inst_lit_activity_flag                true
% 11.82/2.00  --inst_restr_to_given                   false
% 11.82/2.00  --inst_activity_threshold               500
% 11.82/2.00  --inst_out_proof                        true
% 11.82/2.00  
% 11.82/2.00  ------ Resolution Options
% 11.82/2.00  
% 11.82/2.00  --resolution_flag                       true
% 11.82/2.00  --res_lit_sel                           adaptive
% 11.82/2.00  --res_lit_sel_side                      none
% 11.82/2.00  --res_ordering                          kbo
% 11.82/2.00  --res_to_prop_solver                    active
% 11.82/2.00  --res_prop_simpl_new                    false
% 11.82/2.00  --res_prop_simpl_given                  true
% 11.82/2.00  --res_passive_queue_type                priority_queues
% 11.82/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.82/2.00  --res_passive_queues_freq               [15;5]
% 11.82/2.00  --res_forward_subs                      full
% 11.82/2.00  --res_backward_subs                     full
% 11.82/2.00  --res_forward_subs_resolution           true
% 11.82/2.00  --res_backward_subs_resolution          true
% 11.82/2.00  --res_orphan_elimination                true
% 11.82/2.00  --res_time_limit                        2.
% 11.82/2.00  --res_out_proof                         true
% 11.82/2.00  
% 11.82/2.00  ------ Superposition Options
% 11.82/2.00  
% 11.82/2.00  --superposition_flag                    true
% 11.82/2.00  --sup_passive_queue_type                priority_queues
% 11.82/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.82/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.82/2.00  --demod_completeness_check              fast
% 11.82/2.00  --demod_use_ground                      true
% 11.82/2.00  --sup_to_prop_solver                    passive
% 11.82/2.00  --sup_prop_simpl_new                    true
% 11.82/2.00  --sup_prop_simpl_given                  true
% 11.82/2.00  --sup_fun_splitting                     true
% 11.82/2.00  --sup_smt_interval                      50000
% 11.82/2.00  
% 11.82/2.00  ------ Superposition Simplification Setup
% 11.82/2.00  
% 11.82/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.82/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.82/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.82/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.82/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.82/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.82/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.82/2.00  --sup_immed_triv                        [TrivRules]
% 11.82/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.82/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.82/2.00  --sup_immed_bw_main                     []
% 11.82/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.82/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.82/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.82/2.00  --sup_input_bw                          []
% 11.82/2.00  
% 11.82/2.00  ------ Combination Options
% 11.82/2.00  
% 11.82/2.00  --comb_res_mult                         3
% 11.82/2.00  --comb_sup_mult                         2
% 11.82/2.00  --comb_inst_mult                        10
% 11.82/2.00  
% 11.82/2.00  ------ Debug Options
% 11.82/2.00  
% 11.82/2.00  --dbg_backtrace                         false
% 11.82/2.00  --dbg_dump_prop_clauses                 false
% 11.82/2.00  --dbg_dump_prop_clauses_file            -
% 11.82/2.00  --dbg_out_stat                          false
% 11.82/2.00  ------ Parsing...
% 11.82/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.82/2.00  
% 11.82/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.82/2.00  
% 11.82/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.82/2.00  
% 11.82/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/2.00  ------ Proving...
% 11.82/2.00  ------ Problem Properties 
% 11.82/2.00  
% 11.82/2.00  
% 11.82/2.00  clauses                                 23
% 11.82/2.00  conjectures                             3
% 11.82/2.00  EPR                                     6
% 11.82/2.00  Horn                                    19
% 11.82/2.00  unary                                   7
% 11.82/2.00  binary                                  9
% 11.82/2.00  lits                                    47
% 11.82/2.00  lits eq                                 10
% 11.82/2.00  fd_pure                                 0
% 11.82/2.00  fd_pseudo                               0
% 11.82/2.00  fd_cond                                 3
% 11.82/2.00  fd_pseudo_cond                          3
% 11.82/2.00  AC symbols                              0
% 11.82/2.00  
% 11.82/2.00  ------ Schedule dynamic 5 is on 
% 11.82/2.00  
% 11.82/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.82/2.00  
% 11.82/2.00  
% 11.82/2.00  ------ 
% 11.82/2.00  Current options:
% 11.82/2.00  ------ 
% 11.82/2.00  
% 11.82/2.00  ------ Input Options
% 11.82/2.00  
% 11.82/2.00  --out_options                           all
% 11.82/2.00  --tptp_safe_out                         true
% 11.82/2.00  --problem_path                          ""
% 11.82/2.00  --include_path                          ""
% 11.82/2.00  --clausifier                            res/vclausify_rel
% 11.82/2.00  --clausifier_options                    ""
% 11.82/2.00  --stdin                                 false
% 11.82/2.00  --stats_out                             all
% 11.82/2.00  
% 11.82/2.00  ------ General Options
% 11.82/2.00  
% 11.82/2.00  --fof                                   false
% 11.82/2.00  --time_out_real                         305.
% 11.82/2.00  --time_out_virtual                      -1.
% 11.82/2.00  --symbol_type_check                     false
% 11.82/2.00  --clausify_out                          false
% 11.82/2.00  --sig_cnt_out                           false
% 11.82/2.00  --trig_cnt_out                          false
% 11.82/2.00  --trig_cnt_out_tolerance                1.
% 11.82/2.00  --trig_cnt_out_sk_spl                   false
% 11.82/2.00  --abstr_cl_out                          false
% 11.82/2.00  
% 11.82/2.00  ------ Global Options
% 11.82/2.00  
% 11.82/2.00  --schedule                              default
% 11.82/2.00  --add_important_lit                     false
% 11.82/2.00  --prop_solver_per_cl                    1000
% 11.82/2.00  --min_unsat_core                        false
% 11.82/2.00  --soft_assumptions                      false
% 11.82/2.00  --soft_lemma_size                       3
% 11.82/2.00  --prop_impl_unit_size                   0
% 11.82/2.00  --prop_impl_unit                        []
% 11.82/2.00  --share_sel_clauses                     true
% 11.82/2.00  --reset_solvers                         false
% 11.82/2.00  --bc_imp_inh                            [conj_cone]
% 11.82/2.00  --conj_cone_tolerance                   3.
% 11.82/2.00  --extra_neg_conj                        none
% 11.82/2.00  --large_theory_mode                     true
% 11.82/2.00  --prolific_symb_bound                   200
% 11.82/2.00  --lt_threshold                          2000
% 11.82/2.00  --clause_weak_htbl                      true
% 11.82/2.00  --gc_record_bc_elim                     false
% 11.82/2.00  
% 11.82/2.00  ------ Preprocessing Options
% 11.82/2.00  
% 11.82/2.00  --preprocessing_flag                    true
% 11.82/2.00  --time_out_prep_mult                    0.1
% 11.82/2.00  --splitting_mode                        input
% 11.82/2.00  --splitting_grd                         true
% 11.82/2.00  --splitting_cvd                         false
% 11.82/2.00  --splitting_cvd_svl                     false
% 11.82/2.00  --splitting_nvd                         32
% 11.82/2.00  --sub_typing                            true
% 11.82/2.00  --prep_gs_sim                           true
% 11.82/2.00  --prep_unflatten                        true
% 11.82/2.00  --prep_res_sim                          true
% 11.82/2.00  --prep_upred                            true
% 11.82/2.00  --prep_sem_filter                       exhaustive
% 11.82/2.00  --prep_sem_filter_out                   false
% 11.82/2.00  --pred_elim                             true
% 11.82/2.00  --res_sim_input                         true
% 11.82/2.00  --eq_ax_congr_red                       true
% 11.82/2.00  --pure_diseq_elim                       true
% 11.82/2.00  --brand_transform                       false
% 11.82/2.00  --non_eq_to_eq                          false
% 11.82/2.00  --prep_def_merge                        true
% 11.82/2.00  --prep_def_merge_prop_impl              false
% 11.82/2.00  --prep_def_merge_mbd                    true
% 11.82/2.00  --prep_def_merge_tr_red                 false
% 11.82/2.00  --prep_def_merge_tr_cl                  false
% 11.82/2.00  --smt_preprocessing                     true
% 11.82/2.00  --smt_ac_axioms                         fast
% 11.82/2.00  --preprocessed_out                      false
% 11.82/2.00  --preprocessed_stats                    false
% 11.82/2.00  
% 11.82/2.00  ------ Abstraction refinement Options
% 11.82/2.00  
% 11.82/2.00  --abstr_ref                             []
% 11.82/2.00  --abstr_ref_prep                        false
% 11.82/2.00  --abstr_ref_until_sat                   false
% 11.82/2.00  --abstr_ref_sig_restrict                funpre
% 11.82/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.82/2.00  --abstr_ref_under                       []
% 11.82/2.00  
% 11.82/2.00  ------ SAT Options
% 11.82/2.00  
% 11.82/2.00  --sat_mode                              false
% 11.82/2.00  --sat_fm_restart_options                ""
% 11.82/2.00  --sat_gr_def                            false
% 11.82/2.00  --sat_epr_types                         true
% 11.82/2.00  --sat_non_cyclic_types                  false
% 11.82/2.00  --sat_finite_models                     false
% 11.82/2.00  --sat_fm_lemmas                         false
% 11.82/2.00  --sat_fm_prep                           false
% 11.82/2.00  --sat_fm_uc_incr                        true
% 11.82/2.00  --sat_out_model                         small
% 11.82/2.00  --sat_out_clauses                       false
% 11.82/2.00  
% 11.82/2.00  ------ QBF Options
% 11.82/2.00  
% 11.82/2.00  --qbf_mode                              false
% 11.82/2.00  --qbf_elim_univ                         false
% 11.82/2.00  --qbf_dom_inst                          none
% 11.82/2.00  --qbf_dom_pre_inst                      false
% 11.82/2.00  --qbf_sk_in                             false
% 11.82/2.00  --qbf_pred_elim                         true
% 11.82/2.00  --qbf_split                             512
% 11.82/2.00  
% 11.82/2.00  ------ BMC1 Options
% 11.82/2.00  
% 11.82/2.00  --bmc1_incremental                      false
% 11.82/2.00  --bmc1_axioms                           reachable_all
% 11.82/2.00  --bmc1_min_bound                        0
% 11.82/2.00  --bmc1_max_bound                        -1
% 11.82/2.00  --bmc1_max_bound_default                -1
% 11.82/2.00  --bmc1_symbol_reachability              true
% 11.82/2.00  --bmc1_property_lemmas                  false
% 11.82/2.00  --bmc1_k_induction                      false
% 11.82/2.00  --bmc1_non_equiv_states                 false
% 11.82/2.00  --bmc1_deadlock                         false
% 11.82/2.00  --bmc1_ucm                              false
% 11.82/2.00  --bmc1_add_unsat_core                   none
% 11.82/2.00  --bmc1_unsat_core_children              false
% 11.82/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.82/2.00  --bmc1_out_stat                         full
% 11.82/2.00  --bmc1_ground_init                      false
% 11.82/2.00  --bmc1_pre_inst_next_state              false
% 11.82/2.00  --bmc1_pre_inst_state                   false
% 11.82/2.00  --bmc1_pre_inst_reach_state             false
% 11.82/2.00  --bmc1_out_unsat_core                   false
% 11.82/2.00  --bmc1_aig_witness_out                  false
% 11.82/2.00  --bmc1_verbose                          false
% 11.82/2.00  --bmc1_dump_clauses_tptp                false
% 11.82/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.82/2.00  --bmc1_dump_file                        -
% 11.82/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.82/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.82/2.00  --bmc1_ucm_extend_mode                  1
% 11.82/2.00  --bmc1_ucm_init_mode                    2
% 11.82/2.00  --bmc1_ucm_cone_mode                    none
% 11.82/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.82/2.00  --bmc1_ucm_relax_model                  4
% 11.82/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.82/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.82/2.00  --bmc1_ucm_layered_model                none
% 11.82/2.00  --bmc1_ucm_max_lemma_size               10
% 11.82/2.00  
% 11.82/2.00  ------ AIG Options
% 11.82/2.00  
% 11.82/2.00  --aig_mode                              false
% 11.82/2.00  
% 11.82/2.00  ------ Instantiation Options
% 11.82/2.00  
% 11.82/2.00  --instantiation_flag                    true
% 11.82/2.00  --inst_sos_flag                         true
% 11.82/2.00  --inst_sos_phase                        true
% 11.82/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.82/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.82/2.00  --inst_lit_sel_side                     none
% 11.82/2.00  --inst_solver_per_active                1400
% 11.82/2.00  --inst_solver_calls_frac                1.
% 11.82/2.00  --inst_passive_queue_type               priority_queues
% 11.82/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.82/2.00  --inst_passive_queues_freq              [25;2]
% 11.82/2.00  --inst_dismatching                      true
% 11.82/2.00  --inst_eager_unprocessed_to_passive     true
% 11.82/2.00  --inst_prop_sim_given                   true
% 11.82/2.00  --inst_prop_sim_new                     false
% 11.82/2.00  --inst_subs_new                         false
% 11.82/2.00  --inst_eq_res_simp                      false
% 11.82/2.00  --inst_subs_given                       false
% 11.82/2.00  --inst_orphan_elimination               true
% 11.82/2.00  --inst_learning_loop_flag               true
% 11.82/2.00  --inst_learning_start                   3000
% 11.82/2.00  --inst_learning_factor                  2
% 11.82/2.00  --inst_start_prop_sim_after_learn       3
% 11.82/2.00  --inst_sel_renew                        solver
% 11.82/2.00  --inst_lit_activity_flag                true
% 11.82/2.00  --inst_restr_to_given                   false
% 11.82/2.00  --inst_activity_threshold               500
% 11.82/2.00  --inst_out_proof                        true
% 11.82/2.00  
% 11.82/2.00  ------ Resolution Options
% 11.82/2.00  
% 11.82/2.00  --resolution_flag                       false
% 11.82/2.00  --res_lit_sel                           adaptive
% 11.82/2.00  --res_lit_sel_side                      none
% 11.82/2.00  --res_ordering                          kbo
% 11.82/2.00  --res_to_prop_solver                    active
% 11.82/2.00  --res_prop_simpl_new                    false
% 11.82/2.00  --res_prop_simpl_given                  true
% 11.82/2.00  --res_passive_queue_type                priority_queues
% 11.82/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.82/2.00  --res_passive_queues_freq               [15;5]
% 11.82/2.00  --res_forward_subs                      full
% 11.82/2.00  --res_backward_subs                     full
% 11.82/2.00  --res_forward_subs_resolution           true
% 11.82/2.00  --res_backward_subs_resolution          true
% 11.82/2.00  --res_orphan_elimination                true
% 11.82/2.00  --res_time_limit                        2.
% 11.82/2.00  --res_out_proof                         true
% 11.82/2.00  
% 11.82/2.00  ------ Superposition Options
% 11.82/2.00  
% 11.82/2.00  --superposition_flag                    true
% 11.82/2.00  --sup_passive_queue_type                priority_queues
% 11.82/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.82/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.82/2.00  --demod_completeness_check              fast
% 11.82/2.00  --demod_use_ground                      true
% 11.82/2.00  --sup_to_prop_solver                    passive
% 11.82/2.00  --sup_prop_simpl_new                    true
% 11.82/2.00  --sup_prop_simpl_given                  true
% 11.82/2.00  --sup_fun_splitting                     true
% 11.82/2.00  --sup_smt_interval                      50000
% 11.82/2.00  
% 11.82/2.00  ------ Superposition Simplification Setup
% 11.82/2.00  
% 11.82/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.82/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.82/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.82/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.82/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.82/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.82/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.82/2.00  --sup_immed_triv                        [TrivRules]
% 11.82/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.82/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.82/2.00  --sup_immed_bw_main                     []
% 11.82/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.82/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.82/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.82/2.00  --sup_input_bw                          []
% 11.82/2.00  
% 11.82/2.00  ------ Combination Options
% 11.82/2.00  
% 11.82/2.00  --comb_res_mult                         3
% 11.82/2.00  --comb_sup_mult                         2
% 11.82/2.00  --comb_inst_mult                        10
% 11.82/2.00  
% 11.82/2.00  ------ Debug Options
% 11.82/2.00  
% 11.82/2.00  --dbg_backtrace                         false
% 11.82/2.00  --dbg_dump_prop_clauses                 false
% 11.82/2.00  --dbg_dump_prop_clauses_file            -
% 11.82/2.00  --dbg_out_stat                          false
% 11.82/2.00  
% 11.82/2.00  
% 11.82/2.00  
% 11.82/2.00  
% 11.82/2.00  ------ Proving...
% 11.82/2.00  
% 11.82/2.00  
% 11.82/2.00  % SZS status Theorem for theBenchmark.p
% 11.82/2.00  
% 11.82/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.82/2.00  
% 11.82/2.00  fof(f9,axiom,(
% 11.82/2.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 11.82/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/2.00  
% 11.82/2.00  fof(f50,plain,(
% 11.82/2.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 11.82/2.00    inference(cnf_transformation,[],[f9])).
% 11.82/2.00  
% 11.82/2.00  fof(f2,axiom,(
% 11.82/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 11.82/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/2.00  
% 11.82/2.00  fof(f15,plain,(
% 11.82/2.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 11.82/2.00    inference(ennf_transformation,[],[f2])).
% 11.82/2.00  
% 11.82/2.00  fof(f41,plain,(
% 11.82/2.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 11.82/2.00    inference(cnf_transformation,[],[f15])).
% 11.82/2.00  
% 11.82/2.00  fof(f13,conjecture,(
% 11.82/2.00    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 11.82/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/2.00  
% 11.82/2.00  fof(f14,negated_conjecture,(
% 11.82/2.00    ~! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 11.82/2.00    inference(negated_conjecture,[],[f13])).
% 11.82/2.00  
% 11.82/2.00  fof(f23,plain,(
% 11.82/2.00    ? [X0,X1] : ((~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0) & r1_tarski(X0,X1))),
% 11.82/2.00    inference(ennf_transformation,[],[f14])).
% 11.82/2.00  
% 11.82/2.00  fof(f24,plain,(
% 11.82/2.00    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r1_tarski(X0,X1))),
% 11.82/2.00    inference(flattening,[],[f23])).
% 11.82/2.00  
% 11.82/2.00  fof(f33,plain,(
% 11.82/2.00    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r1_tarski(X0,X1)) => (~r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) & k1_xboole_0 != sK2 & r1_tarski(sK2,sK3))),
% 11.82/2.00    introduced(choice_axiom,[])).
% 11.82/2.00  
% 11.82/2.00  fof(f34,plain,(
% 11.82/2.00    ~r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) & k1_xboole_0 != sK2 & r1_tarski(sK2,sK3)),
% 11.82/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f33])).
% 11.82/2.00  
% 11.82/2.00  fof(f56,plain,(
% 11.82/2.00    r1_tarski(sK2,sK3)),
% 11.82/2.00    inference(cnf_transformation,[],[f34])).
% 11.82/2.00  
% 11.82/2.00  fof(f7,axiom,(
% 11.82/2.00    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 11.82/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/2.00  
% 11.82/2.00  fof(f17,plain,(
% 11.82/2.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.82/2.00    inference(ennf_transformation,[],[f7])).
% 11.82/2.00  
% 11.82/2.00  fof(f18,plain,(
% 11.82/2.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 11.82/2.00    inference(flattening,[],[f17])).
% 11.82/2.00  
% 11.82/2.00  fof(f47,plain,(
% 11.82/2.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.82/2.00    inference(cnf_transformation,[],[f18])).
% 11.82/2.00  
% 11.82/2.00  fof(f10,axiom,(
% 11.82/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 11.82/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/2.00  
% 11.82/2.00  fof(f30,plain,(
% 11.82/2.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 11.82/2.00    inference(nnf_transformation,[],[f10])).
% 11.82/2.00  
% 11.82/2.00  fof(f51,plain,(
% 11.82/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 11.82/2.00    inference(cnf_transformation,[],[f30])).
% 11.82/2.00  
% 11.82/2.00  fof(f4,axiom,(
% 11.82/2.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.82/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/2.00  
% 11.82/2.00  fof(f44,plain,(
% 11.82/2.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.82/2.00    inference(cnf_transformation,[],[f4])).
% 11.82/2.00  
% 11.82/2.00  fof(f3,axiom,(
% 11.82/2.00    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 11.82/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/2.00  
% 11.82/2.00  fof(f16,plain,(
% 11.82/2.00    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 11.82/2.00    inference(ennf_transformation,[],[f3])).
% 11.82/2.00  
% 11.82/2.00  fof(f42,plain,(
% 11.82/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 11.82/2.00    inference(cnf_transformation,[],[f16])).
% 11.82/2.00  
% 11.82/2.00  fof(f43,plain,(
% 11.82/2.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 11.82/2.00    inference(cnf_transformation,[],[f16])).
% 11.82/2.00  
% 11.82/2.00  fof(f8,axiom,(
% 11.82/2.00    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 11.82/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/2.00  
% 11.82/2.00  fof(f19,plain,(
% 11.82/2.00    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 11.82/2.00    inference(ennf_transformation,[],[f8])).
% 11.82/2.00  
% 11.82/2.00  fof(f49,plain,(
% 11.82/2.00    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 11.82/2.00    inference(cnf_transformation,[],[f19])).
% 11.82/2.00  
% 11.82/2.00  fof(f12,axiom,(
% 11.82/2.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 11.82/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/2.00  
% 11.82/2.00  fof(f21,plain,(
% 11.82/2.00    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 11.82/2.00    inference(ennf_transformation,[],[f12])).
% 11.82/2.00  
% 11.82/2.00  fof(f22,plain,(
% 11.82/2.00    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 11.82/2.00    inference(flattening,[],[f21])).
% 11.82/2.00  
% 11.82/2.00  fof(f31,plain,(
% 11.82/2.00    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)))),
% 11.82/2.00    introduced(choice_axiom,[])).
% 11.82/2.00  
% 11.82/2.00  fof(f32,plain,(
% 11.82/2.00    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK1(X0,X1)) & r2_hidden(sK1(X0,X1),X0)))),
% 11.82/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f31])).
% 11.82/2.00  
% 11.82/2.00  fof(f54,plain,(
% 11.82/2.00    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK1(X0,X1),X0)) )),
% 11.82/2.00    inference(cnf_transformation,[],[f32])).
% 11.82/2.00  
% 11.82/2.00  fof(f1,axiom,(
% 11.82/2.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.82/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/2.00  
% 11.82/2.00  fof(f25,plain,(
% 11.82/2.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.82/2.00    inference(nnf_transformation,[],[f1])).
% 11.82/2.00  
% 11.82/2.00  fof(f26,plain,(
% 11.82/2.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.82/2.00    inference(flattening,[],[f25])).
% 11.82/2.00  
% 11.82/2.00  fof(f27,plain,(
% 11.82/2.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.82/2.00    inference(rectify,[],[f26])).
% 11.82/2.00  
% 11.82/2.00  fof(f28,plain,(
% 11.82/2.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.82/2.00    introduced(choice_axiom,[])).
% 11.82/2.00  
% 11.82/2.00  fof(f29,plain,(
% 11.82/2.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.82/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 11.82/2.00  
% 11.82/2.00  fof(f36,plain,(
% 11.82/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 11.82/2.00    inference(cnf_transformation,[],[f29])).
% 11.82/2.00  
% 11.82/2.00  fof(f6,axiom,(
% 11.82/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.82/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/2.00  
% 11.82/2.00  fof(f46,plain,(
% 11.82/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.82/2.00    inference(cnf_transformation,[],[f6])).
% 11.82/2.00  
% 11.82/2.00  fof(f63,plain,(
% 11.82/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 11.82/2.00    inference(definition_unfolding,[],[f36,f46])).
% 11.82/2.00  
% 11.82/2.00  fof(f66,plain,(
% 11.82/2.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.82/2.00    inference(equality_resolution,[],[f63])).
% 11.82/2.00  
% 11.82/2.00  fof(f5,axiom,(
% 11.82/2.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.82/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/2.00  
% 11.82/2.00  fof(f45,plain,(
% 11.82/2.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.82/2.00    inference(cnf_transformation,[],[f5])).
% 11.82/2.00  
% 11.82/2.00  fof(f11,axiom,(
% 11.82/2.00    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 11.82/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.82/2.00  
% 11.82/2.00  fof(f20,plain,(
% 11.82/2.00    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 11.82/2.00    inference(ennf_transformation,[],[f11])).
% 11.82/2.00  
% 11.82/2.00  fof(f53,plain,(
% 11.82/2.00    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 11.82/2.00    inference(cnf_transformation,[],[f20])).
% 11.82/2.00  
% 11.82/2.00  fof(f55,plain,(
% 11.82/2.00    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK1(X0,X1))) )),
% 11.82/2.00    inference(cnf_transformation,[],[f32])).
% 11.82/2.00  
% 11.82/2.00  fof(f48,plain,(
% 11.82/2.00    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 11.82/2.00    inference(cnf_transformation,[],[f19])).
% 11.82/2.00  
% 11.82/2.00  fof(f68,plain,(
% 11.82/2.00    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 11.82/2.00    inference(equality_resolution,[],[f48])).
% 11.82/2.00  
% 11.82/2.00  fof(f58,plain,(
% 11.82/2.00    ~r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2))),
% 11.82/2.00    inference(cnf_transformation,[],[f34])).
% 11.82/2.00  
% 11.82/2.00  fof(f57,plain,(
% 11.82/2.00    k1_xboole_0 != sK2),
% 11.82/2.00    inference(cnf_transformation,[],[f34])).
% 11.82/2.00  
% 11.82/2.00  cnf(c_14,plain,
% 11.82/2.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 11.82/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_741,plain,
% 11.82/2.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 11.82/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_6,plain,
% 11.82/2.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 11.82/2.00      inference(cnf_transformation,[],[f41]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_748,plain,
% 11.82/2.00      ( r1_xboole_0(X0,X1) != iProver_top
% 11.82/2.00      | r1_xboole_0(X1,X0) = iProver_top ),
% 11.82/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_1667,plain,
% 11.82/2.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_741,c_748]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_22,negated_conjecture,
% 11.82/2.00      ( r1_tarski(sK2,sK3) ),
% 11.82/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_734,plain,
% 11.82/2.00      ( r1_tarski(sK2,sK3) = iProver_top ),
% 11.82/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_11,plain,
% 11.82/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 11.82/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_744,plain,
% 11.82/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.82/2.00      | r1_xboole_0(X1,X2) != iProver_top
% 11.82/2.00      | r1_xboole_0(X0,X2) = iProver_top ),
% 11.82/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_2577,plain,
% 11.82/2.00      ( r1_xboole_0(sK2,X0) = iProver_top
% 11.82/2.00      | r1_xboole_0(sK3,X0) != iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_734,c_744]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_2700,plain,
% 11.82/2.00      ( r1_xboole_0(sK2,k4_xboole_0(X0,sK3)) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_1667,c_2577]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_16,plain,
% 11.82/2.00      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 11.82/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_739,plain,
% 11.82/2.00      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 11.82/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_2717,plain,
% 11.82/2.00      ( k4_xboole_0(sK2,k4_xboole_0(X0,sK3)) = sK2 ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_2700,c_739]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_9,plain,
% 11.82/2.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.82/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_745,plain,
% 11.82/2.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 11.82/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_8,plain,
% 11.82/2.00      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
% 11.82/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_746,plain,
% 11.82/2.00      ( r1_tarski(X0,X1) = iProver_top
% 11.82/2.00      | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 11.82/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_1991,plain,
% 11.82/2.00      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_745,c_746]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_2281,plain,
% 11.82/2.00      ( r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X0) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_1991,c_746]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_7,plain,
% 11.82/2.00      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2) ),
% 11.82/2.00      inference(cnf_transformation,[],[f43]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_747,plain,
% 11.82/2.00      ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
% 11.82/2.00      | r1_xboole_0(X0,X2) = iProver_top ),
% 11.82/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_5220,plain,
% 11.82/2.00      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X4),X1) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_2281,c_747]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_8208,plain,
% 11.82/2.00      ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),X3),X4)) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_5220,c_748]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_9138,plain,
% 11.82/2.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),X3),X4)) = X0 ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_8208,c_739]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_9247,plain,
% 11.82/2.00      ( k4_xboole_0(k4_xboole_0(X0,sK3),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X1),X2),X3)) = k4_xboole_0(X0,sK3) ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_2717,c_9138]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_5221,plain,
% 11.82/2.00      ( r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X4),X0) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_2281,c_746]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_8944,plain,
% 11.82/2.00      ( r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X4),X5),X0) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_5221,c_746]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_19846,plain,
% 11.82/2.00      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3),X4),X5),X6),X1) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_8944,c_747]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_31264,plain,
% 11.82/2.00      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),sK3),X3),X4),X1) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_9247,c_19846]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_33221,plain,
% 11.82/2.00      ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),sK3),X3),X4)) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_31264,c_748]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_34238,plain,
% 11.82/2.00      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),sK3),X3),X4)) = X0 ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_33221,c_739]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_9127,plain,
% 11.82/2.00      ( r1_xboole_0(k4_xboole_0(X0,sK3),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X1),X2),X3)) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_2717,c_8208]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_12,plain,
% 11.82/2.00      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 11.82/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_743,plain,
% 11.82/2.00      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 11.82/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_9717,plain,
% 11.82/2.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),sK3) = k1_xboole_0 ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_9127,c_743]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_19,plain,
% 11.82/2.00      ( r1_tarski(X0,k1_setfam_1(X1))
% 11.82/2.00      | r2_hidden(sK1(X1,X0),X1)
% 11.82/2.00      | k1_xboole_0 = X1 ),
% 11.82/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_736,plain,
% 11.82/2.00      ( k1_xboole_0 = X0
% 11.82/2.00      | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top
% 11.82/2.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 11.82/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_4,plain,
% 11.82/2.00      ( r2_hidden(X0,X1)
% 11.82/2.00      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 11.82/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_750,plain,
% 11.82/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.82/2.00      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 11.82/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_2191,plain,
% 11.82/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 11.82/2.00      | r1_tarski(X2,k1_setfam_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = iProver_top
% 11.82/2.00      | r2_hidden(sK1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_736,c_750]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_10921,plain,
% 11.82/2.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),sK3)) = k1_xboole_0
% 11.82/2.00      | r1_tarski(X2,k1_setfam_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),sK3)))) = iProver_top
% 11.82/2.00      | r2_hidden(sK1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),k1_xboole_0),X2),sK3) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_9717,c_2191]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_11077,plain,
% 11.82/2.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),k1_xboole_0) = k1_xboole_0
% 11.82/2.00      | r1_tarski(X2,k1_setfam_1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),k1_xboole_0))) = iProver_top
% 11.82/2.00      | r2_hidden(sK1(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,X0),X1),k1_xboole_0),X2),sK3) = iProver_top ),
% 11.82/2.00      inference(demodulation,[status(thm)],[c_10921,c_9717]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_10,plain,
% 11.82/2.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.82/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_11078,plain,
% 11.82/2.00      ( k4_xboole_0(k4_xboole_0(sK2,X0),X1) = k1_xboole_0
% 11.82/2.00      | r1_tarski(X2,k1_setfam_1(k4_xboole_0(k4_xboole_0(sK2,X0),X1))) = iProver_top
% 11.82/2.00      | r2_hidden(sK1(k4_xboole_0(k4_xboole_0(sK2,X0),X1),X2),sK3) = iProver_top ),
% 11.82/2.00      inference(demodulation,[status(thm)],[c_11077,c_10]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_17,plain,
% 11.82/2.00      ( r1_tarski(k1_setfam_1(X0),X1) | ~ r2_hidden(X1,X0) ),
% 11.82/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_738,plain,
% 11.82/2.00      ( r1_tarski(k1_setfam_1(X0),X1) = iProver_top
% 11.82/2.00      | r2_hidden(X1,X0) != iProver_top ),
% 11.82/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_18,plain,
% 11.82/2.00      ( ~ r1_tarski(X0,sK1(X1,X0))
% 11.82/2.00      | r1_tarski(X0,k1_setfam_1(X1))
% 11.82/2.00      | k1_xboole_0 = X1 ),
% 11.82/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_737,plain,
% 11.82/2.00      ( k1_xboole_0 = X0
% 11.82/2.00      | r1_tarski(X1,sK1(X0,X1)) != iProver_top
% 11.82/2.00      | r1_tarski(X1,k1_setfam_1(X0)) = iProver_top ),
% 11.82/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_1988,plain,
% 11.82/2.00      ( k1_xboole_0 = X0
% 11.82/2.00      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top
% 11.82/2.00      | r2_hidden(sK1(X0,k1_setfam_1(X1)),X1) != iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_738,c_737]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_11255,plain,
% 11.82/2.00      ( k4_xboole_0(k4_xboole_0(sK2,X0),X1) = k1_xboole_0
% 11.82/2.00      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(k4_xboole_0(k4_xboole_0(sK2,X0),X1))) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_11078,c_1988]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_53566,plain,
% 11.82/2.00      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK2),X1),sK3),X2),X3)),X4) = k1_xboole_0
% 11.82/2.00      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(k4_xboole_0(sK2,X4))) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_34238,c_11255]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_2089,plain,
% 11.82/2.00      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_745,c_747]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_2297,plain,
% 11.82/2.00      ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_2089,c_748]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_2701,plain,
% 11.82/2.00      ( r1_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,sK3),X1)) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_2297,c_2577]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_2731,plain,
% 11.82/2.00      ( k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(X0,sK3),X1)) = sK2 ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_2701,c_739]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_1783,plain,
% 11.82/2.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_1667,c_739]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_2296,plain,
% 11.82/2.00      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_1783,c_2089]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_2385,plain,
% 11.82/2.00      ( r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_2296,c_748]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_2966,plain,
% 11.82/2.00      ( r1_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),X1),X2)) = iProver_top ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_2731,c_2385]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_3507,plain,
% 11.82/2.00      ( k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK3),X1),X2)) = sK2 ),
% 11.82/2.00      inference(superposition,[status(thm)],[c_2966,c_739]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_53572,plain,
% 11.82/2.00      ( k4_xboole_0(sK2,X0) = k1_xboole_0
% 11.82/2.00      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(k4_xboole_0(sK2,X0))) = iProver_top ),
% 11.82/2.00      inference(demodulation,[status(thm)],[c_53566,c_3507]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_53623,plain,
% 11.82/2.00      ( k4_xboole_0(sK2,k1_xboole_0) = k1_xboole_0
% 11.82/2.00      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(k4_xboole_0(sK2,k1_xboole_0))) = iProver_top ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_53572]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_285,plain,
% 11.82/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.82/2.00      theory(equality) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_786,plain,
% 11.82/2.00      ( ~ r1_tarski(X0,X1)
% 11.82/2.00      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2))
% 11.82/2.00      | k1_setfam_1(sK2) != X1
% 11.82/2.00      | k1_setfam_1(sK3) != X0 ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_285]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_887,plain,
% 11.82/2.00      ( ~ r1_tarski(X0,k1_setfam_1(X1))
% 11.82/2.00      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2))
% 11.82/2.00      | k1_setfam_1(sK2) != k1_setfam_1(X1)
% 11.82/2.00      | k1_setfam_1(sK3) != X0 ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_786]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_1089,plain,
% 11.82/2.00      ( ~ r1_tarski(k1_setfam_1(sK3),k1_setfam_1(X0))
% 11.82/2.00      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2))
% 11.82/2.00      | k1_setfam_1(sK2) != k1_setfam_1(X0)
% 11.82/2.00      | k1_setfam_1(sK3) != k1_setfam_1(sK3) ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_887]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_9518,plain,
% 11.82/2.00      ( ~ r1_tarski(k1_setfam_1(sK3),k1_setfam_1(k4_xboole_0(sK2,k1_xboole_0)))
% 11.82/2.00      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2))
% 11.82/2.00      | k1_setfam_1(sK2) != k1_setfam_1(k4_xboole_0(sK2,k1_xboole_0))
% 11.82/2.00      | k1_setfam_1(sK3) != k1_setfam_1(sK3) ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_1089]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_9521,plain,
% 11.82/2.00      ( k1_setfam_1(sK2) != k1_setfam_1(k4_xboole_0(sK2,k1_xboole_0))
% 11.82/2.00      | k1_setfam_1(sK3) != k1_setfam_1(sK3)
% 11.82/2.00      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(k4_xboole_0(sK2,k1_xboole_0))) != iProver_top
% 11.82/2.00      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) = iProver_top ),
% 11.82/2.00      inference(predicate_to_equality,[status(thm)],[c_9518]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_281,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_7390,plain,
% 11.82/2.00      ( k4_xboole_0(sK2,k1_xboole_0) != X0
% 11.82/2.00      | k1_xboole_0 != X0
% 11.82/2.00      | k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0) ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_281]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_7391,plain,
% 11.82/2.00      ( k4_xboole_0(sK2,k1_xboole_0) != k1_xboole_0
% 11.82/2.00      | k1_xboole_0 = k4_xboole_0(sK2,k1_xboole_0)
% 11.82/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_7390]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_286,plain,
% 11.82/2.00      ( X0 != X1 | k1_setfam_1(X0) = k1_setfam_1(X1) ),
% 11.82/2.00      theory(equality) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_1553,plain,
% 11.82/2.00      ( k1_setfam_1(sK2) = k1_setfam_1(X0) | sK2 != X0 ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_286]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_5422,plain,
% 11.82/2.00      ( k1_setfam_1(sK2) = k1_setfam_1(k4_xboole_0(sK2,k1_xboole_0))
% 11.82/2.00      | sK2 != k4_xboole_0(sK2,k1_xboole_0) ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_1553]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_804,plain,
% 11.82/2.00      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_281]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_5428,plain,
% 11.82/2.00      ( sK2 != k4_xboole_0(sK2,k1_xboole_0)
% 11.82/2.00      | k1_xboole_0 != k4_xboole_0(sK2,k1_xboole_0)
% 11.82/2.00      | k1_xboole_0 = sK2 ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_804]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_3111,plain,
% 11.82/2.00      ( k4_xboole_0(sK2,k1_xboole_0) = sK2 ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_865,plain,
% 11.82/2.00      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_281]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_1100,plain,
% 11.82/2.00      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_865]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_2143,plain,
% 11.82/2.00      ( k4_xboole_0(sK2,k1_xboole_0) != sK2
% 11.82/2.00      | sK2 = k4_xboole_0(sK2,k1_xboole_0)
% 11.82/2.00      | sK2 != sK2 ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_1100]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_280,plain,( X0 = X0 ),theory(equality) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_1506,plain,
% 11.82/2.00      ( k1_setfam_1(sK3) = k1_setfam_1(sK3) ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_280]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_1422,plain,
% 11.82/2.00      ( sK2 = sK2 ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_280]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_45,plain,
% 11.82/2.00      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 11.82/2.00      | k1_xboole_0 = k1_xboole_0 ),
% 11.82/2.00      inference(instantiation,[status(thm)],[c_12]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_13,plain,
% 11.82/2.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 11.82/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_20,negated_conjecture,
% 11.82/2.00      ( ~ r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) ),
% 11.82/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_24,plain,
% 11.82/2.00      ( r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
% 11.82/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(c_21,negated_conjecture,
% 11.82/2.00      ( k1_xboole_0 != sK2 ),
% 11.82/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.82/2.00  
% 11.82/2.00  cnf(contradiction,plain,
% 11.82/2.00      ( $false ),
% 11.82/2.00      inference(minisat,
% 11.82/2.00                [status(thm)],
% 11.82/2.00                [c_53623,c_9521,c_7391,c_5422,c_5428,c_3111,c_2143,
% 11.82/2.00                 c_1506,c_1422,c_45,c_13,c_24,c_21]) ).
% 11.82/2.00  
% 11.82/2.00  
% 11.82/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.82/2.00  
% 11.82/2.00  ------                               Statistics
% 11.82/2.00  
% 11.82/2.00  ------ General
% 11.82/2.00  
% 11.82/2.00  abstr_ref_over_cycles:                  0
% 11.82/2.00  abstr_ref_under_cycles:                 0
% 11.82/2.00  gc_basic_clause_elim:                   0
% 11.82/2.00  forced_gc_time:                         0
% 11.82/2.00  parsing_time:                           0.008
% 11.82/2.00  unif_index_cands_time:                  0.
% 11.82/2.00  unif_index_add_time:                    0.
% 11.82/2.00  orderings_time:                         0.
% 11.82/2.00  out_proof_time:                         0.011
% 11.82/2.00  total_time:                             1.296
% 11.82/2.00  num_of_symbols:                         41
% 11.82/2.00  num_of_terms:                           45454
% 11.82/2.00  
% 11.82/2.00  ------ Preprocessing
% 11.82/2.00  
% 11.82/2.00  num_of_splits:                          0
% 11.82/2.00  num_of_split_atoms:                     0
% 11.82/2.00  num_of_reused_defs:                     0
% 11.82/2.00  num_eq_ax_congr_red:                    12
% 11.82/2.00  num_of_sem_filtered_clauses:            1
% 11.82/2.00  num_of_subtypes:                        0
% 11.82/2.00  monotx_restored_types:                  0
% 11.82/2.00  sat_num_of_epr_types:                   0
% 11.82/2.00  sat_num_of_non_cyclic_types:            0
% 11.82/2.00  sat_guarded_non_collapsed_types:        0
% 11.82/2.00  num_pure_diseq_elim:                    0
% 11.82/2.00  simp_replaced_by:                       0
% 11.82/2.00  res_preprocessed:                       84
% 11.82/2.00  prep_upred:                             0
% 11.82/2.00  prep_unflattend:                        0
% 11.82/2.00  smt_new_axioms:                         0
% 11.82/2.00  pred_elim_cands:                        3
% 11.82/2.00  pred_elim:                              0
% 11.82/2.00  pred_elim_cl:                           0
% 11.82/2.00  pred_elim_cycles:                       1
% 11.82/2.00  merged_defs:                            6
% 11.82/2.00  merged_defs_ncl:                        0
% 11.82/2.00  bin_hyper_res:                          6
% 11.82/2.00  prep_cycles:                            3
% 11.82/2.00  pred_elim_time:                         0.
% 11.82/2.00  splitting_time:                         0.
% 11.82/2.00  sem_filter_time:                        0.
% 11.82/2.00  monotx_time:                            0.
% 11.82/2.00  subtype_inf_time:                       0.
% 11.82/2.00  
% 11.82/2.00  ------ Problem properties
% 11.82/2.00  
% 11.82/2.00  clauses:                                23
% 11.82/2.00  conjectures:                            3
% 11.82/2.00  epr:                                    6
% 11.82/2.00  horn:                                   19
% 11.82/2.00  ground:                                 4
% 11.82/2.00  unary:                                  7
% 11.82/2.00  binary:                                 9
% 11.82/2.00  lits:                                   47
% 11.82/2.00  lits_eq:                                10
% 11.82/2.00  fd_pure:                                0
% 11.82/2.00  fd_pseudo:                              0
% 11.82/2.00  fd_cond:                                3
% 11.82/2.00  fd_pseudo_cond:                         3
% 11.82/2.00  ac_symbols:                             0
% 11.82/2.00  
% 11.82/2.00  ------ Propositional Solver
% 11.82/2.00  
% 11.82/2.00  prop_solver_calls:                      29
% 11.82/2.00  prop_fast_solver_calls:                 1077
% 11.82/2.00  smt_solver_calls:                       0
% 11.82/2.00  smt_fast_solver_calls:                  0
% 11.82/2.00  prop_num_of_clauses:                    16192
% 11.82/2.00  prop_preprocess_simplified:             28282
% 11.82/2.00  prop_fo_subsumed:                       15
% 11.82/2.00  prop_solver_time:                       0.
% 11.82/2.00  smt_solver_time:                        0.
% 11.82/2.00  smt_fast_solver_time:                   0.
% 11.82/2.00  prop_fast_solver_time:                  0.
% 11.82/2.00  prop_unsat_core_time:                   0.001
% 11.82/2.00  
% 11.82/2.00  ------ QBF
% 11.82/2.00  
% 11.82/2.00  qbf_q_res:                              0
% 11.82/2.00  qbf_num_tautologies:                    0
% 11.82/2.00  qbf_prep_cycles:                        0
% 11.82/2.00  
% 11.82/2.00  ------ BMC1
% 11.82/2.00  
% 11.82/2.00  bmc1_current_bound:                     -1
% 11.82/2.00  bmc1_last_solved_bound:                 -1
% 11.82/2.00  bmc1_unsat_core_size:                   -1
% 11.82/2.00  bmc1_unsat_core_parents_size:           -1
% 11.82/2.00  bmc1_merge_next_fun:                    0
% 11.82/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.82/2.00  
% 11.82/2.00  ------ Instantiation
% 11.82/2.00  
% 11.82/2.00  inst_num_of_clauses:                    3695
% 11.82/2.00  inst_num_in_passive:                    1865
% 11.82/2.00  inst_num_in_active:                     1409
% 11.82/2.00  inst_num_in_unprocessed:                421
% 11.82/2.00  inst_num_of_loops:                      1790
% 11.82/2.00  inst_num_of_learning_restarts:          0
% 11.82/2.00  inst_num_moves_active_passive:          379
% 11.82/2.00  inst_lit_activity:                      0
% 11.82/2.00  inst_lit_activity_moves:                0
% 11.82/2.00  inst_num_tautologies:                   0
% 11.82/2.00  inst_num_prop_implied:                  0
% 11.82/2.00  inst_num_existing_simplified:           0
% 11.82/2.00  inst_num_eq_res_simplified:             0
% 11.82/2.00  inst_num_child_elim:                    0
% 11.82/2.00  inst_num_of_dismatching_blockings:      2056
% 11.82/2.00  inst_num_of_non_proper_insts:           4610
% 11.82/2.00  inst_num_of_duplicates:                 0
% 11.82/2.00  inst_inst_num_from_inst_to_res:         0
% 11.82/2.00  inst_dismatching_checking_time:         0.
% 11.82/2.00  
% 11.82/2.00  ------ Resolution
% 11.82/2.00  
% 11.82/2.00  res_num_of_clauses:                     0
% 11.82/2.00  res_num_in_passive:                     0
% 11.82/2.00  res_num_in_active:                      0
% 11.82/2.00  res_num_of_loops:                       87
% 11.82/2.00  res_forward_subset_subsumed:            289
% 11.82/2.00  res_backward_subset_subsumed:           2
% 11.82/2.00  res_forward_subsumed:                   0
% 11.82/2.00  res_backward_subsumed:                  0
% 11.82/2.00  res_forward_subsumption_resolution:     0
% 11.82/2.00  res_backward_subsumption_resolution:    0
% 11.82/2.00  res_clause_to_clause_subsumption:       36870
% 11.82/2.00  res_orphan_elimination:                 0
% 11.82/2.00  res_tautology_del:                      267
% 11.82/2.00  res_num_eq_res_simplified:              0
% 11.82/2.00  res_num_sel_changes:                    0
% 11.82/2.00  res_moves_from_active_to_pass:          0
% 11.82/2.00  
% 11.82/2.00  ------ Superposition
% 11.82/2.00  
% 11.82/2.00  sup_time_total:                         0.
% 11.82/2.00  sup_time_generating:                    0.
% 11.82/2.00  sup_time_sim_full:                      0.
% 11.82/2.00  sup_time_sim_immed:                     0.
% 11.82/2.00  
% 11.82/2.00  sup_num_of_clauses:                     1886
% 11.82/2.00  sup_num_in_active:                      351
% 11.82/2.00  sup_num_in_passive:                     1535
% 11.82/2.00  sup_num_of_loops:                       357
% 11.82/2.00  sup_fw_superposition:                   13567
% 11.82/2.00  sup_bw_superposition:                   7038
% 11.82/2.00  sup_immediate_simplified:               5072
% 11.82/2.00  sup_given_eliminated:                   0
% 11.82/2.00  comparisons_done:                       0
% 11.82/2.00  comparisons_avoided:                    0
% 11.82/2.00  
% 11.82/2.00  ------ Simplifications
% 11.82/2.00  
% 11.82/2.00  
% 11.82/2.00  sim_fw_subset_subsumed:                 519
% 11.82/2.00  sim_bw_subset_subsumed:                 29
% 11.82/2.00  sim_fw_subsumed:                        1608
% 11.82/2.00  sim_bw_subsumed:                        57
% 11.82/2.00  sim_fw_subsumption_res:                 0
% 11.82/2.00  sim_bw_subsumption_res:                 0
% 11.82/2.00  sim_tautology_del:                      188
% 11.82/2.00  sim_eq_tautology_del:                   584
% 11.82/2.00  sim_eq_res_simp:                        13
% 11.82/2.00  sim_fw_demodulated:                     2352
% 11.82/2.00  sim_bw_demodulated:                     0
% 11.82/2.00  sim_light_normalised:                   1083
% 11.82/2.00  sim_joinable_taut:                      0
% 11.82/2.00  sim_joinable_simp:                      0
% 11.82/2.00  sim_ac_normalised:                      0
% 11.82/2.00  sim_smt_subsumption:                    0
% 11.82/2.00  
%------------------------------------------------------------------------------
