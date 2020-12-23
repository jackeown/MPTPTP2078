%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:43 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 437 expanded)
%              Number of clauses        :   31 ( 118 expanded)
%              Number of leaves         :   14 ( 110 expanded)
%              Depth                    :   18
%              Number of atoms          :  222 (1134 expanded)
%              Number of equality atoms :  146 ( 821 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) != k1_setfam_1(k2_xboole_0(X0,X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) = k1_setfam_1(k2_xboole_0(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f37])).

fof(f14,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f19,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f29])).

fof(f53,plain,(
    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f67,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_setfam_1(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(definition_unfolding,[],[f53,f37,f46])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != X2 ) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f70,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_xboole_0(k1_tarski(X4),k1_tarski(X1)) != X2 ) ),
    inference(equality_resolution,[],[f63])).

fof(f71,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_xboole_0(k1_tarski(X4),k1_tarski(X1))) ),
    inference(equality_resolution,[],[f70])).

fof(f2,axiom,(
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

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f21])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_18,plain,
    ( k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_17,plain,
    ( k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) = k1_setfam_1(k2_xboole_0(X0,X1))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1264,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1))) = k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1))
    | k1_tarski(X0) = k1_xboole_0
    | k1_xboole_0 = X1 ),
    inference(superposition,[status(thm)],[c_18,c_17])).

cnf(c_3063,plain,
    ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | k1_tarski(X0) = k1_xboole_0
    | k1_tarski(X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18,c_1264])).

cnf(c_19,negated_conjecture,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_setfam_1(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3283,plain,
    ( k1_tarski(sK3) = k1_xboole_0
    | k1_tarski(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3063,c_19])).

cnf(c_3623,plain,
    ( k1_setfam_1(k2_xboole_0(k1_tarski(sK2),k1_xboole_0)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k1_tarski(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3283,c_19])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_38,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_40,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_42,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_43,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_53,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_684,plain,
    ( r2_hidden(X0,k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_850,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_684])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_693,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2796,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(X1,k1_tarski(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_850,c_693])).

cnf(c_3606,plain,
    ( k1_tarski(sK2) = k1_xboole_0
    | r2_hidden(sK3,X0) != iProver_top
    | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3283,c_2796])).

cnf(c_3694,plain,
    ( k1_tarski(sK2) = k1_xboole_0
    | r2_hidden(sK3,k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3606])).

cnf(c_3611,plain,
    ( k1_tarski(sK2) = k1_xboole_0
    | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3283,c_850])).

cnf(c_3716,plain,
    ( k1_tarski(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3623,c_38,c_42,c_43,c_53,c_3694,c_3611])).

cnf(c_3726,plain,
    ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3716,c_850])).

cnf(c_3721,plain,
    ( r2_hidden(sK2,X0) != iProver_top
    | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3716,c_2796])).

cnf(c_3781,plain,
    ( r2_hidden(sK2,k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3721])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3726,c_3781,c_53,c_43,c_42,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.48/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/0.99  
% 2.48/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.48/0.99  
% 2.48/0.99  ------  iProver source info
% 2.48/0.99  
% 2.48/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.48/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.48/0.99  git: non_committed_changes: false
% 2.48/0.99  git: last_make_outside_of_git: false
% 2.48/0.99  
% 2.48/0.99  ------ 
% 2.48/0.99  
% 2.48/0.99  ------ Input Options
% 2.48/0.99  
% 2.48/0.99  --out_options                           all
% 2.48/0.99  --tptp_safe_out                         true
% 2.48/0.99  --problem_path                          ""
% 2.48/0.99  --include_path                          ""
% 2.48/0.99  --clausifier                            res/vclausify_rel
% 2.48/0.99  --clausifier_options                    --mode clausify
% 2.48/0.99  --stdin                                 false
% 2.48/0.99  --stats_out                             all
% 2.48/0.99  
% 2.48/0.99  ------ General Options
% 2.48/0.99  
% 2.48/0.99  --fof                                   false
% 2.48/0.99  --time_out_real                         305.
% 2.48/0.99  --time_out_virtual                      -1.
% 2.48/0.99  --symbol_type_check                     false
% 2.48/0.99  --clausify_out                          false
% 2.48/0.99  --sig_cnt_out                           false
% 2.48/0.99  --trig_cnt_out                          false
% 2.48/0.99  --trig_cnt_out_tolerance                1.
% 2.48/0.99  --trig_cnt_out_sk_spl                   false
% 2.48/0.99  --abstr_cl_out                          false
% 2.48/0.99  
% 2.48/0.99  ------ Global Options
% 2.48/0.99  
% 2.48/0.99  --schedule                              default
% 2.48/0.99  --add_important_lit                     false
% 2.48/0.99  --prop_solver_per_cl                    1000
% 2.48/0.99  --min_unsat_core                        false
% 2.48/0.99  --soft_assumptions                      false
% 2.48/0.99  --soft_lemma_size                       3
% 2.48/0.99  --prop_impl_unit_size                   0
% 2.48/0.99  --prop_impl_unit                        []
% 2.48/0.99  --share_sel_clauses                     true
% 2.48/0.99  --reset_solvers                         false
% 2.48/0.99  --bc_imp_inh                            [conj_cone]
% 2.48/0.99  --conj_cone_tolerance                   3.
% 2.48/0.99  --extra_neg_conj                        none
% 2.48/0.99  --large_theory_mode                     true
% 2.48/0.99  --prolific_symb_bound                   200
% 2.48/0.99  --lt_threshold                          2000
% 2.48/0.99  --clause_weak_htbl                      true
% 2.48/0.99  --gc_record_bc_elim                     false
% 2.48/0.99  
% 2.48/0.99  ------ Preprocessing Options
% 2.48/0.99  
% 2.48/0.99  --preprocessing_flag                    true
% 2.48/0.99  --time_out_prep_mult                    0.1
% 2.48/0.99  --splitting_mode                        input
% 2.48/0.99  --splitting_grd                         true
% 2.48/0.99  --splitting_cvd                         false
% 2.48/0.99  --splitting_cvd_svl                     false
% 2.48/0.99  --splitting_nvd                         32
% 2.48/0.99  --sub_typing                            true
% 2.48/0.99  --prep_gs_sim                           true
% 2.48/0.99  --prep_unflatten                        true
% 2.48/0.99  --prep_res_sim                          true
% 2.48/0.99  --prep_upred                            true
% 2.48/0.99  --prep_sem_filter                       exhaustive
% 2.48/0.99  --prep_sem_filter_out                   false
% 2.48/0.99  --pred_elim                             true
% 2.48/0.99  --res_sim_input                         true
% 2.48/0.99  --eq_ax_congr_red                       true
% 2.48/0.99  --pure_diseq_elim                       true
% 2.48/0.99  --brand_transform                       false
% 2.48/0.99  --non_eq_to_eq                          false
% 2.48/0.99  --prep_def_merge                        true
% 2.48/0.99  --prep_def_merge_prop_impl              false
% 2.48/0.99  --prep_def_merge_mbd                    true
% 2.48/0.99  --prep_def_merge_tr_red                 false
% 2.48/0.99  --prep_def_merge_tr_cl                  false
% 2.48/0.99  --smt_preprocessing                     true
% 2.48/0.99  --smt_ac_axioms                         fast
% 2.48/0.99  --preprocessed_out                      false
% 2.48/0.99  --preprocessed_stats                    false
% 2.48/0.99  
% 2.48/0.99  ------ Abstraction refinement Options
% 2.48/0.99  
% 2.48/0.99  --abstr_ref                             []
% 2.48/0.99  --abstr_ref_prep                        false
% 2.48/0.99  --abstr_ref_until_sat                   false
% 2.48/0.99  --abstr_ref_sig_restrict                funpre
% 2.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/0.99  --abstr_ref_under                       []
% 2.48/0.99  
% 2.48/0.99  ------ SAT Options
% 2.48/0.99  
% 2.48/0.99  --sat_mode                              false
% 2.48/0.99  --sat_fm_restart_options                ""
% 2.48/0.99  --sat_gr_def                            false
% 2.48/0.99  --sat_epr_types                         true
% 2.48/0.99  --sat_non_cyclic_types                  false
% 2.48/0.99  --sat_finite_models                     false
% 2.48/0.99  --sat_fm_lemmas                         false
% 2.48/0.99  --sat_fm_prep                           false
% 2.48/0.99  --sat_fm_uc_incr                        true
% 2.48/0.99  --sat_out_model                         small
% 2.48/0.99  --sat_out_clauses                       false
% 2.48/0.99  
% 2.48/0.99  ------ QBF Options
% 2.48/0.99  
% 2.48/0.99  --qbf_mode                              false
% 2.48/0.99  --qbf_elim_univ                         false
% 2.48/0.99  --qbf_dom_inst                          none
% 2.48/0.99  --qbf_dom_pre_inst                      false
% 2.48/0.99  --qbf_sk_in                             false
% 2.48/0.99  --qbf_pred_elim                         true
% 2.48/0.99  --qbf_split                             512
% 2.48/0.99  
% 2.48/0.99  ------ BMC1 Options
% 2.48/0.99  
% 2.48/0.99  --bmc1_incremental                      false
% 2.48/0.99  --bmc1_axioms                           reachable_all
% 2.48/0.99  --bmc1_min_bound                        0
% 2.48/0.99  --bmc1_max_bound                        -1
% 2.48/0.99  --bmc1_max_bound_default                -1
% 2.48/0.99  --bmc1_symbol_reachability              true
% 2.48/0.99  --bmc1_property_lemmas                  false
% 2.48/0.99  --bmc1_k_induction                      false
% 2.48/0.99  --bmc1_non_equiv_states                 false
% 2.48/0.99  --bmc1_deadlock                         false
% 2.48/0.99  --bmc1_ucm                              false
% 2.48/0.99  --bmc1_add_unsat_core                   none
% 2.48/0.99  --bmc1_unsat_core_children              false
% 2.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/0.99  --bmc1_out_stat                         full
% 2.48/0.99  --bmc1_ground_init                      false
% 2.48/0.99  --bmc1_pre_inst_next_state              false
% 2.48/0.99  --bmc1_pre_inst_state                   false
% 2.48/0.99  --bmc1_pre_inst_reach_state             false
% 2.48/0.99  --bmc1_out_unsat_core                   false
% 2.48/0.99  --bmc1_aig_witness_out                  false
% 2.48/0.99  --bmc1_verbose                          false
% 2.48/0.99  --bmc1_dump_clauses_tptp                false
% 2.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.48/0.99  --bmc1_dump_file                        -
% 2.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.48/0.99  --bmc1_ucm_extend_mode                  1
% 2.48/0.99  --bmc1_ucm_init_mode                    2
% 2.48/0.99  --bmc1_ucm_cone_mode                    none
% 2.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.48/0.99  --bmc1_ucm_relax_model                  4
% 2.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/0.99  --bmc1_ucm_layered_model                none
% 2.48/0.99  --bmc1_ucm_max_lemma_size               10
% 2.48/0.99  
% 2.48/0.99  ------ AIG Options
% 2.48/0.99  
% 2.48/0.99  --aig_mode                              false
% 2.48/0.99  
% 2.48/0.99  ------ Instantiation Options
% 2.48/0.99  
% 2.48/0.99  --instantiation_flag                    true
% 2.48/0.99  --inst_sos_flag                         false
% 2.48/0.99  --inst_sos_phase                        true
% 2.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/0.99  --inst_lit_sel_side                     num_symb
% 2.48/0.99  --inst_solver_per_active                1400
% 2.48/0.99  --inst_solver_calls_frac                1.
% 2.48/0.99  --inst_passive_queue_type               priority_queues
% 2.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/0.99  --inst_passive_queues_freq              [25;2]
% 2.48/0.99  --inst_dismatching                      true
% 2.48/0.99  --inst_eager_unprocessed_to_passive     true
% 2.48/0.99  --inst_prop_sim_given                   true
% 2.48/0.99  --inst_prop_sim_new                     false
% 2.48/0.99  --inst_subs_new                         false
% 2.48/0.99  --inst_eq_res_simp                      false
% 2.48/0.99  --inst_subs_given                       false
% 2.48/0.99  --inst_orphan_elimination               true
% 2.48/0.99  --inst_learning_loop_flag               true
% 2.48/0.99  --inst_learning_start                   3000
% 2.48/0.99  --inst_learning_factor                  2
% 2.48/0.99  --inst_start_prop_sim_after_learn       3
% 2.48/0.99  --inst_sel_renew                        solver
% 2.48/0.99  --inst_lit_activity_flag                true
% 2.48/0.99  --inst_restr_to_given                   false
% 2.48/0.99  --inst_activity_threshold               500
% 2.48/0.99  --inst_out_proof                        true
% 2.48/0.99  
% 2.48/0.99  ------ Resolution Options
% 2.48/0.99  
% 2.48/0.99  --resolution_flag                       true
% 2.48/0.99  --res_lit_sel                           adaptive
% 2.48/0.99  --res_lit_sel_side                      none
% 2.48/0.99  --res_ordering                          kbo
% 2.48/0.99  --res_to_prop_solver                    active
% 2.48/0.99  --res_prop_simpl_new                    false
% 2.48/0.99  --res_prop_simpl_given                  true
% 2.48/0.99  --res_passive_queue_type                priority_queues
% 2.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/0.99  --res_passive_queues_freq               [15;5]
% 2.48/0.99  --res_forward_subs                      full
% 2.48/0.99  --res_backward_subs                     full
% 2.48/0.99  --res_forward_subs_resolution           true
% 2.48/0.99  --res_backward_subs_resolution          true
% 2.48/0.99  --res_orphan_elimination                true
% 2.48/0.99  --res_time_limit                        2.
% 2.48/0.99  --res_out_proof                         true
% 2.48/0.99  
% 2.48/0.99  ------ Superposition Options
% 2.48/0.99  
% 2.48/0.99  --superposition_flag                    true
% 2.48/0.99  --sup_passive_queue_type                priority_queues
% 2.48/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.48/0.99  --demod_completeness_check              fast
% 2.48/0.99  --demod_use_ground                      true
% 2.48/0.99  --sup_to_prop_solver                    passive
% 2.48/0.99  --sup_prop_simpl_new                    true
% 2.48/0.99  --sup_prop_simpl_given                  true
% 2.48/0.99  --sup_fun_splitting                     false
% 2.48/0.99  --sup_smt_interval                      50000
% 2.48/0.99  
% 2.48/0.99  ------ Superposition Simplification Setup
% 2.48/0.99  
% 2.48/0.99  --sup_indices_passive                   []
% 2.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.99  --sup_full_bw                           [BwDemod]
% 2.48/0.99  --sup_immed_triv                        [TrivRules]
% 2.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.99  --sup_immed_bw_main                     []
% 2.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/0.99  
% 2.48/0.99  ------ Combination Options
% 2.48/0.99  
% 2.48/0.99  --comb_res_mult                         3
% 2.48/0.99  --comb_sup_mult                         2
% 2.48/0.99  --comb_inst_mult                        10
% 2.48/0.99  
% 2.48/0.99  ------ Debug Options
% 2.48/0.99  
% 2.48/0.99  --dbg_backtrace                         false
% 2.48/0.99  --dbg_dump_prop_clauses                 false
% 2.48/0.99  --dbg_dump_prop_clauses_file            -
% 2.48/0.99  --dbg_out_stat                          false
% 2.48/0.99  ------ Parsing...
% 2.48/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.48/0.99  
% 2.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.48/0.99  
% 2.48/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.48/0.99  
% 2.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.48/0.99  ------ Proving...
% 2.48/0.99  ------ Problem Properties 
% 2.48/0.99  
% 2.48/0.99  
% 2.48/0.99  clauses                                 20
% 2.48/0.99  conjectures                             1
% 2.48/0.99  EPR                                     1
% 2.48/0.99  Horn                                    15
% 2.48/0.99  unary                                   8
% 2.48/0.99  binary                                  6
% 2.48/0.99  lits                                    39
% 2.48/0.99  lits eq                                 22
% 2.48/0.99  fd_pure                                 0
% 2.48/0.99  fd_pseudo                               0
% 2.48/0.99  fd_cond                                 1
% 2.48/0.99  fd_pseudo_cond                          3
% 2.48/0.99  AC symbols                              0
% 2.48/0.99  
% 2.48/0.99  ------ Schedule dynamic 5 is on 
% 2.48/0.99  
% 2.48/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.48/0.99  
% 2.48/0.99  
% 2.48/0.99  ------ 
% 2.48/0.99  Current options:
% 2.48/0.99  ------ 
% 2.48/0.99  
% 2.48/0.99  ------ Input Options
% 2.48/0.99  
% 2.48/0.99  --out_options                           all
% 2.48/0.99  --tptp_safe_out                         true
% 2.48/0.99  --problem_path                          ""
% 2.48/0.99  --include_path                          ""
% 2.48/0.99  --clausifier                            res/vclausify_rel
% 2.48/0.99  --clausifier_options                    --mode clausify
% 2.48/0.99  --stdin                                 false
% 2.48/0.99  --stats_out                             all
% 2.48/0.99  
% 2.48/0.99  ------ General Options
% 2.48/0.99  
% 2.48/0.99  --fof                                   false
% 2.48/0.99  --time_out_real                         305.
% 2.48/0.99  --time_out_virtual                      -1.
% 2.48/0.99  --symbol_type_check                     false
% 2.48/0.99  --clausify_out                          false
% 2.48/0.99  --sig_cnt_out                           false
% 2.48/0.99  --trig_cnt_out                          false
% 2.48/0.99  --trig_cnt_out_tolerance                1.
% 2.48/0.99  --trig_cnt_out_sk_spl                   false
% 2.48/0.99  --abstr_cl_out                          false
% 2.48/0.99  
% 2.48/0.99  ------ Global Options
% 2.48/0.99  
% 2.48/0.99  --schedule                              default
% 2.48/0.99  --add_important_lit                     false
% 2.48/0.99  --prop_solver_per_cl                    1000
% 2.48/0.99  --min_unsat_core                        false
% 2.48/0.99  --soft_assumptions                      false
% 2.48/0.99  --soft_lemma_size                       3
% 2.48/0.99  --prop_impl_unit_size                   0
% 2.48/0.99  --prop_impl_unit                        []
% 2.48/0.99  --share_sel_clauses                     true
% 2.48/0.99  --reset_solvers                         false
% 2.48/0.99  --bc_imp_inh                            [conj_cone]
% 2.48/0.99  --conj_cone_tolerance                   3.
% 2.48/0.99  --extra_neg_conj                        none
% 2.48/0.99  --large_theory_mode                     true
% 2.48/0.99  --prolific_symb_bound                   200
% 2.48/0.99  --lt_threshold                          2000
% 2.48/0.99  --clause_weak_htbl                      true
% 2.48/0.99  --gc_record_bc_elim                     false
% 2.48/0.99  
% 2.48/0.99  ------ Preprocessing Options
% 2.48/0.99  
% 2.48/0.99  --preprocessing_flag                    true
% 2.48/0.99  --time_out_prep_mult                    0.1
% 2.48/0.99  --splitting_mode                        input
% 2.48/0.99  --splitting_grd                         true
% 2.48/0.99  --splitting_cvd                         false
% 2.48/0.99  --splitting_cvd_svl                     false
% 2.48/0.99  --splitting_nvd                         32
% 2.48/0.99  --sub_typing                            true
% 2.48/0.99  --prep_gs_sim                           true
% 2.48/0.99  --prep_unflatten                        true
% 2.48/0.99  --prep_res_sim                          true
% 2.48/0.99  --prep_upred                            true
% 2.48/0.99  --prep_sem_filter                       exhaustive
% 2.48/0.99  --prep_sem_filter_out                   false
% 2.48/0.99  --pred_elim                             true
% 2.48/0.99  --res_sim_input                         true
% 2.48/0.99  --eq_ax_congr_red                       true
% 2.48/0.99  --pure_diseq_elim                       true
% 2.48/0.99  --brand_transform                       false
% 2.48/0.99  --non_eq_to_eq                          false
% 2.48/0.99  --prep_def_merge                        true
% 2.48/0.99  --prep_def_merge_prop_impl              false
% 2.48/0.99  --prep_def_merge_mbd                    true
% 2.48/0.99  --prep_def_merge_tr_red                 false
% 2.48/0.99  --prep_def_merge_tr_cl                  false
% 2.48/0.99  --smt_preprocessing                     true
% 2.48/0.99  --smt_ac_axioms                         fast
% 2.48/0.99  --preprocessed_out                      false
% 2.48/0.99  --preprocessed_stats                    false
% 2.48/0.99  
% 2.48/0.99  ------ Abstraction refinement Options
% 2.48/0.99  
% 2.48/0.99  --abstr_ref                             []
% 2.48/0.99  --abstr_ref_prep                        false
% 2.48/0.99  --abstr_ref_until_sat                   false
% 2.48/0.99  --abstr_ref_sig_restrict                funpre
% 2.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/0.99  --abstr_ref_under                       []
% 2.48/0.99  
% 2.48/0.99  ------ SAT Options
% 2.48/0.99  
% 2.48/0.99  --sat_mode                              false
% 2.48/0.99  --sat_fm_restart_options                ""
% 2.48/0.99  --sat_gr_def                            false
% 2.48/0.99  --sat_epr_types                         true
% 2.48/0.99  --sat_non_cyclic_types                  false
% 2.48/0.99  --sat_finite_models                     false
% 2.48/0.99  --sat_fm_lemmas                         false
% 2.48/0.99  --sat_fm_prep                           false
% 2.48/0.99  --sat_fm_uc_incr                        true
% 2.48/0.99  --sat_out_model                         small
% 2.48/0.99  --sat_out_clauses                       false
% 2.48/0.99  
% 2.48/0.99  ------ QBF Options
% 2.48/0.99  
% 2.48/0.99  --qbf_mode                              false
% 2.48/0.99  --qbf_elim_univ                         false
% 2.48/0.99  --qbf_dom_inst                          none
% 2.48/0.99  --qbf_dom_pre_inst                      false
% 2.48/0.99  --qbf_sk_in                             false
% 2.48/0.99  --qbf_pred_elim                         true
% 2.48/0.99  --qbf_split                             512
% 2.48/0.99  
% 2.48/0.99  ------ BMC1 Options
% 2.48/0.99  
% 2.48/0.99  --bmc1_incremental                      false
% 2.48/0.99  --bmc1_axioms                           reachable_all
% 2.48/0.99  --bmc1_min_bound                        0
% 2.48/0.99  --bmc1_max_bound                        -1
% 2.48/0.99  --bmc1_max_bound_default                -1
% 2.48/0.99  --bmc1_symbol_reachability              true
% 2.48/0.99  --bmc1_property_lemmas                  false
% 2.48/0.99  --bmc1_k_induction                      false
% 2.48/0.99  --bmc1_non_equiv_states                 false
% 2.48/0.99  --bmc1_deadlock                         false
% 2.48/0.99  --bmc1_ucm                              false
% 2.48/0.99  --bmc1_add_unsat_core                   none
% 2.48/0.99  --bmc1_unsat_core_children              false
% 2.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/0.99  --bmc1_out_stat                         full
% 2.48/0.99  --bmc1_ground_init                      false
% 2.48/0.99  --bmc1_pre_inst_next_state              false
% 2.48/0.99  --bmc1_pre_inst_state                   false
% 2.48/0.99  --bmc1_pre_inst_reach_state             false
% 2.48/0.99  --bmc1_out_unsat_core                   false
% 2.48/0.99  --bmc1_aig_witness_out                  false
% 2.48/0.99  --bmc1_verbose                          false
% 2.48/0.99  --bmc1_dump_clauses_tptp                false
% 2.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.48/0.99  --bmc1_dump_file                        -
% 2.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.48/0.99  --bmc1_ucm_extend_mode                  1
% 2.48/0.99  --bmc1_ucm_init_mode                    2
% 2.48/0.99  --bmc1_ucm_cone_mode                    none
% 2.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.48/0.99  --bmc1_ucm_relax_model                  4
% 2.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/0.99  --bmc1_ucm_layered_model                none
% 2.48/0.99  --bmc1_ucm_max_lemma_size               10
% 2.48/0.99  
% 2.48/0.99  ------ AIG Options
% 2.48/0.99  
% 2.48/0.99  --aig_mode                              false
% 2.48/0.99  
% 2.48/0.99  ------ Instantiation Options
% 2.48/0.99  
% 2.48/0.99  --instantiation_flag                    true
% 2.48/0.99  --inst_sos_flag                         false
% 2.48/0.99  --inst_sos_phase                        true
% 2.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/0.99  --inst_lit_sel_side                     none
% 2.48/0.99  --inst_solver_per_active                1400
% 2.48/0.99  --inst_solver_calls_frac                1.
% 2.48/0.99  --inst_passive_queue_type               priority_queues
% 2.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/0.99  --inst_passive_queues_freq              [25;2]
% 2.48/0.99  --inst_dismatching                      true
% 2.48/0.99  --inst_eager_unprocessed_to_passive     true
% 2.48/0.99  --inst_prop_sim_given                   true
% 2.48/0.99  --inst_prop_sim_new                     false
% 2.48/0.99  --inst_subs_new                         false
% 2.48/0.99  --inst_eq_res_simp                      false
% 2.48/0.99  --inst_subs_given                       false
% 2.48/0.99  --inst_orphan_elimination               true
% 2.48/0.99  --inst_learning_loop_flag               true
% 2.48/0.99  --inst_learning_start                   3000
% 2.48/0.99  --inst_learning_factor                  2
% 2.48/0.99  --inst_start_prop_sim_after_learn       3
% 2.48/0.99  --inst_sel_renew                        solver
% 2.48/0.99  --inst_lit_activity_flag                true
% 2.48/0.99  --inst_restr_to_given                   false
% 2.48/0.99  --inst_activity_threshold               500
% 2.48/0.99  --inst_out_proof                        true
% 2.48/0.99  
% 2.48/0.99  ------ Resolution Options
% 2.48/0.99  
% 2.48/0.99  --resolution_flag                       false
% 2.48/0.99  --res_lit_sel                           adaptive
% 2.48/0.99  --res_lit_sel_side                      none
% 2.48/0.99  --res_ordering                          kbo
% 2.48/0.99  --res_to_prop_solver                    active
% 2.48/0.99  --res_prop_simpl_new                    false
% 2.48/0.99  --res_prop_simpl_given                  true
% 2.48/0.99  --res_passive_queue_type                priority_queues
% 2.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/0.99  --res_passive_queues_freq               [15;5]
% 2.48/0.99  --res_forward_subs                      full
% 2.48/0.99  --res_backward_subs                     full
% 2.48/0.99  --res_forward_subs_resolution           true
% 2.48/0.99  --res_backward_subs_resolution          true
% 2.48/0.99  --res_orphan_elimination                true
% 2.48/0.99  --res_time_limit                        2.
% 2.48/0.99  --res_out_proof                         true
% 2.48/0.99  
% 2.48/0.99  ------ Superposition Options
% 2.48/0.99  
% 2.48/0.99  --superposition_flag                    true
% 2.48/0.99  --sup_passive_queue_type                priority_queues
% 2.48/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.48/0.99  --demod_completeness_check              fast
% 2.48/0.99  --demod_use_ground                      true
% 2.48/0.99  --sup_to_prop_solver                    passive
% 2.48/0.99  --sup_prop_simpl_new                    true
% 2.48/0.99  --sup_prop_simpl_given                  true
% 2.48/0.99  --sup_fun_splitting                     false
% 2.48/0.99  --sup_smt_interval                      50000
% 2.48/0.99  
% 2.48/0.99  ------ Superposition Simplification Setup
% 2.48/0.99  
% 2.48/0.99  --sup_indices_passive                   []
% 2.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.99  --sup_full_bw                           [BwDemod]
% 2.48/0.99  --sup_immed_triv                        [TrivRules]
% 2.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.99  --sup_immed_bw_main                     []
% 2.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/0.99  
% 2.48/0.99  ------ Combination Options
% 2.48/0.99  
% 2.48/0.99  --comb_res_mult                         3
% 2.48/0.99  --comb_sup_mult                         2
% 2.48/0.99  --comb_inst_mult                        10
% 2.48/0.99  
% 2.48/0.99  ------ Debug Options
% 2.48/0.99  
% 2.48/0.99  --dbg_backtrace                         false
% 2.48/0.99  --dbg_dump_prop_clauses                 false
% 2.48/0.99  --dbg_dump_prop_clauses_file            -
% 2.48/0.99  --dbg_out_stat                          false
% 2.48/0.99  
% 2.48/0.99  
% 2.48/0.99  
% 2.48/0.99  
% 2.48/0.99  ------ Proving...
% 2.48/0.99  
% 2.48/0.99  
% 2.48/0.99  % SZS status Theorem for theBenchmark.p
% 2.48/0.99  
% 2.48/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.48/0.99  
% 2.48/0.99  fof(f13,axiom,(
% 2.48/0.99    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f52,plain,(
% 2.48/0.99    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 2.48/0.99    inference(cnf_transformation,[],[f13])).
% 2.48/0.99  
% 2.48/0.99  fof(f12,axiom,(
% 2.48/0.99    ! [X0,X1] : ~(k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) != k1_setfam_1(k2_xboole_0(X0,X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f18,plain,(
% 2.48/0.99    ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.48/0.99    inference(ennf_transformation,[],[f12])).
% 2.48/0.99  
% 2.48/0.99  fof(f51,plain,(
% 2.48/0.99    ( ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k2_xboole_0(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.48/0.99    inference(cnf_transformation,[],[f18])).
% 2.48/0.99  
% 2.48/0.99  fof(f4,axiom,(
% 2.48/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f37,plain,(
% 2.48/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.48/0.99    inference(cnf_transformation,[],[f4])).
% 2.48/0.99  
% 2.48/0.99  fof(f66,plain,(
% 2.48/0.99    ( ! [X0,X1] : (k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) = k1_setfam_1(k2_xboole_0(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.48/0.99    inference(definition_unfolding,[],[f51,f37])).
% 2.48/0.99  
% 2.48/0.99  fof(f14,conjecture,(
% 2.48/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f15,negated_conjecture,(
% 2.48/0.99    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.48/0.99    inference(negated_conjecture,[],[f14])).
% 2.48/0.99  
% 2.48/0.99  fof(f19,plain,(
% 2.48/0.99    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 2.48/0.99    inference(ennf_transformation,[],[f15])).
% 2.48/0.99  
% 2.48/0.99  fof(f29,plain,(
% 2.48/0.99    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3))),
% 2.48/0.99    introduced(choice_axiom,[])).
% 2.48/0.99  
% 2.48/0.99  fof(f30,plain,(
% 2.48/0.99    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3))),
% 2.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f29])).
% 2.48/0.99  
% 2.48/0.99  fof(f53,plain,(
% 2.48/0.99    k3_xboole_0(sK2,sK3) != k1_setfam_1(k2_tarski(sK2,sK3))),
% 2.48/0.99    inference(cnf_transformation,[],[f30])).
% 2.48/0.99  
% 2.48/0.99  fof(f7,axiom,(
% 2.48/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f46,plain,(
% 2.48/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.48/0.99    inference(cnf_transformation,[],[f7])).
% 2.48/0.99  
% 2.48/0.99  fof(f67,plain,(
% 2.48/0.99    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_setfam_1(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))),
% 2.48/0.99    inference(definition_unfolding,[],[f53,f37,f46])).
% 2.48/0.99  
% 2.48/0.99  fof(f5,axiom,(
% 2.48/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f23,plain,(
% 2.48/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.48/0.99    inference(nnf_transformation,[],[f5])).
% 2.48/0.99  
% 2.48/0.99  fof(f38,plain,(
% 2.48/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.48/0.99    inference(cnf_transformation,[],[f23])).
% 2.48/0.99  
% 2.48/0.99  fof(f39,plain,(
% 2.48/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.48/0.99    inference(cnf_transformation,[],[f23])).
% 2.48/0.99  
% 2.48/0.99  fof(f3,axiom,(
% 2.48/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f36,plain,(
% 2.48/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.48/0.99    inference(cnf_transformation,[],[f3])).
% 2.48/0.99  
% 2.48/0.99  fof(f58,plain,(
% 2.48/0.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.48/0.99    inference(definition_unfolding,[],[f36,f37])).
% 2.48/0.99  
% 2.48/0.99  fof(f1,axiom,(
% 2.48/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f20,plain,(
% 2.48/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.48/0.99    inference(nnf_transformation,[],[f1])).
% 2.48/0.99  
% 2.48/0.99  fof(f32,plain,(
% 2.48/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.48/0.99    inference(cnf_transformation,[],[f20])).
% 2.48/0.99  
% 2.48/0.99  fof(f56,plain,(
% 2.48/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.48/0.99    inference(definition_unfolding,[],[f32,f37])).
% 2.48/0.99  
% 2.48/0.99  fof(f8,axiom,(
% 2.48/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f47,plain,(
% 2.48/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.48/0.99    inference(cnf_transformation,[],[f8])).
% 2.48/0.99  
% 2.48/0.99  fof(f55,plain,(
% 2.48/0.99    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 2.48/0.99    inference(definition_unfolding,[],[f47,f46])).
% 2.48/0.99  
% 2.48/0.99  fof(f6,axiom,(
% 2.48/0.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f24,plain,(
% 2.48/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.48/0.99    inference(nnf_transformation,[],[f6])).
% 2.48/0.99  
% 2.48/0.99  fof(f25,plain,(
% 2.48/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.48/0.99    inference(flattening,[],[f24])).
% 2.48/0.99  
% 2.48/0.99  fof(f26,plain,(
% 2.48/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.48/0.99    inference(rectify,[],[f25])).
% 2.48/0.99  
% 2.48/0.99  fof(f27,plain,(
% 2.48/0.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.48/0.99    introduced(choice_axiom,[])).
% 2.48/0.99  
% 2.48/0.99  fof(f28,plain,(
% 2.48/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 2.48/0.99  
% 2.48/0.99  fof(f41,plain,(
% 2.48/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.48/0.99    inference(cnf_transformation,[],[f28])).
% 2.48/0.99  
% 2.48/0.99  fof(f63,plain,(
% 2.48/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) != X2) )),
% 2.48/0.99    inference(definition_unfolding,[],[f41,f46])).
% 2.48/0.99  
% 2.48/0.99  fof(f70,plain,(
% 2.48/0.99    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_xboole_0(k1_tarski(X4),k1_tarski(X1)) != X2) )),
% 2.48/0.99    inference(equality_resolution,[],[f63])).
% 2.48/0.99  
% 2.48/0.99  fof(f71,plain,(
% 2.48/0.99    ( ! [X4,X1] : (r2_hidden(X4,k2_xboole_0(k1_tarski(X4),k1_tarski(X1)))) )),
% 2.48/0.99    inference(equality_resolution,[],[f70])).
% 2.48/0.99  
% 2.48/0.99  fof(f2,axiom,(
% 2.48/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f16,plain,(
% 2.48/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.48/0.99    inference(rectify,[],[f2])).
% 2.48/0.99  
% 2.48/0.99  fof(f17,plain,(
% 2.48/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.48/0.99    inference(ennf_transformation,[],[f16])).
% 2.48/0.99  
% 2.48/0.99  fof(f21,plain,(
% 2.48/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.48/0.99    introduced(choice_axiom,[])).
% 2.48/0.99  
% 2.48/0.99  fof(f22,plain,(
% 2.48/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f21])).
% 2.48/0.99  
% 2.48/0.99  fof(f35,plain,(
% 2.48/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.48/0.99    inference(cnf_transformation,[],[f22])).
% 2.48/0.99  
% 2.48/0.99  cnf(c_18,plain,
% 2.48/0.99      ( k1_setfam_1(k1_tarski(X0)) = X0 ),
% 2.48/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_17,plain,
% 2.48/0.99      ( k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) = k1_setfam_1(k2_xboole_0(X0,X1))
% 2.48/0.99      | k1_xboole_0 = X1
% 2.48/0.99      | k1_xboole_0 = X0 ),
% 2.48/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_1264,plain,
% 2.48/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1))) = k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1))
% 2.48/0.99      | k1_tarski(X0) = k1_xboole_0
% 2.48/0.99      | k1_xboole_0 = X1 ),
% 2.48/0.99      inference(superposition,[status(thm)],[c_18,c_17]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_3063,plain,
% 2.48/0.99      ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
% 2.48/0.99      | k1_tarski(X0) = k1_xboole_0
% 2.48/0.99      | k1_tarski(X1) = k1_xboole_0 ),
% 2.48/0.99      inference(superposition,[status(thm)],[c_18,c_1264]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_19,negated_conjecture,
% 2.48/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != k1_setfam_1(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) ),
% 2.48/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_3283,plain,
% 2.48/0.99      ( k1_tarski(sK3) = k1_xboole_0 | k1_tarski(sK2) = k1_xboole_0 ),
% 2.48/0.99      inference(superposition,[status(thm)],[c_3063,c_19]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_3623,plain,
% 2.48/0.99      ( k1_setfam_1(k2_xboole_0(k1_tarski(sK2),k1_xboole_0)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 2.48/0.99      | k1_tarski(sK2) = k1_xboole_0 ),
% 2.48/0.99      inference(superposition,[status(thm)],[c_3283,c_19]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_9,plain,
% 2.48/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 2.48/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_38,plain,
% 2.48/0.99      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.48/0.99      | k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.48/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_8,plain,
% 2.48/0.99      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.48/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_40,plain,
% 2.48/0.99      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 2.48/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_42,plain,
% 2.48/0.99      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.48/0.99      | r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.48/0.99      inference(instantiation,[status(thm)],[c_40]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_7,plain,
% 2.48/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.48/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_43,plain,
% 2.48/0.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 2.48/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_2,plain,
% 2.48/0.99      ( r1_xboole_0(X0,X1)
% 2.48/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 2.48/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_53,plain,
% 2.48/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.48/0.99      | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
% 2.48/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_1,plain,
% 2.48/0.99      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) = k1_tarski(X0) ),
% 2.48/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_14,plain,
% 2.48/0.99      ( r2_hidden(X0,k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
% 2.48/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_684,plain,
% 2.48/0.99      ( r2_hidden(X0,k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = iProver_top ),
% 2.48/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_850,plain,
% 2.48/0.99      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 2.48/0.99      inference(superposition,[status(thm)],[c_1,c_684]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_4,plain,
% 2.48/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 2.48/0.99      inference(cnf_transformation,[],[f35]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_693,plain,
% 2.48/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.48/0.99      | r2_hidden(X0,X2) != iProver_top
% 2.48/0.99      | r1_xboole_0(X2,X1) != iProver_top ),
% 2.48/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_2796,plain,
% 2.48/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.48/0.99      | r1_xboole_0(X1,k1_tarski(X0)) != iProver_top ),
% 2.48/0.99      inference(superposition,[status(thm)],[c_850,c_693]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_3606,plain,
% 2.48/0.99      ( k1_tarski(sK2) = k1_xboole_0
% 2.48/0.99      | r2_hidden(sK3,X0) != iProver_top
% 2.48/0.99      | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
% 2.48/0.99      inference(superposition,[status(thm)],[c_3283,c_2796]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_3694,plain,
% 2.48/0.99      ( k1_tarski(sK2) = k1_xboole_0
% 2.48/0.99      | r2_hidden(sK3,k1_xboole_0) != iProver_top
% 2.48/0.99      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.48/0.99      inference(instantiation,[status(thm)],[c_3606]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_3611,plain,
% 2.48/0.99      ( k1_tarski(sK2) = k1_xboole_0
% 2.48/0.99      | r2_hidden(sK3,k1_xboole_0) = iProver_top ),
% 2.48/0.99      inference(superposition,[status(thm)],[c_3283,c_850]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_3716,plain,
% 2.48/0.99      ( k1_tarski(sK2) = k1_xboole_0 ),
% 2.48/0.99      inference(global_propositional_subsumption,
% 2.48/0.99                [status(thm)],
% 2.48/0.99                [c_3623,c_38,c_42,c_43,c_53,c_3694,c_3611]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_3726,plain,
% 2.48/0.99      ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 2.48/0.99      inference(superposition,[status(thm)],[c_3716,c_850]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_3721,plain,
% 2.48/0.99      ( r2_hidden(sK2,X0) != iProver_top
% 2.48/0.99      | r1_xboole_0(X0,k1_xboole_0) != iProver_top ),
% 2.48/0.99      inference(superposition,[status(thm)],[c_3716,c_2796]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_3781,plain,
% 2.48/0.99      ( r2_hidden(sK2,k1_xboole_0) != iProver_top
% 2.48/0.99      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.48/0.99      inference(instantiation,[status(thm)],[c_3721]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(contradiction,plain,
% 2.48/0.99      ( $false ),
% 2.48/0.99      inference(minisat,[status(thm)],[c_3726,c_3781,c_53,c_43,c_42,c_38]) ).
% 2.48/0.99  
% 2.48/0.99  
% 2.48/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.48/0.99  
% 2.48/0.99  ------                               Statistics
% 2.48/0.99  
% 2.48/0.99  ------ General
% 2.48/0.99  
% 2.48/0.99  abstr_ref_over_cycles:                  0
% 2.48/0.99  abstr_ref_under_cycles:                 0
% 2.48/0.99  gc_basic_clause_elim:                   0
% 2.48/0.99  forced_gc_time:                         0
% 2.48/0.99  parsing_time:                           0.009
% 2.48/0.99  unif_index_cands_time:                  0.
% 2.48/0.99  unif_index_add_time:                    0.
% 2.48/0.99  orderings_time:                         0.
% 2.48/0.99  out_proof_time:                         0.011
% 2.48/0.99  total_time:                             0.179
% 2.48/0.99  num_of_symbols:                         44
% 2.48/0.99  num_of_terms:                           4827
% 2.48/0.99  
% 2.48/0.99  ------ Preprocessing
% 2.48/0.99  
% 2.48/0.99  num_of_splits:                          0
% 2.48/0.99  num_of_split_atoms:                     0
% 2.48/0.99  num_of_reused_defs:                     0
% 2.48/0.99  num_eq_ax_congr_red:                    22
% 2.48/0.99  num_of_sem_filtered_clauses:            1
% 2.48/0.99  num_of_subtypes:                        0
% 2.48/0.99  monotx_restored_types:                  0
% 2.48/0.99  sat_num_of_epr_types:                   0
% 2.48/0.99  sat_num_of_non_cyclic_types:            0
% 2.48/0.99  sat_guarded_non_collapsed_types:        0
% 2.48/0.99  num_pure_diseq_elim:                    0
% 2.48/0.99  simp_replaced_by:                       0
% 2.48/0.99  res_preprocessed:                       77
% 2.48/0.99  prep_upred:                             0
% 2.48/0.99  prep_unflattend:                        8
% 2.48/0.99  smt_new_axioms:                         0
% 2.48/0.99  pred_elim_cands:                        2
% 2.48/0.99  pred_elim:                              0
% 2.48/0.99  pred_elim_cl:                           0
% 2.48/0.99  pred_elim_cycles:                       1
% 2.48/0.99  merged_defs:                            12
% 2.48/0.99  merged_defs_ncl:                        0
% 2.48/0.99  bin_hyper_res:                          12
% 2.48/0.99  prep_cycles:                            3
% 2.48/0.99  pred_elim_time:                         0.003
% 2.48/0.99  splitting_time:                         0.
% 2.48/0.99  sem_filter_time:                        0.
% 2.48/0.99  monotx_time:                            0.001
% 2.48/0.99  subtype_inf_time:                       0.
% 2.48/0.99  
% 2.48/0.99  ------ Problem properties
% 2.48/0.99  
% 2.48/0.99  clauses:                                20
% 2.48/0.99  conjectures:                            1
% 2.48/0.99  epr:                                    1
% 2.48/0.99  horn:                                   15
% 2.48/0.99  ground:                                 1
% 2.48/0.99  unary:                                  8
% 2.48/0.99  binary:                                 6
% 2.48/0.99  lits:                                   39
% 2.48/0.99  lits_eq:                                22
% 2.48/0.99  fd_pure:                                0
% 2.48/0.99  fd_pseudo:                              0
% 2.48/0.99  fd_cond:                                1
% 2.48/0.99  fd_pseudo_cond:                         3
% 2.48/0.99  ac_symbols:                             0
% 2.48/0.99  
% 2.48/0.99  ------ Propositional Solver
% 2.48/0.99  
% 2.48/0.99  prop_solver_calls:                      22
% 2.48/0.99  prop_fast_solver_calls:                 411
% 2.48/0.99  smt_solver_calls:                       0
% 2.48/0.99  smt_fast_solver_calls:                  0
% 2.48/0.99  prop_num_of_clauses:                    1336
% 2.48/0.99  prop_preprocess_simplified:             4312
% 2.48/0.99  prop_fo_subsumed:                       1
% 2.48/0.99  prop_solver_time:                       0.
% 2.48/0.99  smt_solver_time:                        0.
% 2.48/0.99  smt_fast_solver_time:                   0.
% 2.48/0.99  prop_fast_solver_time:                  0.
% 2.48/0.99  prop_unsat_core_time:                   0.
% 2.48/0.99  
% 2.48/0.99  ------ QBF
% 2.48/0.99  
% 2.48/0.99  qbf_q_res:                              0
% 2.48/0.99  qbf_num_tautologies:                    0
% 2.48/0.99  qbf_prep_cycles:                        0
% 2.48/0.99  
% 2.48/0.99  ------ BMC1
% 2.48/0.99  
% 2.48/0.99  bmc1_current_bound:                     -1
% 2.48/0.99  bmc1_last_solved_bound:                 -1
% 2.48/0.99  bmc1_unsat_core_size:                   -1
% 2.48/0.99  bmc1_unsat_core_parents_size:           -1
% 2.48/0.99  bmc1_merge_next_fun:                    0
% 2.48/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.48/0.99  
% 2.48/0.99  ------ Instantiation
% 2.48/0.99  
% 2.48/0.99  inst_num_of_clauses:                    415
% 2.48/0.99  inst_num_in_passive:                    114
% 2.48/0.99  inst_num_in_active:                     169
% 2.48/0.99  inst_num_in_unprocessed:                132
% 2.48/0.99  inst_num_of_loops:                      190
% 2.48/0.99  inst_num_of_learning_restarts:          0
% 2.48/0.99  inst_num_moves_active_passive:          20
% 2.48/0.99  inst_lit_activity:                      0
% 2.48/1.00  inst_lit_activity_moves:                0
% 2.48/1.00  inst_num_tautologies:                   0
% 2.48/1.00  inst_num_prop_implied:                  0
% 2.48/1.00  inst_num_existing_simplified:           0
% 2.48/1.00  inst_num_eq_res_simplified:             0
% 2.48/1.00  inst_num_child_elim:                    0
% 2.48/1.00  inst_num_of_dismatching_blockings:      146
% 2.48/1.00  inst_num_of_non_proper_insts:           443
% 2.48/1.00  inst_num_of_duplicates:                 0
% 2.48/1.00  inst_inst_num_from_inst_to_res:         0
% 2.48/1.00  inst_dismatching_checking_time:         0.
% 2.48/1.00  
% 2.48/1.00  ------ Resolution
% 2.48/1.00  
% 2.48/1.00  res_num_of_clauses:                     0
% 2.48/1.00  res_num_in_passive:                     0
% 2.48/1.00  res_num_in_active:                      0
% 2.48/1.00  res_num_of_loops:                       80
% 2.48/1.00  res_forward_subset_subsumed:            55
% 2.48/1.00  res_backward_subset_subsumed:           0
% 2.48/1.00  res_forward_subsumed:                   0
% 2.48/1.00  res_backward_subsumed:                  0
% 2.48/1.00  res_forward_subsumption_resolution:     0
% 2.48/1.00  res_backward_subsumption_resolution:    0
% 2.48/1.00  res_clause_to_clause_subsumption:       299
% 2.48/1.00  res_orphan_elimination:                 0
% 2.48/1.00  res_tautology_del:                      37
% 2.48/1.00  res_num_eq_res_simplified:              0
% 2.48/1.00  res_num_sel_changes:                    0
% 2.48/1.00  res_moves_from_active_to_pass:          0
% 2.48/1.00  
% 2.48/1.00  ------ Superposition
% 2.48/1.00  
% 2.48/1.00  sup_time_total:                         0.
% 2.48/1.00  sup_time_generating:                    0.
% 2.48/1.00  sup_time_sim_full:                      0.
% 2.48/1.00  sup_time_sim_immed:                     0.
% 2.48/1.00  
% 2.48/1.00  sup_num_of_clauses:                     95
% 2.48/1.00  sup_num_in_active:                      34
% 2.48/1.00  sup_num_in_passive:                     61
% 2.48/1.00  sup_num_of_loops:                       37
% 2.48/1.00  sup_fw_superposition:                   49
% 2.48/1.00  sup_bw_superposition:                   88
% 2.48/1.00  sup_immediate_simplified:               21
% 2.48/1.00  sup_given_eliminated:                   0
% 2.48/1.00  comparisons_done:                       0
% 2.48/1.00  comparisons_avoided:                    24
% 2.48/1.00  
% 2.48/1.00  ------ Simplifications
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  sim_fw_subset_subsumed:                 6
% 2.48/1.00  sim_bw_subset_subsumed:                 7
% 2.48/1.00  sim_fw_subsumed:                        1
% 2.48/1.00  sim_bw_subsumed:                        0
% 2.48/1.00  sim_fw_subsumption_res:                 0
% 2.48/1.00  sim_bw_subsumption_res:                 0
% 2.48/1.00  sim_tautology_del:                      0
% 2.48/1.00  sim_eq_tautology_del:                   6
% 2.48/1.00  sim_eq_res_simp:                        0
% 2.48/1.00  sim_fw_demodulated:                     6
% 2.48/1.00  sim_bw_demodulated:                     6
% 2.48/1.00  sim_light_normalised:                   10
% 2.48/1.00  sim_joinable_taut:                      0
% 2.48/1.00  sim_joinable_simp:                      0
% 2.48/1.00  sim_ac_normalised:                      0
% 2.48/1.00  sim_smt_subsumption:                    0
% 2.48/1.00  
%------------------------------------------------------------------------------
