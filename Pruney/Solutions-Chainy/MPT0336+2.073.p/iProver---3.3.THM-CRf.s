%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:45 EST 2020

% Result     : Theorem 7.55s
% Output     : CNFRefutation 7.55s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 154 expanded)
%              Number of clauses        :   43 (  53 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :   16
%              Number of atoms          :  190 ( 371 expanded)
%              Number of equality atoms :   57 (  85 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
      & r1_xboole_0(sK3,sK2)
      & r2_hidden(sK4,sK3)
      & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    & r1_xboole_0(sK3,sK2)
    & r2_hidden(sK4,sK3)
    & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f25])).

fof(f44,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f51,plain,(
    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_enumset1(sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f44,f35,f48])).

fof(f46,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_enumset1(X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
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

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f22])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f35,f35])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_enumset1(sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_632,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_enumset1(sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_634,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_648,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1344,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_634,c_648])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_636,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_637,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1315,plain,
    ( k4_xboole_0(k1_enumset1(X0,X0,X0),X1) = k1_enumset1(X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_636,c_637])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_633,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_647,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3293,plain,
    ( r2_hidden(sK4,X0) != iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_633,c_647])).

cnf(c_4442,plain,
    ( k4_xboole_0(k1_enumset1(sK4,sK4,sK4),X0) = k1_enumset1(sK4,sK4,sK4)
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_3293])).

cnf(c_5203,plain,
    ( k4_xboole_0(k1_enumset1(sK4,sK4,sK4),sK2) = k1_enumset1(sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_1344,c_4442])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_644,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5237,plain,
    ( r1_tarski(X0,k1_enumset1(sK4,sK4,sK4)) != iProver_top
    | r1_xboole_0(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5203,c_644])).

cnf(c_5551,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_632,c_5237])).

cnf(c_5733,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5551,c_648])).

cnf(c_5743,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_5733,c_637])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_642,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_868,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_642])).

cnf(c_1045,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_868])).

cnf(c_2440,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_644])).

cnf(c_30723,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5743,c_2440])).

cnf(c_1096,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1097,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | r1_xboole_0(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1096])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_847,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
    | ~ r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_848,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) = iProver_top
    | r1_xboole_0(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_750,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_751,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) = iProver_top
    | r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_21,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_20,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30723,c_1097,c_848,c_751,c_21,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:35:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.55/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.55/1.48  
% 7.55/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.55/1.48  
% 7.55/1.48  ------  iProver source info
% 7.55/1.48  
% 7.55/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.55/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.55/1.48  git: non_committed_changes: false
% 7.55/1.48  git: last_make_outside_of_git: false
% 7.55/1.48  
% 7.55/1.48  ------ 
% 7.55/1.48  
% 7.55/1.48  ------ Input Options
% 7.55/1.48  
% 7.55/1.48  --out_options                           all
% 7.55/1.48  --tptp_safe_out                         true
% 7.55/1.48  --problem_path                          ""
% 7.55/1.48  --include_path                          ""
% 7.55/1.48  --clausifier                            res/vclausify_rel
% 7.55/1.48  --clausifier_options                    --mode clausify
% 7.55/1.48  --stdin                                 false
% 7.55/1.48  --stats_out                             all
% 7.55/1.48  
% 7.55/1.48  ------ General Options
% 7.55/1.48  
% 7.55/1.48  --fof                                   false
% 7.55/1.48  --time_out_real                         305.
% 7.55/1.48  --time_out_virtual                      -1.
% 7.55/1.48  --symbol_type_check                     false
% 7.55/1.48  --clausify_out                          false
% 7.55/1.48  --sig_cnt_out                           false
% 7.55/1.48  --trig_cnt_out                          false
% 7.55/1.48  --trig_cnt_out_tolerance                1.
% 7.55/1.48  --trig_cnt_out_sk_spl                   false
% 7.55/1.48  --abstr_cl_out                          false
% 7.55/1.48  
% 7.55/1.48  ------ Global Options
% 7.55/1.48  
% 7.55/1.48  --schedule                              default
% 7.55/1.48  --add_important_lit                     false
% 7.55/1.48  --prop_solver_per_cl                    1000
% 7.55/1.48  --min_unsat_core                        false
% 7.55/1.48  --soft_assumptions                      false
% 7.55/1.48  --soft_lemma_size                       3
% 7.55/1.48  --prop_impl_unit_size                   0
% 7.55/1.48  --prop_impl_unit                        []
% 7.55/1.48  --share_sel_clauses                     true
% 7.55/1.48  --reset_solvers                         false
% 7.55/1.48  --bc_imp_inh                            [conj_cone]
% 7.55/1.48  --conj_cone_tolerance                   3.
% 7.55/1.48  --extra_neg_conj                        none
% 7.55/1.48  --large_theory_mode                     true
% 7.55/1.48  --prolific_symb_bound                   200
% 7.55/1.48  --lt_threshold                          2000
% 7.55/1.48  --clause_weak_htbl                      true
% 7.55/1.48  --gc_record_bc_elim                     false
% 7.55/1.48  
% 7.55/1.48  ------ Preprocessing Options
% 7.55/1.48  
% 7.55/1.48  --preprocessing_flag                    true
% 7.55/1.48  --time_out_prep_mult                    0.1
% 7.55/1.48  --splitting_mode                        input
% 7.55/1.48  --splitting_grd                         true
% 7.55/1.48  --splitting_cvd                         false
% 7.55/1.48  --splitting_cvd_svl                     false
% 7.55/1.48  --splitting_nvd                         32
% 7.55/1.48  --sub_typing                            true
% 7.55/1.48  --prep_gs_sim                           true
% 7.55/1.48  --prep_unflatten                        true
% 7.55/1.48  --prep_res_sim                          true
% 7.55/1.48  --prep_upred                            true
% 7.55/1.48  --prep_sem_filter                       exhaustive
% 7.55/1.48  --prep_sem_filter_out                   false
% 7.55/1.48  --pred_elim                             true
% 7.55/1.48  --res_sim_input                         true
% 7.55/1.48  --eq_ax_congr_red                       true
% 7.55/1.48  --pure_diseq_elim                       true
% 7.55/1.48  --brand_transform                       false
% 7.55/1.48  --non_eq_to_eq                          false
% 7.55/1.48  --prep_def_merge                        true
% 7.55/1.48  --prep_def_merge_prop_impl              false
% 7.55/1.48  --prep_def_merge_mbd                    true
% 7.55/1.48  --prep_def_merge_tr_red                 false
% 7.55/1.48  --prep_def_merge_tr_cl                  false
% 7.55/1.48  --smt_preprocessing                     true
% 7.55/1.48  --smt_ac_axioms                         fast
% 7.55/1.48  --preprocessed_out                      false
% 7.55/1.48  --preprocessed_stats                    false
% 7.55/1.48  
% 7.55/1.48  ------ Abstraction refinement Options
% 7.55/1.48  
% 7.55/1.48  --abstr_ref                             []
% 7.55/1.48  --abstr_ref_prep                        false
% 7.55/1.48  --abstr_ref_until_sat                   false
% 7.55/1.48  --abstr_ref_sig_restrict                funpre
% 7.55/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.55/1.48  --abstr_ref_under                       []
% 7.55/1.48  
% 7.55/1.48  ------ SAT Options
% 7.55/1.48  
% 7.55/1.48  --sat_mode                              false
% 7.55/1.48  --sat_fm_restart_options                ""
% 7.55/1.48  --sat_gr_def                            false
% 7.55/1.48  --sat_epr_types                         true
% 7.55/1.48  --sat_non_cyclic_types                  false
% 7.55/1.48  --sat_finite_models                     false
% 7.55/1.48  --sat_fm_lemmas                         false
% 7.55/1.48  --sat_fm_prep                           false
% 7.55/1.48  --sat_fm_uc_incr                        true
% 7.55/1.48  --sat_out_model                         small
% 7.55/1.48  --sat_out_clauses                       false
% 7.55/1.48  
% 7.55/1.48  ------ QBF Options
% 7.55/1.48  
% 7.55/1.48  --qbf_mode                              false
% 7.55/1.48  --qbf_elim_univ                         false
% 7.55/1.48  --qbf_dom_inst                          none
% 7.55/1.48  --qbf_dom_pre_inst                      false
% 7.55/1.48  --qbf_sk_in                             false
% 7.55/1.48  --qbf_pred_elim                         true
% 7.55/1.48  --qbf_split                             512
% 7.55/1.48  
% 7.55/1.48  ------ BMC1 Options
% 7.55/1.48  
% 7.55/1.48  --bmc1_incremental                      false
% 7.55/1.48  --bmc1_axioms                           reachable_all
% 7.55/1.48  --bmc1_min_bound                        0
% 7.55/1.48  --bmc1_max_bound                        -1
% 7.55/1.48  --bmc1_max_bound_default                -1
% 7.55/1.48  --bmc1_symbol_reachability              true
% 7.55/1.48  --bmc1_property_lemmas                  false
% 7.55/1.48  --bmc1_k_induction                      false
% 7.55/1.48  --bmc1_non_equiv_states                 false
% 7.55/1.48  --bmc1_deadlock                         false
% 7.55/1.48  --bmc1_ucm                              false
% 7.55/1.48  --bmc1_add_unsat_core                   none
% 7.55/1.48  --bmc1_unsat_core_children              false
% 7.55/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.55/1.48  --bmc1_out_stat                         full
% 7.55/1.48  --bmc1_ground_init                      false
% 7.55/1.48  --bmc1_pre_inst_next_state              false
% 7.55/1.48  --bmc1_pre_inst_state                   false
% 7.55/1.48  --bmc1_pre_inst_reach_state             false
% 7.55/1.48  --bmc1_out_unsat_core                   false
% 7.55/1.48  --bmc1_aig_witness_out                  false
% 7.55/1.48  --bmc1_verbose                          false
% 7.55/1.48  --bmc1_dump_clauses_tptp                false
% 7.55/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.55/1.48  --bmc1_dump_file                        -
% 7.55/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.55/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.55/1.48  --bmc1_ucm_extend_mode                  1
% 7.55/1.48  --bmc1_ucm_init_mode                    2
% 7.55/1.48  --bmc1_ucm_cone_mode                    none
% 7.55/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.55/1.48  --bmc1_ucm_relax_model                  4
% 7.55/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.55/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.55/1.48  --bmc1_ucm_layered_model                none
% 7.55/1.48  --bmc1_ucm_max_lemma_size               10
% 7.55/1.48  
% 7.55/1.48  ------ AIG Options
% 7.55/1.48  
% 7.55/1.48  --aig_mode                              false
% 7.55/1.48  
% 7.55/1.48  ------ Instantiation Options
% 7.55/1.48  
% 7.55/1.48  --instantiation_flag                    true
% 7.55/1.48  --inst_sos_flag                         false
% 7.55/1.48  --inst_sos_phase                        true
% 7.55/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.55/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.55/1.48  --inst_lit_sel_side                     num_symb
% 7.55/1.48  --inst_solver_per_active                1400
% 7.55/1.48  --inst_solver_calls_frac                1.
% 7.55/1.48  --inst_passive_queue_type               priority_queues
% 7.55/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.55/1.48  --inst_passive_queues_freq              [25;2]
% 7.55/1.48  --inst_dismatching                      true
% 7.55/1.48  --inst_eager_unprocessed_to_passive     true
% 7.55/1.48  --inst_prop_sim_given                   true
% 7.55/1.48  --inst_prop_sim_new                     false
% 7.55/1.48  --inst_subs_new                         false
% 7.55/1.48  --inst_eq_res_simp                      false
% 7.55/1.48  --inst_subs_given                       false
% 7.55/1.48  --inst_orphan_elimination               true
% 7.55/1.48  --inst_learning_loop_flag               true
% 7.55/1.48  --inst_learning_start                   3000
% 7.55/1.48  --inst_learning_factor                  2
% 7.55/1.48  --inst_start_prop_sim_after_learn       3
% 7.55/1.48  --inst_sel_renew                        solver
% 7.55/1.48  --inst_lit_activity_flag                true
% 7.55/1.48  --inst_restr_to_given                   false
% 7.55/1.48  --inst_activity_threshold               500
% 7.55/1.48  --inst_out_proof                        true
% 7.55/1.48  
% 7.55/1.48  ------ Resolution Options
% 7.55/1.48  
% 7.55/1.48  --resolution_flag                       true
% 7.55/1.48  --res_lit_sel                           adaptive
% 7.55/1.48  --res_lit_sel_side                      none
% 7.55/1.48  --res_ordering                          kbo
% 7.55/1.48  --res_to_prop_solver                    active
% 7.55/1.48  --res_prop_simpl_new                    false
% 7.55/1.48  --res_prop_simpl_given                  true
% 7.55/1.48  --res_passive_queue_type                priority_queues
% 7.55/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.55/1.48  --res_passive_queues_freq               [15;5]
% 7.55/1.48  --res_forward_subs                      full
% 7.55/1.48  --res_backward_subs                     full
% 7.55/1.48  --res_forward_subs_resolution           true
% 7.55/1.48  --res_backward_subs_resolution          true
% 7.55/1.48  --res_orphan_elimination                true
% 7.55/1.48  --res_time_limit                        2.
% 7.55/1.48  --res_out_proof                         true
% 7.55/1.48  
% 7.55/1.48  ------ Superposition Options
% 7.55/1.48  
% 7.55/1.48  --superposition_flag                    true
% 7.55/1.48  --sup_passive_queue_type                priority_queues
% 7.55/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.55/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.55/1.48  --demod_completeness_check              fast
% 7.55/1.48  --demod_use_ground                      true
% 7.55/1.48  --sup_to_prop_solver                    passive
% 7.55/1.48  --sup_prop_simpl_new                    true
% 7.55/1.48  --sup_prop_simpl_given                  true
% 7.55/1.48  --sup_fun_splitting                     false
% 7.55/1.48  --sup_smt_interval                      50000
% 7.55/1.48  
% 7.55/1.48  ------ Superposition Simplification Setup
% 7.55/1.48  
% 7.55/1.48  --sup_indices_passive                   []
% 7.55/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.55/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.48  --sup_full_bw                           [BwDemod]
% 7.55/1.48  --sup_immed_triv                        [TrivRules]
% 7.55/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.48  --sup_immed_bw_main                     []
% 7.55/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.55/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.48  
% 7.55/1.48  ------ Combination Options
% 7.55/1.48  
% 7.55/1.48  --comb_res_mult                         3
% 7.55/1.48  --comb_sup_mult                         2
% 7.55/1.48  --comb_inst_mult                        10
% 7.55/1.48  
% 7.55/1.48  ------ Debug Options
% 7.55/1.48  
% 7.55/1.48  --dbg_backtrace                         false
% 7.55/1.48  --dbg_dump_prop_clauses                 false
% 7.55/1.48  --dbg_dump_prop_clauses_file            -
% 7.55/1.48  --dbg_out_stat                          false
% 7.55/1.48  ------ Parsing...
% 7.55/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.55/1.48  
% 7.55/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.55/1.48  
% 7.55/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.55/1.48  
% 7.55/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.55/1.48  ------ Proving...
% 7.55/1.48  ------ Problem Properties 
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  clauses                                 18
% 7.55/1.48  conjectures                             4
% 7.55/1.48  EPR                                     4
% 7.55/1.48  Horn                                    15
% 7.55/1.48  unary                                   6
% 7.55/1.48  binary                                  10
% 7.55/1.48  lits                                    32
% 7.55/1.48  lits eq                                 3
% 7.55/1.48  fd_pure                                 0
% 7.55/1.48  fd_pseudo                               0
% 7.55/1.48  fd_cond                                 0
% 7.55/1.48  fd_pseudo_cond                          0
% 7.55/1.48  AC symbols                              0
% 7.55/1.48  
% 7.55/1.48  ------ Schedule dynamic 5 is on 
% 7.55/1.48  
% 7.55/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  ------ 
% 7.55/1.48  Current options:
% 7.55/1.48  ------ 
% 7.55/1.48  
% 7.55/1.48  ------ Input Options
% 7.55/1.48  
% 7.55/1.48  --out_options                           all
% 7.55/1.48  --tptp_safe_out                         true
% 7.55/1.48  --problem_path                          ""
% 7.55/1.48  --include_path                          ""
% 7.55/1.48  --clausifier                            res/vclausify_rel
% 7.55/1.48  --clausifier_options                    --mode clausify
% 7.55/1.48  --stdin                                 false
% 7.55/1.48  --stats_out                             all
% 7.55/1.48  
% 7.55/1.48  ------ General Options
% 7.55/1.48  
% 7.55/1.48  --fof                                   false
% 7.55/1.48  --time_out_real                         305.
% 7.55/1.48  --time_out_virtual                      -1.
% 7.55/1.48  --symbol_type_check                     false
% 7.55/1.48  --clausify_out                          false
% 7.55/1.48  --sig_cnt_out                           false
% 7.55/1.48  --trig_cnt_out                          false
% 7.55/1.48  --trig_cnt_out_tolerance                1.
% 7.55/1.48  --trig_cnt_out_sk_spl                   false
% 7.55/1.48  --abstr_cl_out                          false
% 7.55/1.48  
% 7.55/1.48  ------ Global Options
% 7.55/1.48  
% 7.55/1.48  --schedule                              default
% 7.55/1.48  --add_important_lit                     false
% 7.55/1.48  --prop_solver_per_cl                    1000
% 7.55/1.48  --min_unsat_core                        false
% 7.55/1.48  --soft_assumptions                      false
% 7.55/1.48  --soft_lemma_size                       3
% 7.55/1.48  --prop_impl_unit_size                   0
% 7.55/1.48  --prop_impl_unit                        []
% 7.55/1.48  --share_sel_clauses                     true
% 7.55/1.48  --reset_solvers                         false
% 7.55/1.48  --bc_imp_inh                            [conj_cone]
% 7.55/1.48  --conj_cone_tolerance                   3.
% 7.55/1.48  --extra_neg_conj                        none
% 7.55/1.48  --large_theory_mode                     true
% 7.55/1.48  --prolific_symb_bound                   200
% 7.55/1.48  --lt_threshold                          2000
% 7.55/1.48  --clause_weak_htbl                      true
% 7.55/1.48  --gc_record_bc_elim                     false
% 7.55/1.48  
% 7.55/1.48  ------ Preprocessing Options
% 7.55/1.48  
% 7.55/1.48  --preprocessing_flag                    true
% 7.55/1.48  --time_out_prep_mult                    0.1
% 7.55/1.48  --splitting_mode                        input
% 7.55/1.48  --splitting_grd                         true
% 7.55/1.48  --splitting_cvd                         false
% 7.55/1.48  --splitting_cvd_svl                     false
% 7.55/1.48  --splitting_nvd                         32
% 7.55/1.48  --sub_typing                            true
% 7.55/1.48  --prep_gs_sim                           true
% 7.55/1.48  --prep_unflatten                        true
% 7.55/1.48  --prep_res_sim                          true
% 7.55/1.48  --prep_upred                            true
% 7.55/1.48  --prep_sem_filter                       exhaustive
% 7.55/1.48  --prep_sem_filter_out                   false
% 7.55/1.48  --pred_elim                             true
% 7.55/1.48  --res_sim_input                         true
% 7.55/1.48  --eq_ax_congr_red                       true
% 7.55/1.48  --pure_diseq_elim                       true
% 7.55/1.48  --brand_transform                       false
% 7.55/1.48  --non_eq_to_eq                          false
% 7.55/1.48  --prep_def_merge                        true
% 7.55/1.48  --prep_def_merge_prop_impl              false
% 7.55/1.48  --prep_def_merge_mbd                    true
% 7.55/1.48  --prep_def_merge_tr_red                 false
% 7.55/1.48  --prep_def_merge_tr_cl                  false
% 7.55/1.48  --smt_preprocessing                     true
% 7.55/1.48  --smt_ac_axioms                         fast
% 7.55/1.48  --preprocessed_out                      false
% 7.55/1.48  --preprocessed_stats                    false
% 7.55/1.48  
% 7.55/1.48  ------ Abstraction refinement Options
% 7.55/1.48  
% 7.55/1.48  --abstr_ref                             []
% 7.55/1.48  --abstr_ref_prep                        false
% 7.55/1.48  --abstr_ref_until_sat                   false
% 7.55/1.48  --abstr_ref_sig_restrict                funpre
% 7.55/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.55/1.48  --abstr_ref_under                       []
% 7.55/1.48  
% 7.55/1.48  ------ SAT Options
% 7.55/1.48  
% 7.55/1.48  --sat_mode                              false
% 7.55/1.48  --sat_fm_restart_options                ""
% 7.55/1.48  --sat_gr_def                            false
% 7.55/1.48  --sat_epr_types                         true
% 7.55/1.48  --sat_non_cyclic_types                  false
% 7.55/1.48  --sat_finite_models                     false
% 7.55/1.48  --sat_fm_lemmas                         false
% 7.55/1.48  --sat_fm_prep                           false
% 7.55/1.48  --sat_fm_uc_incr                        true
% 7.55/1.48  --sat_out_model                         small
% 7.55/1.48  --sat_out_clauses                       false
% 7.55/1.48  
% 7.55/1.48  ------ QBF Options
% 7.55/1.48  
% 7.55/1.48  --qbf_mode                              false
% 7.55/1.48  --qbf_elim_univ                         false
% 7.55/1.48  --qbf_dom_inst                          none
% 7.55/1.48  --qbf_dom_pre_inst                      false
% 7.55/1.48  --qbf_sk_in                             false
% 7.55/1.48  --qbf_pred_elim                         true
% 7.55/1.48  --qbf_split                             512
% 7.55/1.48  
% 7.55/1.48  ------ BMC1 Options
% 7.55/1.48  
% 7.55/1.48  --bmc1_incremental                      false
% 7.55/1.48  --bmc1_axioms                           reachable_all
% 7.55/1.48  --bmc1_min_bound                        0
% 7.55/1.48  --bmc1_max_bound                        -1
% 7.55/1.48  --bmc1_max_bound_default                -1
% 7.55/1.48  --bmc1_symbol_reachability              true
% 7.55/1.48  --bmc1_property_lemmas                  false
% 7.55/1.48  --bmc1_k_induction                      false
% 7.55/1.48  --bmc1_non_equiv_states                 false
% 7.55/1.48  --bmc1_deadlock                         false
% 7.55/1.48  --bmc1_ucm                              false
% 7.55/1.48  --bmc1_add_unsat_core                   none
% 7.55/1.48  --bmc1_unsat_core_children              false
% 7.55/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.55/1.48  --bmc1_out_stat                         full
% 7.55/1.48  --bmc1_ground_init                      false
% 7.55/1.48  --bmc1_pre_inst_next_state              false
% 7.55/1.48  --bmc1_pre_inst_state                   false
% 7.55/1.48  --bmc1_pre_inst_reach_state             false
% 7.55/1.48  --bmc1_out_unsat_core                   false
% 7.55/1.48  --bmc1_aig_witness_out                  false
% 7.55/1.48  --bmc1_verbose                          false
% 7.55/1.48  --bmc1_dump_clauses_tptp                false
% 7.55/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.55/1.48  --bmc1_dump_file                        -
% 7.55/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.55/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.55/1.48  --bmc1_ucm_extend_mode                  1
% 7.55/1.48  --bmc1_ucm_init_mode                    2
% 7.55/1.48  --bmc1_ucm_cone_mode                    none
% 7.55/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.55/1.48  --bmc1_ucm_relax_model                  4
% 7.55/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.55/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.55/1.48  --bmc1_ucm_layered_model                none
% 7.55/1.48  --bmc1_ucm_max_lemma_size               10
% 7.55/1.48  
% 7.55/1.48  ------ AIG Options
% 7.55/1.48  
% 7.55/1.48  --aig_mode                              false
% 7.55/1.48  
% 7.55/1.48  ------ Instantiation Options
% 7.55/1.48  
% 7.55/1.48  --instantiation_flag                    true
% 7.55/1.48  --inst_sos_flag                         false
% 7.55/1.48  --inst_sos_phase                        true
% 7.55/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.55/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.55/1.48  --inst_lit_sel_side                     none
% 7.55/1.48  --inst_solver_per_active                1400
% 7.55/1.48  --inst_solver_calls_frac                1.
% 7.55/1.48  --inst_passive_queue_type               priority_queues
% 7.55/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.55/1.48  --inst_passive_queues_freq              [25;2]
% 7.55/1.48  --inst_dismatching                      true
% 7.55/1.48  --inst_eager_unprocessed_to_passive     true
% 7.55/1.48  --inst_prop_sim_given                   true
% 7.55/1.48  --inst_prop_sim_new                     false
% 7.55/1.48  --inst_subs_new                         false
% 7.55/1.48  --inst_eq_res_simp                      false
% 7.55/1.48  --inst_subs_given                       false
% 7.55/1.48  --inst_orphan_elimination               true
% 7.55/1.48  --inst_learning_loop_flag               true
% 7.55/1.48  --inst_learning_start                   3000
% 7.55/1.48  --inst_learning_factor                  2
% 7.55/1.48  --inst_start_prop_sim_after_learn       3
% 7.55/1.48  --inst_sel_renew                        solver
% 7.55/1.48  --inst_lit_activity_flag                true
% 7.55/1.48  --inst_restr_to_given                   false
% 7.55/1.48  --inst_activity_threshold               500
% 7.55/1.48  --inst_out_proof                        true
% 7.55/1.48  
% 7.55/1.48  ------ Resolution Options
% 7.55/1.48  
% 7.55/1.48  --resolution_flag                       false
% 7.55/1.48  --res_lit_sel                           adaptive
% 7.55/1.48  --res_lit_sel_side                      none
% 7.55/1.48  --res_ordering                          kbo
% 7.55/1.48  --res_to_prop_solver                    active
% 7.55/1.48  --res_prop_simpl_new                    false
% 7.55/1.48  --res_prop_simpl_given                  true
% 7.55/1.48  --res_passive_queue_type                priority_queues
% 7.55/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.55/1.48  --res_passive_queues_freq               [15;5]
% 7.55/1.48  --res_forward_subs                      full
% 7.55/1.48  --res_backward_subs                     full
% 7.55/1.48  --res_forward_subs_resolution           true
% 7.55/1.48  --res_backward_subs_resolution          true
% 7.55/1.48  --res_orphan_elimination                true
% 7.55/1.48  --res_time_limit                        2.
% 7.55/1.48  --res_out_proof                         true
% 7.55/1.48  
% 7.55/1.48  ------ Superposition Options
% 7.55/1.48  
% 7.55/1.48  --superposition_flag                    true
% 7.55/1.48  --sup_passive_queue_type                priority_queues
% 7.55/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.55/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.55/1.48  --demod_completeness_check              fast
% 7.55/1.48  --demod_use_ground                      true
% 7.55/1.48  --sup_to_prop_solver                    passive
% 7.55/1.48  --sup_prop_simpl_new                    true
% 7.55/1.48  --sup_prop_simpl_given                  true
% 7.55/1.48  --sup_fun_splitting                     false
% 7.55/1.48  --sup_smt_interval                      50000
% 7.55/1.48  
% 7.55/1.48  ------ Superposition Simplification Setup
% 7.55/1.48  
% 7.55/1.48  --sup_indices_passive                   []
% 7.55/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.55/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.48  --sup_full_bw                           [BwDemod]
% 7.55/1.48  --sup_immed_triv                        [TrivRules]
% 7.55/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.48  --sup_immed_bw_main                     []
% 7.55/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.55/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.48  
% 7.55/1.48  ------ Combination Options
% 7.55/1.48  
% 7.55/1.48  --comb_res_mult                         3
% 7.55/1.48  --comb_sup_mult                         2
% 7.55/1.48  --comb_inst_mult                        10
% 7.55/1.48  
% 7.55/1.48  ------ Debug Options
% 7.55/1.48  
% 7.55/1.48  --dbg_backtrace                         false
% 7.55/1.48  --dbg_dump_prop_clauses                 false
% 7.55/1.48  --dbg_dump_prop_clauses_file            -
% 7.55/1.48  --dbg_out_stat                          false
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  ------ Proving...
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  % SZS status Theorem for theBenchmark.p
% 7.55/1.48  
% 7.55/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.55/1.48  
% 7.55/1.48  fof(f12,conjecture,(
% 7.55/1.48    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f13,negated_conjecture,(
% 7.55/1.48    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.55/1.48    inference(negated_conjecture,[],[f12])).
% 7.55/1.48  
% 7.55/1.48  fof(f20,plain,(
% 7.55/1.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 7.55/1.48    inference(ennf_transformation,[],[f13])).
% 7.55/1.48  
% 7.55/1.48  fof(f21,plain,(
% 7.55/1.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 7.55/1.48    inference(flattening,[],[f20])).
% 7.55/1.48  
% 7.55/1.48  fof(f25,plain,(
% 7.55/1.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)))),
% 7.55/1.48    introduced(choice_axiom,[])).
% 7.55/1.48  
% 7.55/1.48  fof(f26,plain,(
% 7.55/1.48    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 7.55/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f25])).
% 7.55/1.48  
% 7.55/1.48  fof(f44,plain,(
% 7.55/1.48    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 7.55/1.48    inference(cnf_transformation,[],[f26])).
% 7.55/1.48  
% 7.55/1.48  fof(f6,axiom,(
% 7.55/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f35,plain,(
% 7.55/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.55/1.48    inference(cnf_transformation,[],[f6])).
% 7.55/1.48  
% 7.55/1.48  fof(f9,axiom,(
% 7.55/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f41,plain,(
% 7.55/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f9])).
% 7.55/1.48  
% 7.55/1.48  fof(f10,axiom,(
% 7.55/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f42,plain,(
% 7.55/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f10])).
% 7.55/1.48  
% 7.55/1.48  fof(f48,plain,(
% 7.55/1.48    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 7.55/1.48    inference(definition_unfolding,[],[f41,f42])).
% 7.55/1.48  
% 7.55/1.48  fof(f51,plain,(
% 7.55/1.48    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_enumset1(sK4,sK4,sK4))),
% 7.55/1.48    inference(definition_unfolding,[],[f44,f35,f48])).
% 7.55/1.48  
% 7.55/1.48  fof(f46,plain,(
% 7.55/1.48    r1_xboole_0(sK3,sK2)),
% 7.55/1.48    inference(cnf_transformation,[],[f26])).
% 7.55/1.48  
% 7.55/1.48  fof(f2,axiom,(
% 7.55/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f15,plain,(
% 7.55/1.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.55/1.48    inference(ennf_transformation,[],[f2])).
% 7.55/1.48  
% 7.55/1.48  fof(f28,plain,(
% 7.55/1.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f15])).
% 7.55/1.48  
% 7.55/1.48  fof(f11,axiom,(
% 7.55/1.48    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f19,plain,(
% 7.55/1.48    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 7.55/1.48    inference(ennf_transformation,[],[f11])).
% 7.55/1.48  
% 7.55/1.48  fof(f43,plain,(
% 7.55/1.48    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f19])).
% 7.55/1.48  
% 7.55/1.48  fof(f50,plain,(
% 7.55/1.48    ( ! [X0,X1] : (r1_xboole_0(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 7.55/1.48    inference(definition_unfolding,[],[f43,f48])).
% 7.55/1.48  
% 7.55/1.48  fof(f8,axiom,(
% 7.55/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f24,plain,(
% 7.55/1.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.55/1.48    inference(nnf_transformation,[],[f8])).
% 7.55/1.48  
% 7.55/1.48  fof(f39,plain,(
% 7.55/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f24])).
% 7.55/1.48  
% 7.55/1.48  fof(f45,plain,(
% 7.55/1.48    r2_hidden(sK4,sK3)),
% 7.55/1.48    inference(cnf_transformation,[],[f26])).
% 7.55/1.48  
% 7.55/1.48  fof(f3,axiom,(
% 7.55/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f14,plain,(
% 7.55/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.55/1.48    inference(rectify,[],[f3])).
% 7.55/1.48  
% 7.55/1.48  fof(f16,plain,(
% 7.55/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.55/1.48    inference(ennf_transformation,[],[f14])).
% 7.55/1.48  
% 7.55/1.48  fof(f22,plain,(
% 7.55/1.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.55/1.48    introduced(choice_axiom,[])).
% 7.55/1.48  
% 7.55/1.48  fof(f23,plain,(
% 7.55/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.55/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f22])).
% 7.55/1.48  
% 7.55/1.48  fof(f31,plain,(
% 7.55/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f23])).
% 7.55/1.48  
% 7.55/1.48  fof(f4,axiom,(
% 7.55/1.48    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f17,plain,(
% 7.55/1.48    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 7.55/1.48    inference(ennf_transformation,[],[f4])).
% 7.55/1.48  
% 7.55/1.48  fof(f33,plain,(
% 7.55/1.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 7.55/1.48    inference(cnf_transformation,[],[f17])).
% 7.55/1.48  
% 7.55/1.48  fof(f1,axiom,(
% 7.55/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f27,plain,(
% 7.55/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f1])).
% 7.55/1.48  
% 7.55/1.48  fof(f49,plain,(
% 7.55/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.55/1.48    inference(definition_unfolding,[],[f27,f35,f35])).
% 7.55/1.48  
% 7.55/1.48  fof(f5,axiom,(
% 7.55/1.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f34,plain,(
% 7.55/1.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.55/1.48    inference(cnf_transformation,[],[f5])).
% 7.55/1.48  
% 7.55/1.48  fof(f7,axiom,(
% 7.55/1.48    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.55/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.55/1.48  
% 7.55/1.48  fof(f18,plain,(
% 7.55/1.48    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.55/1.48    inference(ennf_transformation,[],[f7])).
% 7.55/1.48  
% 7.55/1.48  fof(f36,plain,(
% 7.55/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.55/1.48    inference(cnf_transformation,[],[f18])).
% 7.55/1.48  
% 7.55/1.48  fof(f47,plain,(
% 7.55/1.48    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 7.55/1.48    inference(cnf_transformation,[],[f26])).
% 7.55/1.48  
% 7.55/1.48  cnf(c_17,negated_conjecture,
% 7.55/1.48      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_enumset1(sK4,sK4,sK4)) ),
% 7.55/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_632,plain,
% 7.55/1.48      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k1_enumset1(sK4,sK4,sK4)) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_15,negated_conjecture,
% 7.55/1.48      ( r1_xboole_0(sK3,sK2) ),
% 7.55/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_634,plain,
% 7.55/1.48      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1,plain,
% 7.55/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.55/1.48      inference(cnf_transformation,[],[f28]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_648,plain,
% 7.55/1.48      ( r1_xboole_0(X0,X1) != iProver_top
% 7.55/1.48      | r1_xboole_0(X1,X0) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1344,plain,
% 7.55/1.48      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_634,c_648]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_13,plain,
% 7.55/1.48      ( r2_hidden(X0,X1) | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
% 7.55/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_636,plain,
% 7.55/1.48      ( r2_hidden(X0,X1) = iProver_top
% 7.55/1.48      | r1_xboole_0(k1_enumset1(X0,X0,X0),X1) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_12,plain,
% 7.55/1.48      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 7.55/1.48      inference(cnf_transformation,[],[f39]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_637,plain,
% 7.55/1.48      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1315,plain,
% 7.55/1.48      ( k4_xboole_0(k1_enumset1(X0,X0,X0),X1) = k1_enumset1(X0,X0,X0)
% 7.55/1.48      | r2_hidden(X0,X1) = iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_636,c_637]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_16,negated_conjecture,
% 7.55/1.48      ( r2_hidden(sK4,sK3) ),
% 7.55/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_633,plain,
% 7.55/1.48      ( r2_hidden(sK4,sK3) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_2,plain,
% 7.55/1.48      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.55/1.48      inference(cnf_transformation,[],[f31]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_647,plain,
% 7.55/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.55/1.48      | r2_hidden(X0,X2) != iProver_top
% 7.55/1.48      | r1_xboole_0(X2,X1) != iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_3293,plain,
% 7.55/1.48      ( r2_hidden(sK4,X0) != iProver_top
% 7.55/1.48      | r1_xboole_0(X0,sK3) != iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_633,c_647]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_4442,plain,
% 7.55/1.48      ( k4_xboole_0(k1_enumset1(sK4,sK4,sK4),X0) = k1_enumset1(sK4,sK4,sK4)
% 7.55/1.48      | r1_xboole_0(X0,sK3) != iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_1315,c_3293]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_5203,plain,
% 7.55/1.48      ( k4_xboole_0(k1_enumset1(sK4,sK4,sK4),sK2) = k1_enumset1(sK4,sK4,sK4) ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_1344,c_4442]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_5,plain,
% 7.55/1.48      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2) ),
% 7.55/1.48      inference(cnf_transformation,[],[f33]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_644,plain,
% 7.55/1.48      ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
% 7.55/1.48      | r1_xboole_0(X0,X2) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_5237,plain,
% 7.55/1.48      ( r1_tarski(X0,k1_enumset1(sK4,sK4,sK4)) != iProver_top
% 7.55/1.48      | r1_xboole_0(X0,sK2) = iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_5203,c_644]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_5551,plain,
% 7.55/1.48      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) = iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_632,c_5237]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_5733,plain,
% 7.55/1.48      ( r1_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_5551,c_648]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_5743,plain,
% 7.55/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sK2 ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_5733,c_637]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_0,plain,
% 7.55/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.55/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_7,plain,
% 7.55/1.48      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.55/1.48      inference(cnf_transformation,[],[f34]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_642,plain,
% 7.55/1.48      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_868,plain,
% 7.55/1.48      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_0,c_642]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1045,plain,
% 7.55/1.48      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_0,c_868]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_2440,plain,
% 7.55/1.48      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X1) = iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_1045,c_644]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_30723,plain,
% 7.55/1.48      ( r1_xboole_0(sK2,sK1) = iProver_top ),
% 7.55/1.48      inference(superposition,[status(thm)],[c_5743,c_2440]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1096,plain,
% 7.55/1.48      ( r1_xboole_0(sK2,sK3) | ~ r1_xboole_0(sK3,sK2) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_1097,plain,
% 7.55/1.48      ( r1_xboole_0(sK2,sK3) = iProver_top
% 7.55/1.48      | r1_xboole_0(sK3,sK2) != iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_1096]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_10,plain,
% 7.55/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.55/1.48      | ~ r1_xboole_0(X0,X2)
% 7.55/1.48      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.55/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_847,plain,
% 7.55/1.48      ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
% 7.55/1.48      | ~ r1_xboole_0(sK2,sK3)
% 7.55/1.48      | ~ r1_xboole_0(sK2,sK1) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_10]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_848,plain,
% 7.55/1.48      ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) = iProver_top
% 7.55/1.48      | r1_xboole_0(sK2,sK3) != iProver_top
% 7.55/1.48      | r1_xboole_0(sK2,sK1) != iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_847]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_750,plain,
% 7.55/1.48      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
% 7.55/1.48      | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
% 7.55/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_751,plain,
% 7.55/1.48      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) = iProver_top
% 7.55/1.48      | r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) != iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_14,negated_conjecture,
% 7.55/1.48      ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
% 7.55/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_21,plain,
% 7.55/1.48      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) != iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(c_20,plain,
% 7.55/1.48      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 7.55/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.55/1.48  
% 7.55/1.48  cnf(contradiction,plain,
% 7.55/1.48      ( $false ),
% 7.55/1.48      inference(minisat,
% 7.55/1.48                [status(thm)],
% 7.55/1.48                [c_30723,c_1097,c_848,c_751,c_21,c_20]) ).
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.55/1.48  
% 7.55/1.48  ------                               Statistics
% 7.55/1.48  
% 7.55/1.48  ------ General
% 7.55/1.48  
% 7.55/1.48  abstr_ref_over_cycles:                  0
% 7.55/1.48  abstr_ref_under_cycles:                 0
% 7.55/1.48  gc_basic_clause_elim:                   0
% 7.55/1.48  forced_gc_time:                         0
% 7.55/1.48  parsing_time:                           0.008
% 7.55/1.48  unif_index_cands_time:                  0.
% 7.55/1.48  unif_index_add_time:                    0.
% 7.55/1.48  orderings_time:                         0.
% 7.55/1.48  out_proof_time:                         0.009
% 7.55/1.48  total_time:                             0.807
% 7.55/1.48  num_of_symbols:                         42
% 7.55/1.48  num_of_terms:                           34411
% 7.55/1.48  
% 7.55/1.48  ------ Preprocessing
% 7.55/1.48  
% 7.55/1.48  num_of_splits:                          0
% 7.55/1.48  num_of_split_atoms:                     0
% 7.55/1.48  num_of_reused_defs:                     0
% 7.55/1.48  num_eq_ax_congr_red:                    4
% 7.55/1.48  num_of_sem_filtered_clauses:            1
% 7.55/1.48  num_of_subtypes:                        0
% 7.55/1.48  monotx_restored_types:                  0
% 7.55/1.48  sat_num_of_epr_types:                   0
% 7.55/1.48  sat_num_of_non_cyclic_types:            0
% 7.55/1.48  sat_guarded_non_collapsed_types:        0
% 7.55/1.48  num_pure_diseq_elim:                    0
% 7.55/1.48  simp_replaced_by:                       0
% 7.55/1.48  res_preprocessed:                       71
% 7.55/1.48  prep_upred:                             0
% 7.55/1.48  prep_unflattend:                        0
% 7.55/1.48  smt_new_axioms:                         0
% 7.55/1.48  pred_elim_cands:                        3
% 7.55/1.48  pred_elim:                              0
% 7.55/1.48  pred_elim_cl:                           0
% 7.55/1.48  pred_elim_cycles:                       1
% 7.55/1.48  merged_defs:                            6
% 7.55/1.48  merged_defs_ncl:                        0
% 7.55/1.48  bin_hyper_res:                          6
% 7.55/1.48  prep_cycles:                            3
% 7.55/1.48  pred_elim_time:                         0.
% 7.55/1.48  splitting_time:                         0.
% 7.55/1.48  sem_filter_time:                        0.
% 7.55/1.48  monotx_time:                            0.
% 7.55/1.48  subtype_inf_time:                       0.
% 7.55/1.48  
% 7.55/1.48  ------ Problem properties
% 7.55/1.48  
% 7.55/1.48  clauses:                                18
% 7.55/1.48  conjectures:                            4
% 7.55/1.48  epr:                                    4
% 7.55/1.48  horn:                                   15
% 7.55/1.48  ground:                                 4
% 7.55/1.48  unary:                                  6
% 7.55/1.48  binary:                                 10
% 7.55/1.48  lits:                                   32
% 7.55/1.48  lits_eq:                                3
% 7.55/1.48  fd_pure:                                0
% 7.55/1.48  fd_pseudo:                              0
% 7.55/1.48  fd_cond:                                0
% 7.55/1.48  fd_pseudo_cond:                         0
% 7.55/1.48  ac_symbols:                             0
% 7.55/1.48  
% 7.55/1.48  ------ Propositional Solver
% 7.55/1.48  
% 7.55/1.48  prop_solver_calls:                      28
% 7.55/1.48  prop_fast_solver_calls:                 573
% 7.55/1.48  smt_solver_calls:                       0
% 7.55/1.48  smt_fast_solver_calls:                  0
% 7.55/1.48  prop_num_of_clauses:                    13807
% 7.55/1.48  prop_preprocess_simplified:             19066
% 7.55/1.48  prop_fo_subsumed:                       2
% 7.55/1.48  prop_solver_time:                       0.
% 7.55/1.48  smt_solver_time:                        0.
% 7.55/1.48  smt_fast_solver_time:                   0.
% 7.55/1.48  prop_fast_solver_time:                  0.
% 7.55/1.48  prop_unsat_core_time:                   0.001
% 7.55/1.48  
% 7.55/1.48  ------ QBF
% 7.55/1.48  
% 7.55/1.48  qbf_q_res:                              0
% 7.55/1.48  qbf_num_tautologies:                    0
% 7.55/1.48  qbf_prep_cycles:                        0
% 7.55/1.48  
% 7.55/1.48  ------ BMC1
% 7.55/1.48  
% 7.55/1.48  bmc1_current_bound:                     -1
% 7.55/1.48  bmc1_last_solved_bound:                 -1
% 7.55/1.48  bmc1_unsat_core_size:                   -1
% 7.55/1.48  bmc1_unsat_core_parents_size:           -1
% 7.55/1.48  bmc1_merge_next_fun:                    0
% 7.55/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.55/1.48  
% 7.55/1.48  ------ Instantiation
% 7.55/1.48  
% 7.55/1.48  inst_num_of_clauses:                    3646
% 7.55/1.48  inst_num_in_passive:                    1277
% 7.55/1.48  inst_num_in_active:                     884
% 7.55/1.48  inst_num_in_unprocessed:                1485
% 7.55/1.48  inst_num_of_loops:                      990
% 7.55/1.48  inst_num_of_learning_restarts:          0
% 7.55/1.48  inst_num_moves_active_passive:          102
% 7.55/1.48  inst_lit_activity:                      0
% 7.55/1.48  inst_lit_activity_moves:                1
% 7.55/1.48  inst_num_tautologies:                   0
% 7.55/1.48  inst_num_prop_implied:                  0
% 7.55/1.48  inst_num_existing_simplified:           0
% 7.55/1.48  inst_num_eq_res_simplified:             0
% 7.55/1.48  inst_num_child_elim:                    0
% 7.55/1.48  inst_num_of_dismatching_blockings:      1654
% 7.55/1.48  inst_num_of_non_proper_insts:           2817
% 7.55/1.48  inst_num_of_duplicates:                 0
% 7.55/1.48  inst_inst_num_from_inst_to_res:         0
% 7.55/1.48  inst_dismatching_checking_time:         0.
% 7.55/1.48  
% 7.55/1.48  ------ Resolution
% 7.55/1.48  
% 7.55/1.48  res_num_of_clauses:                     0
% 7.55/1.48  res_num_in_passive:                     0
% 7.55/1.48  res_num_in_active:                      0
% 7.55/1.48  res_num_of_loops:                       74
% 7.55/1.48  res_forward_subset_subsumed:            224
% 7.55/1.48  res_backward_subset_subsumed:           2
% 7.55/1.48  res_forward_subsumed:                   0
% 7.55/1.48  res_backward_subsumed:                  0
% 7.55/1.48  res_forward_subsumption_resolution:     0
% 7.55/1.48  res_backward_subsumption_resolution:    0
% 7.55/1.48  res_clause_to_clause_subsumption:       18420
% 7.55/1.48  res_orphan_elimination:                 0
% 7.55/1.48  res_tautology_del:                      197
% 7.55/1.48  res_num_eq_res_simplified:              0
% 7.55/1.48  res_num_sel_changes:                    0
% 7.55/1.48  res_moves_from_active_to_pass:          0
% 7.55/1.48  
% 7.55/1.48  ------ Superposition
% 7.55/1.48  
% 7.55/1.48  sup_time_total:                         0.
% 7.55/1.48  sup_time_generating:                    0.
% 7.55/1.48  sup_time_sim_full:                      0.
% 7.55/1.48  sup_time_sim_immed:                     0.
% 7.55/1.48  
% 7.55/1.48  sup_num_of_clauses:                     1164
% 7.55/1.48  sup_num_in_active:                      198
% 7.55/1.48  sup_num_in_passive:                     966
% 7.55/1.48  sup_num_of_loops:                       197
% 7.55/1.48  sup_fw_superposition:                   2255
% 7.55/1.48  sup_bw_superposition:                   1210
% 7.55/1.48  sup_immediate_simplified:               1155
% 7.55/1.48  sup_given_eliminated:                   0
% 7.55/1.48  comparisons_done:                       0
% 7.55/1.48  comparisons_avoided:                    0
% 7.55/1.48  
% 7.55/1.48  ------ Simplifications
% 7.55/1.48  
% 7.55/1.48  
% 7.55/1.48  sim_fw_subset_subsumed:                 2
% 7.55/1.48  sim_bw_subset_subsumed:                 3
% 7.55/1.48  sim_fw_subsumed:                        776
% 7.55/1.48  sim_bw_subsumed:                        17
% 7.55/1.48  sim_fw_subsumption_res:                 0
% 7.55/1.48  sim_bw_subsumption_res:                 0
% 7.55/1.48  sim_tautology_del:                      15
% 7.55/1.48  sim_eq_tautology_del:                   0
% 7.55/1.48  sim_eq_res_simp:                        0
% 7.55/1.48  sim_fw_demodulated:                     0
% 7.55/1.48  sim_bw_demodulated:                     19
% 7.55/1.48  sim_light_normalised:                   809
% 7.55/1.48  sim_joinable_taut:                      0
% 7.55/1.48  sim_joinable_simp:                      0
% 7.55/1.48  sim_ac_normalised:                      0
% 7.55/1.48  sim_smt_subsumption:                    0
% 7.55/1.48  
%------------------------------------------------------------------------------
