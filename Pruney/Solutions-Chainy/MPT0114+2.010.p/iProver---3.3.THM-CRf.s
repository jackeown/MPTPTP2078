%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:59 EST 2020

% Result     : Theorem 15.67s
% Output     : CNFRefutation 15.67s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 171 expanded)
%              Number of clauses        :   66 (  79 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :   18
%              Number of atoms          :  249 ( 423 expanded)
%              Number of equality atoms :   97 ( 133 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k5_xboole_0(X1,X2))
      <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <~> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
        & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
            & r1_tarski(X0,k2_xboole_0(X1,X2)) )
          | r1_tarski(X0,k5_xboole_0(X1,X2)) ) )
   => ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
      & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
          & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
        | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
    & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
      | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).

fof(f46,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f46,f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f45,f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f47,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f47,f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f48,f32])).

cnf(c_220,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_19958,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_28616,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_19958])).

cnf(c_60693,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | sK0 != k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_28616])).

cnf(c_7,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1120,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,X0),X0) = k4_xboole_0(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_33849,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_1489,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k4_xboole_0(sK0,X2),k4_xboole_0(k2_xboole_0(sK1,sK2),X2))
    | X1 != k4_xboole_0(k2_xboole_0(sK1,sK2),X2)
    | X0 != k4_xboole_0(sK0,X2) ),
    inference(instantiation,[status(thm)],[c_220])).

cnf(c_6864,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,X0),X0),X1)
    | ~ r1_tarski(k4_xboole_0(sK0,X0),k4_xboole_0(k2_xboole_0(sK1,sK2),X0))
    | X1 != k4_xboole_0(k2_xboole_0(sK1,sK2),X0)
    | k4_xboole_0(k2_xboole_0(sK0,X0),X0) != k4_xboole_0(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_24897,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | ~ r1_tarski(k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6864])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_927,plain,
    ( r1_tarski(k4_xboole_0(sK0,X0),k4_xboole_0(k2_xboole_0(sK1,sK2),X0))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_17969,plain,
    ( r1_tarski(k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_927])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_594,plain,
    ( r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) = iProver_top
    | r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_605,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_884,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) = sK0
    | r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_605])).

cnf(c_1384,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) = sK0
    | k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
    inference(superposition,[status(thm)],[c_884,c_605])).

cnf(c_14,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_604,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1270,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k3_xboole_0(X1,X2))),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_604])).

cnf(c_10331,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
    | r1_tarski(k2_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_1270])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10453,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
    | r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10331,c_3])).

cnf(c_928,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_932,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
    | r1_tarski(sK0,k2_xboole_0(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_928])).

cnf(c_10692,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10453,c_932])).

cnf(c_1269,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_604])).

cnf(c_10705,plain,
    ( r1_tarski(k2_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),X0))),k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10692,c_1269])).

cnf(c_10742,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10705,c_3])).

cnf(c_10762,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10742])).

cnf(c_215,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1659,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_3514,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1659])).

cnf(c_7958,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) != sK0
    | sK0 = k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_3514])).

cnf(c_2236,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_tarski(X3,k4_xboole_0(k2_xboole_0(X1,X2),X2))
    | X3 != X0 ),
    inference(resolution,[status(thm)],[c_220,c_7])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7636,plain,
    ( r1_tarski(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)))
    | r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | X0 != sK0 ),
    inference(resolution,[status(thm)],[c_2236,c_16])).

cnf(c_595,plain,
    ( r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) = iProver_top
    | r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_606,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_989,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) = k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_595,c_606])).

cnf(c_999,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) = k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_989])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1447,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_214,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1216,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_1782,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1216])).

cnf(c_216,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_799,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(k2_xboole_0(X2,X3),k3_xboole_0(X2,X3)))
    | X1 != k4_xboole_0(k2_xboole_0(X2,X3),k3_xboole_0(X2,X3))
    | X0 != k3_xboole_0(X2,X3) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_1215,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)))
    | X2 != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | k3_xboole_0(X0,X1) != k3_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_2459,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | r1_xboole_0(k3_xboole_0(sK1,sK2),k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))))
    | k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) != k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | k3_xboole_0(sK1,sK2) != k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1215])).

cnf(c_1,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2773,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5768,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK1,sK2),k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))))
    | r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_7924,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7636,c_999,c_1447,c_1782,c_2459,c_2773,c_5768])).

cnf(c_2480,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_4598,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) = k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2480])).

cnf(c_1025,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_911,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) = sK0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_60693,c_33849,c_24897,c_17969,c_10762,c_7958,c_7924,c_4598,c_1025,c_911,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:51:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.67/2.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.67/2.48  
% 15.67/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.67/2.48  
% 15.67/2.48  ------  iProver source info
% 15.67/2.48  
% 15.67/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.67/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.67/2.48  git: non_committed_changes: false
% 15.67/2.48  git: last_make_outside_of_git: false
% 15.67/2.48  
% 15.67/2.48  ------ 
% 15.67/2.48  ------ Parsing...
% 15.67/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.67/2.48  
% 15.67/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.67/2.48  
% 15.67/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.67/2.48  
% 15.67/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.67/2.48  ------ Proving...
% 15.67/2.48  ------ Problem Properties 
% 15.67/2.48  
% 15.67/2.48  
% 15.67/2.48  clauses                                 18
% 15.67/2.48  conjectures                             3
% 15.67/2.48  EPR                                     1
% 15.67/2.48  Horn                                    16
% 15.67/2.48  unary                                   5
% 15.67/2.48  binary                                  11
% 15.67/2.48  lits                                    33
% 15.67/2.48  lits eq                                 6
% 15.67/2.48  fd_pure                                 0
% 15.67/2.48  fd_pseudo                               0
% 15.67/2.48  fd_cond                                 0
% 15.67/2.48  fd_pseudo_cond                          0
% 15.67/2.48  AC symbols                              0
% 15.67/2.48  
% 15.67/2.48  ------ Input Options Time Limit: Unbounded
% 15.67/2.48  
% 15.67/2.48  
% 15.67/2.48  ------ 
% 15.67/2.48  Current options:
% 15.67/2.48  ------ 
% 15.67/2.48  
% 15.67/2.48  
% 15.67/2.48  
% 15.67/2.48  
% 15.67/2.48  ------ Proving...
% 15.67/2.48  
% 15.67/2.48  
% 15.67/2.48  % SZS status Theorem for theBenchmark.p
% 15.67/2.48  
% 15.67/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.67/2.48  
% 15.67/2.48  fof(f9,axiom,(
% 15.67/2.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f38,plain,(
% 15.67/2.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 15.67/2.48    inference(cnf_transformation,[],[f9])).
% 15.67/2.48  
% 15.67/2.48  fof(f8,axiom,(
% 15.67/2.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f20,plain,(
% 15.67/2.48    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 15.67/2.48    inference(ennf_transformation,[],[f8])).
% 15.67/2.48  
% 15.67/2.48  fof(f37,plain,(
% 15.67/2.48    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 15.67/2.48    inference(cnf_transformation,[],[f20])).
% 15.67/2.48  
% 15.67/2.48  fof(f15,conjecture,(
% 15.67/2.48    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f16,negated_conjecture,(
% 15.67/2.48    ~! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 15.67/2.48    inference(negated_conjecture,[],[f15])).
% 15.67/2.48  
% 15.67/2.48  fof(f25,plain,(
% 15.67/2.48    ? [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <~> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 15.67/2.48    inference(ennf_transformation,[],[f16])).
% 15.67/2.48  
% 15.67/2.48  fof(f26,plain,(
% 15.67/2.48    ? [X0,X1,X2] : (((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 15.67/2.48    inference(nnf_transformation,[],[f25])).
% 15.67/2.48  
% 15.67/2.48  fof(f27,plain,(
% 15.67/2.48    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 15.67/2.48    inference(flattening,[],[f26])).
% 15.67/2.48  
% 15.67/2.48  fof(f28,plain,(
% 15.67/2.48    ? [X0,X1,X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | r1_tarski(X0,k5_xboole_0(X1,X2)))) => ((~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))))),
% 15.67/2.48    introduced(choice_axiom,[])).
% 15.67/2.48  
% 15.67/2.48  fof(f29,plain,(
% 15.67/2.48    (~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))) & ((r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))) | r1_tarski(sK0,k5_xboole_0(sK1,sK2)))),
% 15.67/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).
% 15.67/2.48  
% 15.67/2.48  fof(f46,plain,(
% 15.67/2.48    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 15.67/2.48    inference(cnf_transformation,[],[f29])).
% 15.67/2.48  
% 15.67/2.48  fof(f3,axiom,(
% 15.67/2.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f32,plain,(
% 15.67/2.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 15.67/2.48    inference(cnf_transformation,[],[f3])).
% 15.67/2.48  
% 15.67/2.48  fof(f53,plain,(
% 15.67/2.48    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))),
% 15.67/2.48    inference(definition_unfolding,[],[f46,f32])).
% 15.67/2.48  
% 15.67/2.48  fof(f6,axiom,(
% 15.67/2.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f19,plain,(
% 15.67/2.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.67/2.48    inference(ennf_transformation,[],[f6])).
% 15.67/2.48  
% 15.67/2.48  fof(f35,plain,(
% 15.67/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.67/2.48    inference(cnf_transformation,[],[f19])).
% 15.67/2.48  
% 15.67/2.48  fof(f14,axiom,(
% 15.67/2.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f45,plain,(
% 15.67/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 15.67/2.48    inference(cnf_transformation,[],[f14])).
% 15.67/2.48  
% 15.67/2.48  fof(f50,plain,(
% 15.67/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1))) )),
% 15.67/2.48    inference(definition_unfolding,[],[f45,f32])).
% 15.67/2.48  
% 15.67/2.48  fof(f7,axiom,(
% 15.67/2.48    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f36,plain,(
% 15.67/2.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 15.67/2.48    inference(cnf_transformation,[],[f7])).
% 15.67/2.48  
% 15.67/2.48  fof(f5,axiom,(
% 15.67/2.48    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f34,plain,(
% 15.67/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 15.67/2.48    inference(cnf_transformation,[],[f5])).
% 15.67/2.48  
% 15.67/2.48  fof(f47,plain,(
% 15.67/2.48    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 15.67/2.48    inference(cnf_transformation,[],[f29])).
% 15.67/2.48  
% 15.67/2.48  fof(f52,plain,(
% 15.67/2.48    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))),
% 15.67/2.48    inference(definition_unfolding,[],[f47,f32])).
% 15.67/2.48  
% 15.67/2.48  fof(f4,axiom,(
% 15.67/2.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f18,plain,(
% 15.67/2.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.67/2.48    inference(ennf_transformation,[],[f4])).
% 15.67/2.48  
% 15.67/2.48  fof(f33,plain,(
% 15.67/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.67/2.48    inference(cnf_transformation,[],[f18])).
% 15.67/2.48  
% 15.67/2.48  fof(f1,axiom,(
% 15.67/2.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f17,plain,(
% 15.67/2.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 15.67/2.48    inference(ennf_transformation,[],[f1])).
% 15.67/2.48  
% 15.67/2.48  fof(f30,plain,(
% 15.67/2.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 15.67/2.48    inference(cnf_transformation,[],[f17])).
% 15.67/2.48  
% 15.67/2.48  fof(f2,axiom,(
% 15.67/2.48    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f31,plain,(
% 15.67/2.48    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 15.67/2.48    inference(cnf_transformation,[],[f2])).
% 15.67/2.48  
% 15.67/2.48  fof(f49,plain,(
% 15.67/2.48    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) )),
% 15.67/2.48    inference(definition_unfolding,[],[f31,f32])).
% 15.67/2.48  
% 15.67/2.48  fof(f12,axiom,(
% 15.67/2.48    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f23,plain,(
% 15.67/2.48    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 15.67/2.48    inference(ennf_transformation,[],[f12])).
% 15.67/2.48  
% 15.67/2.48  fof(f42,plain,(
% 15.67/2.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 15.67/2.48    inference(cnf_transformation,[],[f23])).
% 15.67/2.48  
% 15.67/2.48  fof(f13,axiom,(
% 15.67/2.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 15.67/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.67/2.48  
% 15.67/2.48  fof(f24,plain,(
% 15.67/2.48    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 15.67/2.48    inference(ennf_transformation,[],[f13])).
% 15.67/2.48  
% 15.67/2.48  fof(f44,plain,(
% 15.67/2.48    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 15.67/2.48    inference(cnf_transformation,[],[f24])).
% 15.67/2.48  
% 15.67/2.48  fof(f48,plain,(
% 15.67/2.48    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k5_xboole_0(sK1,sK2))),
% 15.67/2.48    inference(cnf_transformation,[],[f29])).
% 15.67/2.48  
% 15.67/2.48  fof(f51,plain,(
% 15.67/2.48    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))),
% 15.67/2.48    inference(definition_unfolding,[],[f48,f32])).
% 15.67/2.48  
% 15.67/2.48  cnf(c_220,plain,
% 15.67/2.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.67/2.48      theory(equality) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_19958,plain,
% 15.67/2.48      ( ~ r1_tarski(X0,X1)
% 15.67/2.48      | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
% 15.67/2.48      | k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) != X1
% 15.67/2.48      | sK0 != X0 ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_220]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_28616,plain,
% 15.67/2.48      ( ~ r1_tarski(X0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
% 15.67/2.48      | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
% 15.67/2.48      | k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
% 15.67/2.48      | sK0 != X0 ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_19958]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_60693,plain,
% 15.67/2.48      ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
% 15.67/2.48      | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
% 15.67/2.48      | k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
% 15.67/2.48      | sK0 != k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_28616]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_7,plain,
% 15.67/2.48      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 15.67/2.48      inference(cnf_transformation,[],[f38]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1120,plain,
% 15.67/2.48      ( k4_xboole_0(k2_xboole_0(sK0,X0),X0) = k4_xboole_0(sK0,X0) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_7]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_33849,plain,
% 15.67/2.48      ( k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_1120]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1489,plain,
% 15.67/2.48      ( r1_tarski(X0,X1)
% 15.67/2.48      | ~ r1_tarski(k4_xboole_0(sK0,X2),k4_xboole_0(k2_xboole_0(sK1,sK2),X2))
% 15.67/2.48      | X1 != k4_xboole_0(k2_xboole_0(sK1,sK2),X2)
% 15.67/2.48      | X0 != k4_xboole_0(sK0,X2) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_220]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_6864,plain,
% 15.67/2.48      ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,X0),X0),X1)
% 15.67/2.48      | ~ r1_tarski(k4_xboole_0(sK0,X0),k4_xboole_0(k2_xboole_0(sK1,sK2),X0))
% 15.67/2.48      | X1 != k4_xboole_0(k2_xboole_0(sK1,sK2),X0)
% 15.67/2.48      | k4_xboole_0(k2_xboole_0(sK0,X0),X0) != k4_xboole_0(sK0,X0) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_1489]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_24897,plain,
% 15.67/2.48      ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
% 15.67/2.48      | ~ r1_tarski(k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
% 15.67/2.48      | k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) != k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
% 15.67/2.48      | k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_6864]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_6,plain,
% 15.67/2.48      ( ~ r1_tarski(X0,X1)
% 15.67/2.48      | r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
% 15.67/2.48      inference(cnf_transformation,[],[f37]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_927,plain,
% 15.67/2.48      ( r1_tarski(k4_xboole_0(sK0,X0),k4_xboole_0(k2_xboole_0(sK1,sK2),X0))
% 15.67/2.48      | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_6]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_17969,plain,
% 15.67/2.48      ( r1_tarski(k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
% 15.67/2.48      | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_927]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_17,negated_conjecture,
% 15.67/2.48      ( r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
% 15.67/2.48      | r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
% 15.67/2.48      inference(cnf_transformation,[],[f53]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_594,plain,
% 15.67/2.48      ( r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) = iProver_top
% 15.67/2.48      | r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_4,plain,
% 15.67/2.48      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.67/2.48      inference(cnf_transformation,[],[f35]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_605,plain,
% 15.67/2.48      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_884,plain,
% 15.67/2.48      ( k3_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) = sK0
% 15.67/2.48      | r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_594,c_605]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1384,plain,
% 15.67/2.48      ( k3_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) = sK0
% 15.67/2.48      | k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_884,c_605]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_14,plain,
% 15.67/2.48      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 15.67/2.48      inference(cnf_transformation,[],[f50]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_5,plain,
% 15.67/2.48      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
% 15.67/2.48      inference(cnf_transformation,[],[f36]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_604,plain,
% 15.67/2.48      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1270,plain,
% 15.67/2.48      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))),k3_xboole_0(X0,k3_xboole_0(X1,X2))),k2_xboole_0(X1,X2)) = iProver_top ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_14,c_604]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_10331,plain,
% 15.67/2.48      ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
% 15.67/2.48      | r1_tarski(k2_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2)) = iProver_top ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_1384,c_1270]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_3,plain,
% 15.67/2.48      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 15.67/2.48      inference(cnf_transformation,[],[f34]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_10453,plain,
% 15.67/2.48      ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
% 15.67/2.48      | r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 15.67/2.48      inference(demodulation,[status(thm)],[c_10331,c_3]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_928,plain,
% 15.67/2.48      ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
% 15.67/2.48      | k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_4]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_932,plain,
% 15.67/2.48      ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0
% 15.67/2.48      | r1_tarski(sK0,k2_xboole_0(sK1,sK2)) != iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_928]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_10692,plain,
% 15.67/2.48      ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = sK0 ),
% 15.67/2.48      inference(global_propositional_subsumption,
% 15.67/2.48                [status(thm)],
% 15.67/2.48                [c_10453,c_932]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1269,plain,
% 15.67/2.48      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))),X1) = iProver_top ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_3,c_604]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_10705,plain,
% 15.67/2.48      ( r1_tarski(k2_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,sK2),X0))),k2_xboole_0(sK1,sK2)) = iProver_top ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_10692,c_1269]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_10742,plain,
% 15.67/2.48      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 15.67/2.48      inference(demodulation,[status(thm)],[c_10705,c_3]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_10762,plain,
% 15.67/2.48      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
% 15.67/2.48      inference(predicate_to_equality_rev,[status(thm)],[c_10742]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_215,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1659,plain,
% 15.67/2.48      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_215]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_3514,plain,
% 15.67/2.48      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_1659]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_7958,plain,
% 15.67/2.48      ( k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) != sK0
% 15.67/2.48      | sK0 = k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2))
% 15.67/2.48      | sK0 != sK0 ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_3514]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_2236,plain,
% 15.67/2.48      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
% 15.67/2.48      | r1_tarski(X3,k4_xboole_0(k2_xboole_0(X1,X2),X2))
% 15.67/2.48      | X3 != X0 ),
% 15.67/2.48      inference(resolution,[status(thm)],[c_220,c_7]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_16,negated_conjecture,
% 15.67/2.48      ( r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
% 15.67/2.48      | r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
% 15.67/2.48      inference(cnf_transformation,[],[f52]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_7636,plain,
% 15.67/2.48      ( r1_tarski(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)))
% 15.67/2.48      | r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
% 15.67/2.48      | X0 != sK0 ),
% 15.67/2.48      inference(resolution,[status(thm)],[c_2236,c_16]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_595,plain,
% 15.67/2.48      ( r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) = iProver_top
% 15.67/2.48      | r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_2,plain,
% 15.67/2.48      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 15.67/2.48      inference(cnf_transformation,[],[f33]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_606,plain,
% 15.67/2.48      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 15.67/2.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_989,plain,
% 15.67/2.48      ( k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) = k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
% 15.67/2.48      | r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = iProver_top ),
% 15.67/2.48      inference(superposition,[status(thm)],[c_595,c_606]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_999,plain,
% 15.67/2.48      ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
% 15.67/2.48      | k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) = k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
% 15.67/2.48      inference(predicate_to_equality_rev,[status(thm)],[c_989]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_0,plain,
% 15.67/2.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 15.67/2.48      inference(cnf_transformation,[],[f30]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1447,plain,
% 15.67/2.48      ( ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
% 15.67/2.48      | r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_0]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_214,plain,( X0 = X0 ),theory(equality) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1216,plain,
% 15.67/2.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X0,X1) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_214]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1782,plain,
% 15.67/2.48      ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,sK2) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_1216]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_216,plain,
% 15.67/2.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.67/2.48      theory(equality) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_799,plain,
% 15.67/2.48      ( r1_xboole_0(X0,X1)
% 15.67/2.48      | ~ r1_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(k2_xboole_0(X2,X3),k3_xboole_0(X2,X3)))
% 15.67/2.48      | X1 != k4_xboole_0(k2_xboole_0(X2,X3),k3_xboole_0(X2,X3))
% 15.67/2.48      | X0 != k3_xboole_0(X2,X3) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_216]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1215,plain,
% 15.67/2.48      ( r1_xboole_0(k3_xboole_0(X0,X1),X2)
% 15.67/2.48      | ~ r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)))
% 15.67/2.48      | X2 != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
% 15.67/2.48      | k3_xboole_0(X0,X1) != k3_xboole_0(X0,X1) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_799]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_2459,plain,
% 15.67/2.48      ( ~ r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
% 15.67/2.48      | r1_xboole_0(k3_xboole_0(sK1,sK2),k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))))
% 15.67/2.48      | k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) != k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
% 15.67/2.48      | k3_xboole_0(sK1,sK2) != k3_xboole_0(sK1,sK2) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_1215]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1,plain,
% 15.67/2.48      ( r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
% 15.67/2.48      inference(cnf_transformation,[],[f49]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_2773,plain,
% 15.67/2.48      ( r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_1]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_11,plain,
% 15.67/2.48      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.67/2.48      inference(cnf_transformation,[],[f42]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_5768,plain,
% 15.67/2.48      ( ~ r1_xboole_0(k3_xboole_0(sK1,sK2),k2_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))))
% 15.67/2.48      | r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_11]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_7924,plain,
% 15.67/2.48      ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
% 15.67/2.48      inference(global_propositional_subsumption,
% 15.67/2.48                [status(thm)],
% 15.67/2.48                [c_7636,c_999,c_1447,c_1782,c_2459,c_2773,c_5768]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_2480,plain,
% 15.67/2.48      ( k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_214]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_4598,plain,
% 15.67/2.48      ( k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) = k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_2480]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_1025,plain,
% 15.67/2.48      ( sK0 = sK0 ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_214]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_13,plain,
% 15.67/2.48      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ),
% 15.67/2.48      inference(cnf_transformation,[],[f44]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_911,plain,
% 15.67/2.48      ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
% 15.67/2.48      | k4_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK1,sK2)) = sK0 ),
% 15.67/2.48      inference(instantiation,[status(thm)],[c_13]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(c_15,negated_conjecture,
% 15.67/2.48      ( ~ r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
% 15.67/2.48      | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
% 15.67/2.48      | ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
% 15.67/2.48      inference(cnf_transformation,[],[f51]) ).
% 15.67/2.48  
% 15.67/2.48  cnf(contradiction,plain,
% 15.67/2.48      ( $false ),
% 15.67/2.48      inference(minisat,
% 15.67/2.48                [status(thm)],
% 15.67/2.48                [c_60693,c_33849,c_24897,c_17969,c_10762,c_7958,c_7924,
% 15.67/2.48                 c_4598,c_1025,c_911,c_15]) ).
% 15.67/2.48  
% 15.67/2.48  
% 15.67/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.67/2.48  
% 15.67/2.48  ------                               Statistics
% 15.67/2.48  
% 15.67/2.48  ------ Selected
% 15.67/2.48  
% 15.67/2.48  total_time:                             1.804
% 15.67/2.48  
%------------------------------------------------------------------------------
