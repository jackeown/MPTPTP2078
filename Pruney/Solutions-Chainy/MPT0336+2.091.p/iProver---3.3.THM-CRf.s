%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:48 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :  164 (2130 expanded)
%              Number of clauses        :  102 ( 620 expanded)
%              Number of leaves         :   19 ( 626 expanded)
%              Depth                    :   23
%              Number of atoms          :  311 (2839 expanded)
%              Number of equality atoms :  110 (1897 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :   13 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f20,plain,(
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

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f34])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f32])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
      & r1_xboole_0(sK4,sK3)
      & r2_hidden(sK5,sK4)
      & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f33,f39])).

fof(f66,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f63,f61])).

fof(f65,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f64,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_tarski(sK5,sK5)) ),
    inference(definition_unfolding,[],[f64,f51,f61])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f52,f51,f51])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f41,f51,f51])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f36])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f51])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f67,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2472,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_17274,plain,
    ( ~ r2_hidden(sK1(sK2,sK3),X0)
    | ~ r2_hidden(sK1(sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0) ),
    inference(instantiation,[status(thm)],[c_2472])).

cnf(c_17276,plain,
    ( ~ r2_hidden(sK1(sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK1(sK2,sK3),k1_xboole_0)
    | ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_17274])).

cnf(c_22,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_913,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_928,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2139,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_913,c_928])).

cnf(c_19,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_tarski(X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_916,plain,
    ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_912,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_927,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12410,plain,
    ( r2_hidden(sK5,X0) != iProver_top
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_912,c_927])).

cnf(c_13322,plain,
    ( k4_xboole_0(X0,k2_tarski(sK5,sK5)) = X0
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_916,c_12410])).

cnf(c_13835,plain,
    ( k4_xboole_0(sK3,k2_tarski(sK5,sK5)) = sK3 ),
    inference(superposition,[status(thm)],[c_2139,c_13322])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_tarski(sK5,sK5)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_305,plain,
    ( k2_tarski(sK5,sK5) != X0
    | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = X1
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_306,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_tarski(sK5,sK5))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_10,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_929,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_306,c_10])).

cnf(c_13845,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_13835,c_929])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_11,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1950,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_11])).

cnf(c_2126,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_1950,c_10])).

cnf(c_13,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_922,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_18,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_917,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3046,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_922,c_917])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3051,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3046,c_7])).

cnf(c_7875,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2126,c_2126,c_3051])).

cnf(c_7887,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_7875])).

cnf(c_1959,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),X0))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0) ),
    inference(superposition,[status(thm)],[c_929,c_10])).

cnf(c_1967,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),X3) ),
    inference(superposition,[status(thm)],[c_10,c_10])).

cnf(c_1972,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))))))) ),
    inference(demodulation,[status(thm)],[c_1967,c_10])).

cnf(c_1976,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),X0))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,X0))) ),
    inference(demodulation,[status(thm)],[c_1959,c_10,c_1972])).

cnf(c_2493,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),X0)))) ),
    inference(superposition,[status(thm)],[c_0,c_1976])).

cnf(c_1964,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),X0))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),X0) ),
    inference(superposition,[status(thm)],[c_929,c_10])).

cnf(c_1974,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),X0))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),X0))) ),
    inference(demodulation,[status(thm)],[c_1964,c_10])).

cnf(c_2651,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))) ),
    inference(superposition,[status(thm)],[c_2493,c_1974])).

cnf(c_7901,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))))))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))) ),
    inference(superposition,[status(thm)],[c_2651,c_7875])).

cnf(c_1955,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_0,c_10])).

cnf(c_7914,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_1955,c_7875])).

cnf(c_8040,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_7914,c_10])).

cnf(c_2633,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),X0)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))) ),
    inference(superposition,[status(thm)],[c_0,c_1974])).

cnf(c_7926,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),X0)))) ),
    inference(superposition,[status(thm)],[c_2633,c_7875])).

cnf(c_7950,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_7875,c_10])).

cnf(c_8024,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))) = k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),X0)) ),
    inference(demodulation,[status(thm)],[c_7926,c_7875,c_7950])).

cnf(c_8041,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))) ),
    inference(demodulation,[status(thm)],[c_8040,c_8024])).

cnf(c_8054,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))) ),
    inference(demodulation,[status(thm)],[c_7901,c_7875,c_8041])).

cnf(c_3058,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3051,c_1950])).

cnf(c_8055,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))))) = sK2 ),
    inference(demodulation,[status(thm)],[c_8054,c_3051,c_3058])).

cnf(c_7927,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))))) ),
    inference(superposition,[status(thm)],[c_2651,c_7875])).

cnf(c_8023,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))) = k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))) ),
    inference(demodulation,[status(thm)],[c_7927,c_7875,c_7950])).

cnf(c_8042,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))) ),
    inference(demodulation,[status(thm)],[c_8041,c_8023])).

cnf(c_2495,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k1_xboole_0)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1950,c_1976])).

cnf(c_2500,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k1_xboole_0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2495,c_1950])).

cnf(c_3059,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3051,c_2500])).

cnf(c_8043,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8042,c_1976,c_3059])).

cnf(c_8056,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8055,c_8043])).

cnf(c_7889,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1955,c_7875])).

cnf(c_8077,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_7889,c_10])).

cnf(c_7919,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_1955,c_7875])).

cnf(c_8031,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_7919,c_10])).

cnf(c_8032,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_8031,c_10])).

cnf(c_8033,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_8032,c_7875])).

cnf(c_8090,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_8077,c_8033])).

cnf(c_2124,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10,c_1950])).

cnf(c_5679,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2124,c_10,c_3051])).

cnf(c_7909,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5679,c_7875])).

cnf(c_8046,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7909,c_3051])).

cnf(c_8094,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_7887,c_8046])).

cnf(c_13846,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_13845,c_7887,c_8056,c_8090,c_8094])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_923,plain,
    ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_14861,plain,
    ( r2_hidden(sK1(sK2,sK3),k1_xboole_0) = iProver_top
    | r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_13846,c_923])).

cnf(c_14902,plain,
    ( r2_hidden(sK1(sK2,sK3),k1_xboole_0)
    | r1_xboole_0(sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14861])).

cnf(c_1499,plain,
    ( r2_hidden(sK1(X0,sK3),k4_xboole_0(X0,k4_xboole_0(X0,sK3)))
    | r1_xboole_0(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_6821,plain,
    ( r2_hidden(sK1(sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1499])).

cnf(c_1675,plain,
    ( ~ r1_xboole_0(X0,sK3)
    | r1_xboole_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3210,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1675])).

cnf(c_2097,plain,
    ( ~ r2_hidden(sK0(k2_tarski(sK5,sK5),X0),X0)
    | ~ r2_hidden(sK0(k2_tarski(sK5,sK5),X0),X1)
    | ~ r1_xboole_0(X1,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2099,plain,
    ( ~ r2_hidden(sK0(k2_tarski(sK5,sK5),k1_xboole_0),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2097])).

cnf(c_1378,plain,
    ( r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1182,plain,
    ( r2_hidden(sK0(k2_tarski(sK5,sK5),X0),X0)
    | r1_xboole_0(k2_tarski(sK5,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1189,plain,
    ( r2_hidden(sK0(k2_tarski(sK5,sK5),k1_xboole_0),k1_xboole_0)
    | r1_xboole_0(k2_tarski(sK5,sK5),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1182])).

cnf(c_16,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1084,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
    | ~ r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_972,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_293,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | k2_tarski(sK5,sK5) != X0
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_294,plain,
    ( ~ r1_xboole_0(k2_tarski(sK5,sK5),X0)
    | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0) ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_296,plain,
    ( ~ r1_xboole_0(k2_tarski(sK5,sK5),k1_xboole_0)
    | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_49,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_21,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17276,c_14902,c_6821,c_3210,c_2099,c_1378,c_1189,c_1084,c_972,c_296,c_49,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:13:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.51/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/1.48  
% 7.51/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.51/1.48  
% 7.51/1.48  ------  iProver source info
% 7.51/1.48  
% 7.51/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.51/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.51/1.48  git: non_committed_changes: false
% 7.51/1.48  git: last_make_outside_of_git: false
% 7.51/1.48  
% 7.51/1.48  ------ 
% 7.51/1.48  
% 7.51/1.48  ------ Input Options
% 7.51/1.48  
% 7.51/1.48  --out_options                           all
% 7.51/1.48  --tptp_safe_out                         true
% 7.51/1.48  --problem_path                          ""
% 7.51/1.48  --include_path                          ""
% 7.51/1.48  --clausifier                            res/vclausify_rel
% 7.51/1.48  --clausifier_options                    ""
% 7.51/1.48  --stdin                                 false
% 7.51/1.48  --stats_out                             all
% 7.51/1.48  
% 7.51/1.48  ------ General Options
% 7.51/1.48  
% 7.51/1.48  --fof                                   false
% 7.51/1.48  --time_out_real                         305.
% 7.51/1.48  --time_out_virtual                      -1.
% 7.51/1.48  --symbol_type_check                     false
% 7.51/1.48  --clausify_out                          false
% 7.51/1.48  --sig_cnt_out                           false
% 7.51/1.48  --trig_cnt_out                          false
% 7.51/1.48  --trig_cnt_out_tolerance                1.
% 7.51/1.48  --trig_cnt_out_sk_spl                   false
% 7.51/1.48  --abstr_cl_out                          false
% 7.51/1.48  
% 7.51/1.48  ------ Global Options
% 7.51/1.48  
% 7.51/1.48  --schedule                              default
% 7.51/1.48  --add_important_lit                     false
% 7.51/1.48  --prop_solver_per_cl                    1000
% 7.51/1.48  --min_unsat_core                        false
% 7.51/1.48  --soft_assumptions                      false
% 7.51/1.48  --soft_lemma_size                       3
% 7.51/1.48  --prop_impl_unit_size                   0
% 7.51/1.48  --prop_impl_unit                        []
% 7.51/1.48  --share_sel_clauses                     true
% 7.51/1.48  --reset_solvers                         false
% 7.51/1.48  --bc_imp_inh                            [conj_cone]
% 7.51/1.48  --conj_cone_tolerance                   3.
% 7.51/1.48  --extra_neg_conj                        none
% 7.51/1.48  --large_theory_mode                     true
% 7.51/1.48  --prolific_symb_bound                   200
% 7.51/1.48  --lt_threshold                          2000
% 7.51/1.48  --clause_weak_htbl                      true
% 7.51/1.48  --gc_record_bc_elim                     false
% 7.51/1.48  
% 7.51/1.48  ------ Preprocessing Options
% 7.51/1.48  
% 7.51/1.48  --preprocessing_flag                    true
% 7.51/1.48  --time_out_prep_mult                    0.1
% 7.51/1.48  --splitting_mode                        input
% 7.51/1.48  --splitting_grd                         true
% 7.51/1.48  --splitting_cvd                         false
% 7.51/1.48  --splitting_cvd_svl                     false
% 7.51/1.48  --splitting_nvd                         32
% 7.51/1.48  --sub_typing                            true
% 7.51/1.48  --prep_gs_sim                           true
% 7.51/1.48  --prep_unflatten                        true
% 7.51/1.48  --prep_res_sim                          true
% 7.51/1.48  --prep_upred                            true
% 7.51/1.48  --prep_sem_filter                       exhaustive
% 7.51/1.48  --prep_sem_filter_out                   false
% 7.51/1.48  --pred_elim                             true
% 7.51/1.48  --res_sim_input                         true
% 7.51/1.48  --eq_ax_congr_red                       true
% 7.51/1.48  --pure_diseq_elim                       true
% 7.51/1.48  --brand_transform                       false
% 7.51/1.48  --non_eq_to_eq                          false
% 7.51/1.48  --prep_def_merge                        true
% 7.51/1.48  --prep_def_merge_prop_impl              false
% 7.51/1.48  --prep_def_merge_mbd                    true
% 7.51/1.48  --prep_def_merge_tr_red                 false
% 7.51/1.48  --prep_def_merge_tr_cl                  false
% 7.51/1.48  --smt_preprocessing                     true
% 7.51/1.48  --smt_ac_axioms                         fast
% 7.51/1.48  --preprocessed_out                      false
% 7.51/1.48  --preprocessed_stats                    false
% 7.51/1.48  
% 7.51/1.48  ------ Abstraction refinement Options
% 7.51/1.48  
% 7.51/1.48  --abstr_ref                             []
% 7.51/1.48  --abstr_ref_prep                        false
% 7.51/1.48  --abstr_ref_until_sat                   false
% 7.51/1.48  --abstr_ref_sig_restrict                funpre
% 7.51/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.51/1.48  --abstr_ref_under                       []
% 7.51/1.48  
% 7.51/1.48  ------ SAT Options
% 7.51/1.48  
% 7.51/1.48  --sat_mode                              false
% 7.51/1.48  --sat_fm_restart_options                ""
% 7.51/1.48  --sat_gr_def                            false
% 7.51/1.48  --sat_epr_types                         true
% 7.51/1.48  --sat_non_cyclic_types                  false
% 7.51/1.48  --sat_finite_models                     false
% 7.51/1.48  --sat_fm_lemmas                         false
% 7.51/1.48  --sat_fm_prep                           false
% 7.51/1.48  --sat_fm_uc_incr                        true
% 7.51/1.48  --sat_out_model                         small
% 7.51/1.48  --sat_out_clauses                       false
% 7.51/1.48  
% 7.51/1.48  ------ QBF Options
% 7.51/1.48  
% 7.51/1.48  --qbf_mode                              false
% 7.51/1.48  --qbf_elim_univ                         false
% 7.51/1.48  --qbf_dom_inst                          none
% 7.51/1.48  --qbf_dom_pre_inst                      false
% 7.51/1.48  --qbf_sk_in                             false
% 7.51/1.48  --qbf_pred_elim                         true
% 7.51/1.48  --qbf_split                             512
% 7.51/1.48  
% 7.51/1.48  ------ BMC1 Options
% 7.51/1.48  
% 7.51/1.48  --bmc1_incremental                      false
% 7.51/1.48  --bmc1_axioms                           reachable_all
% 7.51/1.48  --bmc1_min_bound                        0
% 7.51/1.48  --bmc1_max_bound                        -1
% 7.51/1.48  --bmc1_max_bound_default                -1
% 7.51/1.48  --bmc1_symbol_reachability              true
% 7.51/1.48  --bmc1_property_lemmas                  false
% 7.51/1.48  --bmc1_k_induction                      false
% 7.51/1.48  --bmc1_non_equiv_states                 false
% 7.51/1.48  --bmc1_deadlock                         false
% 7.51/1.48  --bmc1_ucm                              false
% 7.51/1.48  --bmc1_add_unsat_core                   none
% 7.51/1.48  --bmc1_unsat_core_children              false
% 7.51/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.51/1.48  --bmc1_out_stat                         full
% 7.51/1.48  --bmc1_ground_init                      false
% 7.51/1.48  --bmc1_pre_inst_next_state              false
% 7.51/1.48  --bmc1_pre_inst_state                   false
% 7.51/1.48  --bmc1_pre_inst_reach_state             false
% 7.51/1.48  --bmc1_out_unsat_core                   false
% 7.51/1.48  --bmc1_aig_witness_out                  false
% 7.51/1.48  --bmc1_verbose                          false
% 7.51/1.48  --bmc1_dump_clauses_tptp                false
% 7.51/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.51/1.48  --bmc1_dump_file                        -
% 7.51/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.51/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.51/1.48  --bmc1_ucm_extend_mode                  1
% 7.51/1.48  --bmc1_ucm_init_mode                    2
% 7.51/1.48  --bmc1_ucm_cone_mode                    none
% 7.51/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.51/1.48  --bmc1_ucm_relax_model                  4
% 7.51/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.51/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.51/1.48  --bmc1_ucm_layered_model                none
% 7.51/1.48  --bmc1_ucm_max_lemma_size               10
% 7.51/1.48  
% 7.51/1.48  ------ AIG Options
% 7.51/1.48  
% 7.51/1.48  --aig_mode                              false
% 7.51/1.48  
% 7.51/1.48  ------ Instantiation Options
% 7.51/1.48  
% 7.51/1.48  --instantiation_flag                    true
% 7.51/1.48  --inst_sos_flag                         true
% 7.51/1.48  --inst_sos_phase                        true
% 7.51/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.51/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.51/1.48  --inst_lit_sel_side                     num_symb
% 7.51/1.48  --inst_solver_per_active                1400
% 7.51/1.48  --inst_solver_calls_frac                1.
% 7.51/1.48  --inst_passive_queue_type               priority_queues
% 7.51/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.51/1.48  --inst_passive_queues_freq              [25;2]
% 7.51/1.48  --inst_dismatching                      true
% 7.51/1.48  --inst_eager_unprocessed_to_passive     true
% 7.51/1.48  --inst_prop_sim_given                   true
% 7.51/1.48  --inst_prop_sim_new                     false
% 7.51/1.48  --inst_subs_new                         false
% 7.51/1.48  --inst_eq_res_simp                      false
% 7.51/1.48  --inst_subs_given                       false
% 7.51/1.48  --inst_orphan_elimination               true
% 7.51/1.48  --inst_learning_loop_flag               true
% 7.51/1.48  --inst_learning_start                   3000
% 7.51/1.48  --inst_learning_factor                  2
% 7.51/1.48  --inst_start_prop_sim_after_learn       3
% 7.51/1.48  --inst_sel_renew                        solver
% 7.51/1.48  --inst_lit_activity_flag                true
% 7.51/1.48  --inst_restr_to_given                   false
% 7.51/1.48  --inst_activity_threshold               500
% 7.51/1.48  --inst_out_proof                        true
% 7.51/1.48  
% 7.51/1.48  ------ Resolution Options
% 7.51/1.48  
% 7.51/1.48  --resolution_flag                       true
% 7.51/1.48  --res_lit_sel                           adaptive
% 7.51/1.48  --res_lit_sel_side                      none
% 7.51/1.48  --res_ordering                          kbo
% 7.51/1.48  --res_to_prop_solver                    active
% 7.51/1.48  --res_prop_simpl_new                    false
% 7.51/1.48  --res_prop_simpl_given                  true
% 7.51/1.48  --res_passive_queue_type                priority_queues
% 7.51/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.51/1.48  --res_passive_queues_freq               [15;5]
% 7.51/1.48  --res_forward_subs                      full
% 7.51/1.48  --res_backward_subs                     full
% 7.51/1.48  --res_forward_subs_resolution           true
% 7.51/1.48  --res_backward_subs_resolution          true
% 7.51/1.48  --res_orphan_elimination                true
% 7.51/1.48  --res_time_limit                        2.
% 7.51/1.48  --res_out_proof                         true
% 7.51/1.48  
% 7.51/1.48  ------ Superposition Options
% 7.51/1.48  
% 7.51/1.48  --superposition_flag                    true
% 7.51/1.48  --sup_passive_queue_type                priority_queues
% 7.51/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.51/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.51/1.48  --demod_completeness_check              fast
% 7.51/1.48  --demod_use_ground                      true
% 7.51/1.48  --sup_to_prop_solver                    passive
% 7.51/1.48  --sup_prop_simpl_new                    true
% 7.51/1.48  --sup_prop_simpl_given                  true
% 7.51/1.48  --sup_fun_splitting                     true
% 7.51/1.48  --sup_smt_interval                      50000
% 7.51/1.48  
% 7.51/1.48  ------ Superposition Simplification Setup
% 7.51/1.48  
% 7.51/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.51/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.51/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.51/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.51/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.51/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.51/1.48  --sup_immed_triv                        [TrivRules]
% 7.51/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.51/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.51/1.48  --sup_immed_bw_main                     []
% 7.51/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.51/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.51/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.51/1.48  --sup_input_bw                          []
% 7.51/1.48  
% 7.51/1.48  ------ Combination Options
% 7.51/1.48  
% 7.51/1.48  --comb_res_mult                         3
% 7.51/1.48  --comb_sup_mult                         2
% 7.51/1.48  --comb_inst_mult                        10
% 7.51/1.48  
% 7.51/1.48  ------ Debug Options
% 7.51/1.48  
% 7.51/1.48  --dbg_backtrace                         false
% 7.51/1.48  --dbg_dump_prop_clauses                 false
% 7.51/1.48  --dbg_dump_prop_clauses_file            -
% 7.51/1.48  --dbg_out_stat                          false
% 7.51/1.48  ------ Parsing...
% 7.51/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.51/1.48  
% 7.51/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.51/1.48  
% 7.51/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.51/1.48  
% 7.51/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.51/1.48  ------ Proving...
% 7.51/1.48  ------ Problem Properties 
% 7.51/1.48  
% 7.51/1.48  
% 7.51/1.48  clauses                                 24
% 7.51/1.48  conjectures                             3
% 7.51/1.48  EPR                                     6
% 7.51/1.48  Horn                                    20
% 7.51/1.48  unary                                   9
% 7.51/1.48  binary                                  12
% 7.51/1.48  lits                                    43
% 7.51/1.48  lits eq                                 10
% 7.51/1.48  fd_pure                                 0
% 7.51/1.48  fd_pseudo                               0
% 7.51/1.48  fd_cond                                 0
% 7.51/1.48  fd_pseudo_cond                          1
% 7.51/1.48  AC symbols                              0
% 7.51/1.48  
% 7.51/1.48  ------ Schedule dynamic 5 is on 
% 7.51/1.48  
% 7.51/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.51/1.48  
% 7.51/1.48  
% 7.51/1.48  ------ 
% 7.51/1.48  Current options:
% 7.51/1.48  ------ 
% 7.51/1.48  
% 7.51/1.48  ------ Input Options
% 7.51/1.48  
% 7.51/1.48  --out_options                           all
% 7.51/1.48  --tptp_safe_out                         true
% 7.51/1.48  --problem_path                          ""
% 7.51/1.48  --include_path                          ""
% 7.51/1.48  --clausifier                            res/vclausify_rel
% 7.51/1.48  --clausifier_options                    ""
% 7.51/1.48  --stdin                                 false
% 7.51/1.48  --stats_out                             all
% 7.51/1.48  
% 7.51/1.48  ------ General Options
% 7.51/1.48  
% 7.51/1.48  --fof                                   false
% 7.51/1.48  --time_out_real                         305.
% 7.51/1.48  --time_out_virtual                      -1.
% 7.51/1.48  --symbol_type_check                     false
% 7.51/1.48  --clausify_out                          false
% 7.51/1.48  --sig_cnt_out                           false
% 7.51/1.48  --trig_cnt_out                          false
% 7.51/1.48  --trig_cnt_out_tolerance                1.
% 7.51/1.48  --trig_cnt_out_sk_spl                   false
% 7.51/1.48  --abstr_cl_out                          false
% 7.51/1.48  
% 7.51/1.48  ------ Global Options
% 7.51/1.48  
% 7.51/1.48  --schedule                              default
% 7.51/1.48  --add_important_lit                     false
% 7.51/1.48  --prop_solver_per_cl                    1000
% 7.51/1.48  --min_unsat_core                        false
% 7.51/1.48  --soft_assumptions                      false
% 7.51/1.48  --soft_lemma_size                       3
% 7.51/1.48  --prop_impl_unit_size                   0
% 7.51/1.48  --prop_impl_unit                        []
% 7.51/1.48  --share_sel_clauses                     true
% 7.51/1.48  --reset_solvers                         false
% 7.51/1.48  --bc_imp_inh                            [conj_cone]
% 7.51/1.48  --conj_cone_tolerance                   3.
% 7.51/1.48  --extra_neg_conj                        none
% 7.51/1.48  --large_theory_mode                     true
% 7.51/1.48  --prolific_symb_bound                   200
% 7.51/1.48  --lt_threshold                          2000
% 7.51/1.48  --clause_weak_htbl                      true
% 7.51/1.48  --gc_record_bc_elim                     false
% 7.51/1.48  
% 7.51/1.48  ------ Preprocessing Options
% 7.51/1.48  
% 7.51/1.48  --preprocessing_flag                    true
% 7.51/1.48  --time_out_prep_mult                    0.1
% 7.51/1.48  --splitting_mode                        input
% 7.51/1.48  --splitting_grd                         true
% 7.51/1.48  --splitting_cvd                         false
% 7.51/1.48  --splitting_cvd_svl                     false
% 7.51/1.48  --splitting_nvd                         32
% 7.51/1.48  --sub_typing                            true
% 7.51/1.48  --prep_gs_sim                           true
% 7.51/1.48  --prep_unflatten                        true
% 7.51/1.48  --prep_res_sim                          true
% 7.51/1.48  --prep_upred                            true
% 7.51/1.48  --prep_sem_filter                       exhaustive
% 7.51/1.48  --prep_sem_filter_out                   false
% 7.51/1.48  --pred_elim                             true
% 7.51/1.48  --res_sim_input                         true
% 7.51/1.48  --eq_ax_congr_red                       true
% 7.51/1.48  --pure_diseq_elim                       true
% 7.51/1.48  --brand_transform                       false
% 7.51/1.48  --non_eq_to_eq                          false
% 7.51/1.48  --prep_def_merge                        true
% 7.51/1.48  --prep_def_merge_prop_impl              false
% 7.51/1.48  --prep_def_merge_mbd                    true
% 7.51/1.48  --prep_def_merge_tr_red                 false
% 7.51/1.48  --prep_def_merge_tr_cl                  false
% 7.51/1.48  --smt_preprocessing                     true
% 7.51/1.48  --smt_ac_axioms                         fast
% 7.51/1.48  --preprocessed_out                      false
% 7.51/1.48  --preprocessed_stats                    false
% 7.51/1.48  
% 7.51/1.48  ------ Abstraction refinement Options
% 7.51/1.48  
% 7.51/1.48  --abstr_ref                             []
% 7.51/1.48  --abstr_ref_prep                        false
% 7.51/1.48  --abstr_ref_until_sat                   false
% 7.51/1.48  --abstr_ref_sig_restrict                funpre
% 7.51/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.51/1.48  --abstr_ref_under                       []
% 7.51/1.48  
% 7.51/1.48  ------ SAT Options
% 7.51/1.48  
% 7.51/1.48  --sat_mode                              false
% 7.51/1.48  --sat_fm_restart_options                ""
% 7.51/1.48  --sat_gr_def                            false
% 7.51/1.48  --sat_epr_types                         true
% 7.51/1.48  --sat_non_cyclic_types                  false
% 7.51/1.48  --sat_finite_models                     false
% 7.51/1.48  --sat_fm_lemmas                         false
% 7.51/1.48  --sat_fm_prep                           false
% 7.51/1.48  --sat_fm_uc_incr                        true
% 7.51/1.48  --sat_out_model                         small
% 7.51/1.48  --sat_out_clauses                       false
% 7.51/1.48  
% 7.51/1.48  ------ QBF Options
% 7.51/1.48  
% 7.51/1.48  --qbf_mode                              false
% 7.51/1.48  --qbf_elim_univ                         false
% 7.51/1.48  --qbf_dom_inst                          none
% 7.51/1.48  --qbf_dom_pre_inst                      false
% 7.51/1.48  --qbf_sk_in                             false
% 7.51/1.48  --qbf_pred_elim                         true
% 7.51/1.48  --qbf_split                             512
% 7.51/1.48  
% 7.51/1.48  ------ BMC1 Options
% 7.51/1.48  
% 7.51/1.48  --bmc1_incremental                      false
% 7.51/1.48  --bmc1_axioms                           reachable_all
% 7.51/1.48  --bmc1_min_bound                        0
% 7.51/1.48  --bmc1_max_bound                        -1
% 7.51/1.48  --bmc1_max_bound_default                -1
% 7.51/1.48  --bmc1_symbol_reachability              true
% 7.51/1.48  --bmc1_property_lemmas                  false
% 7.51/1.48  --bmc1_k_induction                      false
% 7.51/1.48  --bmc1_non_equiv_states                 false
% 7.51/1.48  --bmc1_deadlock                         false
% 7.51/1.48  --bmc1_ucm                              false
% 7.51/1.48  --bmc1_add_unsat_core                   none
% 7.51/1.48  --bmc1_unsat_core_children              false
% 7.51/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.51/1.48  --bmc1_out_stat                         full
% 7.51/1.48  --bmc1_ground_init                      false
% 7.51/1.48  --bmc1_pre_inst_next_state              false
% 7.51/1.48  --bmc1_pre_inst_state                   false
% 7.51/1.48  --bmc1_pre_inst_reach_state             false
% 7.51/1.48  --bmc1_out_unsat_core                   false
% 7.51/1.48  --bmc1_aig_witness_out                  false
% 7.51/1.48  --bmc1_verbose                          false
% 7.51/1.48  --bmc1_dump_clauses_tptp                false
% 7.51/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.51/1.48  --bmc1_dump_file                        -
% 7.51/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.51/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.51/1.48  --bmc1_ucm_extend_mode                  1
% 7.51/1.48  --bmc1_ucm_init_mode                    2
% 7.51/1.48  --bmc1_ucm_cone_mode                    none
% 7.51/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.51/1.48  --bmc1_ucm_relax_model                  4
% 7.51/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.51/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.51/1.48  --bmc1_ucm_layered_model                none
% 7.51/1.48  --bmc1_ucm_max_lemma_size               10
% 7.51/1.48  
% 7.51/1.48  ------ AIG Options
% 7.51/1.48  
% 7.51/1.48  --aig_mode                              false
% 7.51/1.48  
% 7.51/1.48  ------ Instantiation Options
% 7.51/1.48  
% 7.51/1.48  --instantiation_flag                    true
% 7.51/1.48  --inst_sos_flag                         true
% 7.51/1.48  --inst_sos_phase                        true
% 7.51/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.51/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.51/1.48  --inst_lit_sel_side                     none
% 7.51/1.48  --inst_solver_per_active                1400
% 7.51/1.48  --inst_solver_calls_frac                1.
% 7.51/1.48  --inst_passive_queue_type               priority_queues
% 7.51/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.51/1.48  --inst_passive_queues_freq              [25;2]
% 7.51/1.48  --inst_dismatching                      true
% 7.51/1.48  --inst_eager_unprocessed_to_passive     true
% 7.51/1.48  --inst_prop_sim_given                   true
% 7.51/1.48  --inst_prop_sim_new                     false
% 7.51/1.48  --inst_subs_new                         false
% 7.51/1.48  --inst_eq_res_simp                      false
% 7.51/1.48  --inst_subs_given                       false
% 7.51/1.48  --inst_orphan_elimination               true
% 7.51/1.48  --inst_learning_loop_flag               true
% 7.51/1.48  --inst_learning_start                   3000
% 7.51/1.48  --inst_learning_factor                  2
% 7.51/1.48  --inst_start_prop_sim_after_learn       3
% 7.51/1.48  --inst_sel_renew                        solver
% 7.51/1.48  --inst_lit_activity_flag                true
% 7.51/1.48  --inst_restr_to_given                   false
% 7.51/1.48  --inst_activity_threshold               500
% 7.51/1.48  --inst_out_proof                        true
% 7.51/1.48  
% 7.51/1.48  ------ Resolution Options
% 7.51/1.48  
% 7.51/1.48  --resolution_flag                       false
% 7.51/1.48  --res_lit_sel                           adaptive
% 7.51/1.48  --res_lit_sel_side                      none
% 7.51/1.48  --res_ordering                          kbo
% 7.51/1.48  --res_to_prop_solver                    active
% 7.51/1.48  --res_prop_simpl_new                    false
% 7.51/1.48  --res_prop_simpl_given                  true
% 7.51/1.48  --res_passive_queue_type                priority_queues
% 7.51/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.51/1.48  --res_passive_queues_freq               [15;5]
% 7.51/1.48  --res_forward_subs                      full
% 7.51/1.48  --res_backward_subs                     full
% 7.51/1.48  --res_forward_subs_resolution           true
% 7.51/1.48  --res_backward_subs_resolution          true
% 7.51/1.48  --res_orphan_elimination                true
% 7.51/1.48  --res_time_limit                        2.
% 7.51/1.48  --res_out_proof                         true
% 7.51/1.48  
% 7.51/1.48  ------ Superposition Options
% 7.51/1.48  
% 7.51/1.48  --superposition_flag                    true
% 7.51/1.48  --sup_passive_queue_type                priority_queues
% 7.51/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.51/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.51/1.48  --demod_completeness_check              fast
% 7.51/1.48  --demod_use_ground                      true
% 7.51/1.48  --sup_to_prop_solver                    passive
% 7.51/1.48  --sup_prop_simpl_new                    true
% 7.51/1.48  --sup_prop_simpl_given                  true
% 7.51/1.48  --sup_fun_splitting                     true
% 7.51/1.48  --sup_smt_interval                      50000
% 7.51/1.48  
% 7.51/1.48  ------ Superposition Simplification Setup
% 7.51/1.48  
% 7.51/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.51/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.51/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.51/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.51/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.51/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.51/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.51/1.48  --sup_immed_triv                        [TrivRules]
% 7.51/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.51/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.51/1.48  --sup_immed_bw_main                     []
% 7.51/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.51/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.51/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.51/1.48  --sup_input_bw                          []
% 7.51/1.48  
% 7.51/1.48  ------ Combination Options
% 7.51/1.48  
% 7.51/1.48  --comb_res_mult                         3
% 7.51/1.48  --comb_sup_mult                         2
% 7.51/1.48  --comb_inst_mult                        10
% 7.51/1.48  
% 7.51/1.48  ------ Debug Options
% 7.51/1.48  
% 7.51/1.48  --dbg_backtrace                         false
% 7.51/1.48  --dbg_dump_prop_clauses                 false
% 7.51/1.48  --dbg_dump_prop_clauses_file            -
% 7.51/1.48  --dbg_out_stat                          false
% 7.51/1.48  
% 7.51/1.48  
% 7.51/1.48  
% 7.51/1.48  
% 7.51/1.48  ------ Proving...
% 7.51/1.48  
% 7.51/1.48  
% 7.51/1.48  % SZS status Theorem for theBenchmark.p
% 7.51/1.48  
% 7.51/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.51/1.48  
% 7.51/1.48  fof(f3,axiom,(
% 7.51/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f20,plain,(
% 7.51/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.51/1.48    inference(rectify,[],[f3])).
% 7.51/1.48  
% 7.51/1.48  fof(f23,plain,(
% 7.51/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.51/1.48    inference(ennf_transformation,[],[f20])).
% 7.51/1.48  
% 7.51/1.48  fof(f34,plain,(
% 7.51/1.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.51/1.48    introduced(choice_axiom,[])).
% 7.51/1.48  
% 7.51/1.48  fof(f35,plain,(
% 7.51/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.51/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f34])).
% 7.51/1.48  
% 7.51/1.48  fof(f45,plain,(
% 7.51/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.51/1.48    inference(cnf_transformation,[],[f35])).
% 7.51/1.48  
% 7.51/1.48  fof(f18,conjecture,(
% 7.51/1.48    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f19,negated_conjecture,(
% 7.51/1.48    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.51/1.48    inference(negated_conjecture,[],[f18])).
% 7.51/1.48  
% 7.51/1.48  fof(f32,plain,(
% 7.51/1.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 7.51/1.48    inference(ennf_transformation,[],[f19])).
% 7.51/1.48  
% 7.51/1.48  fof(f33,plain,(
% 7.51/1.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 7.51/1.48    inference(flattening,[],[f32])).
% 7.51/1.48  
% 7.51/1.48  fof(f39,plain,(
% 7.51/1.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 7.51/1.48    introduced(choice_axiom,[])).
% 7.51/1.48  
% 7.51/1.48  fof(f40,plain,(
% 7.51/1.48    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 7.51/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f33,f39])).
% 7.51/1.48  
% 7.51/1.48  fof(f66,plain,(
% 7.51/1.48    r1_xboole_0(sK4,sK3)),
% 7.51/1.48    inference(cnf_transformation,[],[f40])).
% 7.51/1.48  
% 7.51/1.48  fof(f2,axiom,(
% 7.51/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f22,plain,(
% 7.51/1.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.51/1.48    inference(ennf_transformation,[],[f2])).
% 7.51/1.48  
% 7.51/1.48  fof(f42,plain,(
% 7.51/1.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.51/1.48    inference(cnf_transformation,[],[f22])).
% 7.51/1.48  
% 7.51/1.48  fof(f17,axiom,(
% 7.51/1.48    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f38,plain,(
% 7.51/1.48    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 7.51/1.48    inference(nnf_transformation,[],[f17])).
% 7.51/1.48  
% 7.51/1.48  fof(f63,plain,(
% 7.51/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 7.51/1.48    inference(cnf_transformation,[],[f38])).
% 7.51/1.48  
% 7.51/1.48  fof(f16,axiom,(
% 7.51/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f61,plain,(
% 7.51/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.51/1.48    inference(cnf_transformation,[],[f16])).
% 7.51/1.48  
% 7.51/1.48  fof(f73,plain,(
% 7.51/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k2_tarski(X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 7.51/1.48    inference(definition_unfolding,[],[f63,f61])).
% 7.51/1.48  
% 7.51/1.48  fof(f65,plain,(
% 7.51/1.48    r2_hidden(sK5,sK4)),
% 7.51/1.48    inference(cnf_transformation,[],[f40])).
% 7.51/1.48  
% 7.51/1.48  fof(f6,axiom,(
% 7.51/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f25,plain,(
% 7.51/1.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.51/1.48    inference(ennf_transformation,[],[f6])).
% 7.51/1.48  
% 7.51/1.48  fof(f49,plain,(
% 7.51/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.51/1.48    inference(cnf_transformation,[],[f25])).
% 7.51/1.48  
% 7.51/1.48  fof(f8,axiom,(
% 7.51/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f51,plain,(
% 7.51/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.51/1.48    inference(cnf_transformation,[],[f8])).
% 7.51/1.48  
% 7.51/1.48  fof(f71,plain,(
% 7.51/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.51/1.48    inference(definition_unfolding,[],[f49,f51])).
% 7.51/1.48  
% 7.51/1.48  fof(f64,plain,(
% 7.51/1.48    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 7.51/1.48    inference(cnf_transformation,[],[f40])).
% 7.51/1.48  
% 7.51/1.48  fof(f75,plain,(
% 7.51/1.48    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_tarski(sK5,sK5))),
% 7.51/1.48    inference(definition_unfolding,[],[f64,f51,f61])).
% 7.51/1.48  
% 7.51/1.48  fof(f9,axiom,(
% 7.51/1.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f52,plain,(
% 7.51/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.51/1.48    inference(cnf_transformation,[],[f9])).
% 7.51/1.48  
% 7.51/1.48  fof(f72,plain,(
% 7.51/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 7.51/1.48    inference(definition_unfolding,[],[f52,f51,f51])).
% 7.51/1.48  
% 7.51/1.48  fof(f1,axiom,(
% 7.51/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f41,plain,(
% 7.51/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.51/1.48    inference(cnf_transformation,[],[f1])).
% 7.51/1.48  
% 7.51/1.48  fof(f68,plain,(
% 7.51/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.51/1.48    inference(definition_unfolding,[],[f41,f51,f51])).
% 7.51/1.48  
% 7.51/1.48  fof(f10,axiom,(
% 7.51/1.48    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f53,plain,(
% 7.51/1.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 7.51/1.48    inference(cnf_transformation,[],[f10])).
% 7.51/1.48  
% 7.51/1.48  fof(f12,axiom,(
% 7.51/1.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f55,plain,(
% 7.51/1.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.51/1.48    inference(cnf_transformation,[],[f12])).
% 7.51/1.48  
% 7.51/1.48  fof(f15,axiom,(
% 7.51/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f31,plain,(
% 7.51/1.48    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 7.51/1.48    inference(ennf_transformation,[],[f15])).
% 7.51/1.48  
% 7.51/1.48  fof(f60,plain,(
% 7.51/1.48    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.51/1.48    inference(cnf_transformation,[],[f31])).
% 7.51/1.48  
% 7.51/1.48  fof(f5,axiom,(
% 7.51/1.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f48,plain,(
% 7.51/1.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.51/1.48    inference(cnf_transformation,[],[f5])).
% 7.51/1.48  
% 7.51/1.48  fof(f4,axiom,(
% 7.51/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f21,plain,(
% 7.51/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.51/1.48    inference(rectify,[],[f4])).
% 7.51/1.48  
% 7.51/1.48  fof(f24,plain,(
% 7.51/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.51/1.48    inference(ennf_transformation,[],[f21])).
% 7.51/1.48  
% 7.51/1.48  fof(f36,plain,(
% 7.51/1.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 7.51/1.48    introduced(choice_axiom,[])).
% 7.51/1.48  
% 7.51/1.48  fof(f37,plain,(
% 7.51/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.51/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f36])).
% 7.51/1.48  
% 7.51/1.48  fof(f46,plain,(
% 7.51/1.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 7.51/1.48    inference(cnf_transformation,[],[f37])).
% 7.51/1.48  
% 7.51/1.48  fof(f70,plain,(
% 7.51/1.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 7.51/1.48    inference(definition_unfolding,[],[f46,f51])).
% 7.51/1.48  
% 7.51/1.48  fof(f44,plain,(
% 7.51/1.48    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.51/1.48    inference(cnf_transformation,[],[f35])).
% 7.51/1.48  
% 7.51/1.48  fof(f13,axiom,(
% 7.51/1.48    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f28,plain,(
% 7.51/1.48    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.51/1.48    inference(ennf_transformation,[],[f13])).
% 7.51/1.48  
% 7.51/1.48  fof(f56,plain,(
% 7.51/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.51/1.48    inference(cnf_transformation,[],[f28])).
% 7.51/1.48  
% 7.51/1.48  fof(f11,axiom,(
% 7.51/1.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 7.51/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.51/1.48  
% 7.51/1.48  fof(f26,plain,(
% 7.51/1.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.51/1.48    inference(ennf_transformation,[],[f11])).
% 7.51/1.48  
% 7.51/1.48  fof(f27,plain,(
% 7.51/1.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 7.51/1.48    inference(flattening,[],[f26])).
% 7.51/1.48  
% 7.51/1.48  fof(f54,plain,(
% 7.51/1.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.51/1.48    inference(cnf_transformation,[],[f27])).
% 7.51/1.48  
% 7.51/1.48  fof(f67,plain,(
% 7.51/1.48    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 7.51/1.48    inference(cnf_transformation,[],[f40])).
% 7.51/1.48  
% 7.51/1.48  cnf(c_2,plain,
% 7.51/1.48      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.51/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_2472,plain,
% 7.51/1.48      ( ~ r2_hidden(X0,X1)
% 7.51/1.48      | ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 7.51/1.48      | ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X1) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_17274,plain,
% 7.51/1.48      ( ~ r2_hidden(sK1(sK2,sK3),X0)
% 7.51/1.48      | ~ r2_hidden(sK1(sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 7.51/1.48      | ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_2472]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_17276,plain,
% 7.51/1.48      ( ~ r2_hidden(sK1(sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 7.51/1.48      | ~ r2_hidden(sK1(sK2,sK3),k1_xboole_0)
% 7.51/1.48      | ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_xboole_0) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_17274]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_22,negated_conjecture,
% 7.51/1.48      ( r1_xboole_0(sK4,sK3) ),
% 7.51/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_913,plain,
% 7.51/1.48      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 7.51/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_1,plain,
% 7.51/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.51/1.48      inference(cnf_transformation,[],[f42]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_928,plain,
% 7.51/1.48      ( r1_xboole_0(X0,X1) != iProver_top
% 7.51/1.48      | r1_xboole_0(X1,X0) = iProver_top ),
% 7.51/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_2139,plain,
% 7.51/1.48      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_913,c_928]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_19,plain,
% 7.51/1.48      ( r2_hidden(X0,X1) | k4_xboole_0(X1,k2_tarski(X0,X0)) = X1 ),
% 7.51/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_916,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
% 7.51/1.48      | r2_hidden(X1,X0) = iProver_top ),
% 7.51/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_23,negated_conjecture,
% 7.51/1.48      ( r2_hidden(sK5,sK4) ),
% 7.51/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_912,plain,
% 7.51/1.48      ( r2_hidden(sK5,sK4) = iProver_top ),
% 7.51/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_927,plain,
% 7.51/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.51/1.48      | r2_hidden(X0,X2) != iProver_top
% 7.51/1.48      | r1_xboole_0(X2,X1) != iProver_top ),
% 7.51/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_12410,plain,
% 7.51/1.48      ( r2_hidden(sK5,X0) != iProver_top
% 7.51/1.48      | r1_xboole_0(X0,sK4) != iProver_top ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_912,c_927]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_13322,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k2_tarski(sK5,sK5)) = X0
% 7.51/1.48      | r1_xboole_0(X0,sK4) != iProver_top ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_916,c_12410]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_13835,plain,
% 7.51/1.48      ( k4_xboole_0(sK3,k2_tarski(sK5,sK5)) = sK3 ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_2139,c_13322]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8,plain,
% 7.51/1.48      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.51/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_24,negated_conjecture,
% 7.51/1.48      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_tarski(sK5,sK5)) ),
% 7.51/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_305,plain,
% 7.51/1.48      ( k2_tarski(sK5,sK5) != X0
% 7.51/1.48      | k4_xboole_0(X1,k4_xboole_0(X1,X0)) = X1
% 7.51/1.48      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X1 ),
% 7.51/1.48      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_306,plain,
% 7.51/1.48      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k2_tarski(sK5,sK5))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 7.51/1.48      inference(unflattening,[status(thm)],[c_305]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_10,plain,
% 7.51/1.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.51/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_929,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_306,c_10]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_13845,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_13835,c_929]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_0,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.51/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_11,plain,
% 7.51/1.48      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.51/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_1950,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_0,c_11]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_2126,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_1950,c_10]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_13,plain,
% 7.51/1.48      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.51/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_922,plain,
% 7.51/1.48      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.51/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_18,plain,
% 7.51/1.48      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ),
% 7.51/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_917,plain,
% 7.51/1.48      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
% 7.51/1.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.51/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_3046,plain,
% 7.51/1.48      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_922,c_917]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_7,plain,
% 7.51/1.48      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.51/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_3051,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.51/1.48      inference(light_normalisation,[status(thm)],[c_3046,c_7]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_7875,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.51/1.48      inference(light_normalisation,[status(thm)],[c_2126,c_2126,c_3051]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_7887,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_0,c_7875]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_1959,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),X0))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_929,c_10]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_1967,plain,
% 7.51/1.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))),X3) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_10,c_10]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_1972,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3))))))) ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_1967,c_10]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_1976,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),X0))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,X0))) ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_1959,c_10,c_1972]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_2493,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),X0)))) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_0,c_1976]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_1964,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),X0))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))),X0) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_929,c_10]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_1974,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),X0))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),X0))) ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_1964,c_10]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_2651,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_2493,c_1974]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_7901,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))))))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_2651,c_7875]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_1955,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_0,c_10]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_7914,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_1955,c_7875]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8040,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_7914,c_10]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_2633,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),X0)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_0,c_1974]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_7926,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),X0)))) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_2633,c_7875]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_7950,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_7875,c_10]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8024,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))) = k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),X0)) ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_7926,c_7875,c_7950]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8041,plain,
% 7.51/1.48      ( k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))) ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_8040,c_8024]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8054,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))) ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_7901,c_7875,c_8041]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_3058,plain,
% 7.51/1.48      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_3051,c_1950]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8055,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))))) = sK2 ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_8054,c_3051,c_3058]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_7927,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))))) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_2651,c_7875]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8023,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))) = k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))),k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))))) ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_7927,c_7875,c_7950]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8042,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))) ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_8041,c_8023]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_2495,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k1_xboole_0)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k1_xboole_0)) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_1950,c_1976]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_2500,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k1_xboole_0)))) = k1_xboole_0 ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_2495,c_1950]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_3059,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))) = k1_xboole_0 ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_3051,c_2500]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8043,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5))))),k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k2_tarski(sK5,sK5)))))))))) = k1_xboole_0 ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_8042,c_1976,c_3059]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8056,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_8055,c_8043]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_7889,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_1955,c_7875]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8077,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_7889,c_10]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_7919,plain,
% 7.51/1.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_1955,c_7875]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8031,plain,
% 7.51/1.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.51/1.48      inference(light_normalisation,[status(thm)],[c_7919,c_10]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8032,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_8031,c_10]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8033,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_8032,c_7875]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8090,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_8077,c_8033]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_2124,plain,
% 7.51/1.48      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)))) = k1_xboole_0 ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_10,c_1950]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_5679,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_2124,c_10,c_3051]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_7909,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_5679,c_7875]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8046,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = X0 ),
% 7.51/1.48      inference(light_normalisation,[status(thm)],[c_7909,c_3051]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_8094,plain,
% 7.51/1.48      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.51/1.48      inference(demodulation,[status(thm)],[c_7887,c_8046]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_13846,plain,
% 7.51/1.48      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 7.51/1.48      inference(demodulation,
% 7.51/1.48                [status(thm)],
% 7.51/1.48                [c_13845,c_7887,c_8056,c_8090,c_8094]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_6,plain,
% 7.51/1.48      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 7.51/1.48      | r1_xboole_0(X0,X1) ),
% 7.51/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_923,plain,
% 7.51/1.48      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top
% 7.51/1.48      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.51/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_14861,plain,
% 7.51/1.48      ( r2_hidden(sK1(sK2,sK3),k1_xboole_0) = iProver_top
% 7.51/1.48      | r1_xboole_0(sK2,sK3) = iProver_top ),
% 7.51/1.48      inference(superposition,[status(thm)],[c_13846,c_923]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_14902,plain,
% 7.51/1.48      ( r2_hidden(sK1(sK2,sK3),k1_xboole_0) | r1_xboole_0(sK2,sK3) ),
% 7.51/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_14861]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_1499,plain,
% 7.51/1.48      ( r2_hidden(sK1(X0,sK3),k4_xboole_0(X0,k4_xboole_0(X0,sK3)))
% 7.51/1.48      | r1_xboole_0(X0,sK3) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_6821,plain,
% 7.51/1.48      ( r2_hidden(sK1(sK2,sK3),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 7.51/1.48      | r1_xboole_0(sK2,sK3) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_1499]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_1675,plain,
% 7.51/1.48      ( ~ r1_xboole_0(X0,sK3) | r1_xboole_0(sK3,X0) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_3210,plain,
% 7.51/1.48      ( r1_xboole_0(sK3,sK2) | ~ r1_xboole_0(sK2,sK3) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_1675]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_2097,plain,
% 7.51/1.48      ( ~ r2_hidden(sK0(k2_tarski(sK5,sK5),X0),X0)
% 7.51/1.48      | ~ r2_hidden(sK0(k2_tarski(sK5,sK5),X0),X1)
% 7.51/1.48      | ~ r1_xboole_0(X1,X0) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_2099,plain,
% 7.51/1.48      ( ~ r2_hidden(sK0(k2_tarski(sK5,sK5),k1_xboole_0),k1_xboole_0)
% 7.51/1.48      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_2097]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_1378,plain,
% 7.51/1.48      ( r1_xboole_0(sK3,sK4) | ~ r1_xboole_0(sK4,sK3) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_3,plain,
% 7.51/1.48      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 7.51/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_1182,plain,
% 7.51/1.48      ( r2_hidden(sK0(k2_tarski(sK5,sK5),X0),X0)
% 7.51/1.48      | r1_xboole_0(k2_tarski(sK5,sK5),X0) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_1189,plain,
% 7.51/1.48      ( r2_hidden(sK0(k2_tarski(sK5,sK5),k1_xboole_0),k1_xboole_0)
% 7.51/1.48      | r1_xboole_0(k2_tarski(sK5,sK5),k1_xboole_0) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_1182]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_16,plain,
% 7.51/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.51/1.48      | ~ r1_xboole_0(X0,X2)
% 7.51/1.48      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.51/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_1084,plain,
% 7.51/1.48      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
% 7.51/1.48      | ~ r1_xboole_0(sK3,sK4)
% 7.51/1.48      | ~ r1_xboole_0(sK3,sK2) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_16]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_972,plain,
% 7.51/1.48      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
% 7.51/1.48      | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_12,plain,
% 7.51/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 7.51/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_293,plain,
% 7.51/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.51/1.48      | r1_xboole_0(X2,X1)
% 7.51/1.48      | k2_tarski(sK5,sK5) != X0
% 7.51/1.48      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) != X2 ),
% 7.51/1.48      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_294,plain,
% 7.51/1.48      ( ~ r1_xboole_0(k2_tarski(sK5,sK5),X0)
% 7.51/1.48      | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X0) ),
% 7.51/1.48      inference(unflattening,[status(thm)],[c_293]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_296,plain,
% 7.51/1.48      ( ~ r1_xboole_0(k2_tarski(sK5,sK5),k1_xboole_0)
% 7.51/1.48      | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_xboole_0) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_294]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_49,plain,
% 7.51/1.48      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 7.51/1.48      inference(instantiation,[status(thm)],[c_13]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(c_21,negated_conjecture,
% 7.51/1.48      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 7.51/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.51/1.48  
% 7.51/1.48  cnf(contradiction,plain,
% 7.51/1.48      ( $false ),
% 7.51/1.48      inference(minisat,
% 7.51/1.48                [status(thm)],
% 7.51/1.48                [c_17276,c_14902,c_6821,c_3210,c_2099,c_1378,c_1189,
% 7.51/1.48                 c_1084,c_972,c_296,c_49,c_21,c_22]) ).
% 7.51/1.48  
% 7.51/1.48  
% 7.51/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.51/1.48  
% 7.51/1.48  ------                               Statistics
% 7.51/1.48  
% 7.51/1.48  ------ General
% 7.51/1.48  
% 7.51/1.48  abstr_ref_over_cycles:                  0
% 7.51/1.48  abstr_ref_under_cycles:                 0
% 7.51/1.48  gc_basic_clause_elim:                   0
% 7.51/1.48  forced_gc_time:                         0
% 7.51/1.48  parsing_time:                           0.008
% 7.51/1.48  unif_index_cands_time:                  0.
% 7.51/1.48  unif_index_add_time:                    0.
% 7.51/1.48  orderings_time:                         0.
% 7.51/1.48  out_proof_time:                         0.012
% 7.51/1.48  total_time:                             0.615
% 7.51/1.48  num_of_symbols:                         44
% 7.51/1.48  num_of_terms:                           35085
% 7.51/1.48  
% 7.51/1.48  ------ Preprocessing
% 7.51/1.48  
% 7.51/1.48  num_of_splits:                          0
% 7.51/1.48  num_of_split_atoms:                     0
% 7.51/1.48  num_of_reused_defs:                     0
% 7.51/1.48  num_eq_ax_congr_red:                    12
% 7.51/1.48  num_of_sem_filtered_clauses:            1
% 7.51/1.48  num_of_subtypes:                        0
% 7.51/1.48  monotx_restored_types:                  0
% 7.51/1.48  sat_num_of_epr_types:                   0
% 7.51/1.48  sat_num_of_non_cyclic_types:            0
% 7.51/1.48  sat_guarded_non_collapsed_types:        0
% 7.51/1.48  num_pure_diseq_elim:                    0
% 7.51/1.48  simp_replaced_by:                       0
% 7.51/1.48  res_preprocessed:                       112
% 7.51/1.48  prep_upred:                             0
% 7.51/1.48  prep_unflattend:                        8
% 7.51/1.48  smt_new_axioms:                         0
% 7.51/1.48  pred_elim_cands:                        2
% 7.51/1.48  pred_elim:                              1
% 7.51/1.48  pred_elim_cl:                           1
% 7.51/1.48  pred_elim_cycles:                       3
% 7.51/1.48  merged_defs:                            8
% 7.51/1.48  merged_defs_ncl:                        0
% 7.51/1.48  bin_hyper_res:                          8
% 7.51/1.48  prep_cycles:                            4
% 7.51/1.48  pred_elim_time:                         0.002
% 7.51/1.48  splitting_time:                         0.
% 7.51/1.48  sem_filter_time:                        0.
% 7.51/1.48  monotx_time:                            0.
% 7.51/1.48  subtype_inf_time:                       0.
% 7.51/1.48  
% 7.51/1.48  ------ Problem properties
% 7.51/1.48  
% 7.51/1.48  clauses:                                24
% 7.51/1.48  conjectures:                            3
% 7.51/1.48  epr:                                    6
% 7.51/1.48  horn:                                   20
% 7.51/1.48  ground:                                 4
% 7.51/1.48  unary:                                  9
% 7.51/1.48  binary:                                 12
% 7.51/1.48  lits:                                   43
% 7.51/1.48  lits_eq:                                10
% 7.51/1.48  fd_pure:                                0
% 7.51/1.48  fd_pseudo:                              0
% 7.51/1.48  fd_cond:                                0
% 7.51/1.48  fd_pseudo_cond:                         1
% 7.51/1.48  ac_symbols:                             0
% 7.51/1.48  
% 7.51/1.48  ------ Propositional Solver
% 7.51/1.48  
% 7.51/1.48  prop_solver_calls:                      29
% 7.51/1.48  prop_fast_solver_calls:                 599
% 7.51/1.48  smt_solver_calls:                       0
% 7.51/1.48  smt_fast_solver_calls:                  0
% 7.51/1.48  prop_num_of_clauses:                    7430
% 7.51/1.48  prop_preprocess_simplified:             12210
% 7.51/1.48  prop_fo_subsumed:                       1
% 7.51/1.48  prop_solver_time:                       0.
% 7.51/1.48  smt_solver_time:                        0.
% 7.51/1.48  smt_fast_solver_time:                   0.
% 7.51/1.48  prop_fast_solver_time:                  0.
% 7.51/1.48  prop_unsat_core_time:                   0.001
% 7.51/1.48  
% 7.51/1.48  ------ QBF
% 7.51/1.48  
% 7.51/1.48  qbf_q_res:                              0
% 7.51/1.48  qbf_num_tautologies:                    0
% 7.51/1.48  qbf_prep_cycles:                        0
% 7.51/1.48  
% 7.51/1.48  ------ BMC1
% 7.51/1.48  
% 7.51/1.48  bmc1_current_bound:                     -1
% 7.51/1.48  bmc1_last_solved_bound:                 -1
% 7.51/1.48  bmc1_unsat_core_size:                   -1
% 7.51/1.48  bmc1_unsat_core_parents_size:           -1
% 7.51/1.48  bmc1_merge_next_fun:                    0
% 7.51/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.51/1.48  
% 7.51/1.48  ------ Instantiation
% 7.51/1.48  
% 7.51/1.48  inst_num_of_clauses:                    1592
% 7.51/1.48  inst_num_in_passive:                    478
% 7.51/1.48  inst_num_in_active:                     527
% 7.51/1.48  inst_num_in_unprocessed:                586
% 7.51/1.48  inst_num_of_loops:                      564
% 7.51/1.48  inst_num_of_learning_restarts:          0
% 7.51/1.48  inst_num_moves_active_passive:          36
% 7.51/1.48  inst_lit_activity:                      0
% 7.51/1.48  inst_lit_activity_moves:                0
% 7.51/1.48  inst_num_tautologies:                   0
% 7.51/1.48  inst_num_prop_implied:                  0
% 7.51/1.48  inst_num_existing_simplified:           0
% 7.51/1.48  inst_num_eq_res_simplified:             0
% 7.51/1.48  inst_num_child_elim:                    0
% 7.51/1.48  inst_num_of_dismatching_blockings:      853
% 7.51/1.48  inst_num_of_non_proper_insts:           1832
% 7.51/1.48  inst_num_of_duplicates:                 0
% 7.51/1.48  inst_inst_num_from_inst_to_res:         0
% 7.51/1.48  inst_dismatching_checking_time:         0.
% 7.51/1.48  
% 7.51/1.48  ------ Resolution
% 7.51/1.48  
% 7.51/1.48  res_num_of_clauses:                     0
% 7.51/1.48  res_num_in_passive:                     0
% 7.51/1.48  res_num_in_active:                      0
% 7.51/1.48  res_num_of_loops:                       116
% 7.51/1.48  res_forward_subset_subsumed:            80
% 7.51/1.48  res_backward_subset_subsumed:           0
% 7.51/1.48  res_forward_subsumed:                   1
% 7.51/1.48  res_backward_subsumed:                  0
% 7.51/1.48  res_forward_subsumption_resolution:     0
% 7.51/1.48  res_backward_subsumption_resolution:    0
% 7.51/1.48  res_clause_to_clause_subsumption:       10194
% 7.51/1.48  res_orphan_elimination:                 0
% 7.51/1.48  res_tautology_del:                      78
% 7.51/1.48  res_num_eq_res_simplified:              0
% 7.51/1.48  res_num_sel_changes:                    0
% 7.51/1.48  res_moves_from_active_to_pass:          0
% 7.51/1.48  
% 7.51/1.48  ------ Superposition
% 7.51/1.48  
% 7.51/1.48  sup_time_total:                         0.
% 7.51/1.48  sup_time_generating:                    0.
% 7.51/1.49  sup_time_sim_full:                      0.
% 7.51/1.49  sup_time_sim_immed:                     0.
% 7.51/1.49  
% 7.51/1.49  sup_num_of_clauses:                     960
% 7.51/1.49  sup_num_in_active:                      67
% 7.51/1.49  sup_num_in_passive:                     893
% 7.51/1.49  sup_num_of_loops:                       112
% 7.51/1.49  sup_fw_superposition:                   1535
% 7.51/1.49  sup_bw_superposition:                   1103
% 7.51/1.49  sup_immediate_simplified:               1612
% 7.51/1.49  sup_given_eliminated:                   20
% 7.51/1.49  comparisons_done:                       0
% 7.51/1.49  comparisons_avoided:                    0
% 7.51/1.49  
% 7.51/1.49  ------ Simplifications
% 7.51/1.49  
% 7.51/1.49  
% 7.51/1.49  sim_fw_subset_subsumed:                 46
% 7.51/1.49  sim_bw_subset_subsumed:                 0
% 7.51/1.49  sim_fw_subsumed:                        184
% 7.51/1.49  sim_bw_subsumed:                        49
% 7.51/1.49  sim_fw_subsumption_res:                 0
% 7.51/1.49  sim_bw_subsumption_res:                 0
% 7.51/1.49  sim_tautology_del:                      6
% 7.51/1.49  sim_eq_tautology_del:                   428
% 7.51/1.49  sim_eq_res_simp:                        0
% 7.51/1.49  sim_fw_demodulated:                     1616
% 7.51/1.49  sim_bw_demodulated:                     199
% 7.51/1.49  sim_light_normalised:                   658
% 7.51/1.49  sim_joinable_taut:                      0
% 7.51/1.49  sim_joinable_simp:                      0
% 7.51/1.49  sim_ac_normalised:                      0
% 7.51/1.49  sim_smt_subsumption:                    0
% 7.51/1.49  
%------------------------------------------------------------------------------
