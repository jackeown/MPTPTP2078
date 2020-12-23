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
% DateTime   : Thu Dec  3 11:38:42 EST 2020

% Result     : Theorem 35.68s
% Output     : CNFRefutation 35.68s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 301 expanded)
%              Number of clauses        :   51 ( 102 expanded)
%              Number of leaves         :   16 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  208 ( 667 expanded)
%              Number of equality atoms :   69 ( 199 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f22])).

fof(f27,plain,
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

fof(f28,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    & r1_xboole_0(sK3,sK2)
    & r2_hidden(sK4,sK3)
    & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f27])).

fof(f49,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
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
    inference(rectify,[],[f4])).

fof(f18,plain,(
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

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f25])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f51])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f50,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2) ),
    inference(definition_unfolding,[],[f50,f52])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_678,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_688,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1714,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_688])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_680,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_689,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2560,plain,
    ( k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_680,c_689])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_677,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_687,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4314,plain,
    ( r2_hidden(sK4,X0) != iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_687])).

cnf(c_130040,plain,
    ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0) = k1_xboole_0
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2560,c_4314])).

cnf(c_133259,plain,
    ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1714,c_130040])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_133309,plain,
    ( k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_133259,c_0])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_215,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != X0
    | k3_xboole_0(X1,X0) = X1
    | k3_xboole_0(sK1,sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_216,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_7,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_350,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_xboole_0(sK1,sK2) ),
    inference(theory_normalisation,[status(thm)],[c_216,c_7,c_0])).

cnf(c_136174,plain,
    ( k3_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_133309,c_350])).

cnf(c_2561,plain,
    ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_678,c_689])).

cnf(c_2997,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(sK2,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2561,c_7])).

cnf(c_707,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_2999,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(sK2,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2561,c_707])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_684,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2558,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_684,c_689])).

cnf(c_3007,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(sK2,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2999,c_2558])).

cnf(c_3008,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2997,c_3007])).

cnf(c_705,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_1493,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_350,c_705])).

cnf(c_3217,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3008,c_1493])).

cnf(c_3221,plain,
    ( k3_xboole_0(sK1,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3217,c_3008])).

cnf(c_136175,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_136174,c_3221])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1546,plain,
    ( r1_xboole_0(X0,sK2)
    | k3_xboole_0(X0,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_75672,plain,
    ( r1_xboole_0(sK1,sK2)
    | k3_xboole_0(sK1,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1546])).

cnf(c_1309,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_852,plain,
    ( r1_xboole_0(X0,sK3)
    | ~ r1_xboole_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1069,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_771,plain,
    ( r1_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)))
    | ~ r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_725,plain,
    ( r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2)
    | ~ r1_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_136175,c_75672,c_1309,c_1069,c_771,c_725,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:56:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 35.68/5.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.68/5.00  
% 35.68/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.68/5.00  
% 35.68/5.00  ------  iProver source info
% 35.68/5.00  
% 35.68/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.68/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.68/5.00  git: non_committed_changes: false
% 35.68/5.00  git: last_make_outside_of_git: false
% 35.68/5.00  
% 35.68/5.00  ------ 
% 35.68/5.00  
% 35.68/5.00  ------ Input Options
% 35.68/5.00  
% 35.68/5.00  --out_options                           all
% 35.68/5.00  --tptp_safe_out                         true
% 35.68/5.00  --problem_path                          ""
% 35.68/5.00  --include_path                          ""
% 35.68/5.00  --clausifier                            res/vclausify_rel
% 35.68/5.00  --clausifier_options                    ""
% 35.68/5.00  --stdin                                 false
% 35.68/5.00  --stats_out                             all
% 35.68/5.00  
% 35.68/5.00  ------ General Options
% 35.68/5.00  
% 35.68/5.00  --fof                                   false
% 35.68/5.00  --time_out_real                         305.
% 35.68/5.00  --time_out_virtual                      -1.
% 35.68/5.00  --symbol_type_check                     false
% 35.68/5.00  --clausify_out                          false
% 35.68/5.00  --sig_cnt_out                           false
% 35.68/5.00  --trig_cnt_out                          false
% 35.68/5.00  --trig_cnt_out_tolerance                1.
% 35.68/5.00  --trig_cnt_out_sk_spl                   false
% 35.68/5.00  --abstr_cl_out                          false
% 35.68/5.00  
% 35.68/5.00  ------ Global Options
% 35.68/5.00  
% 35.68/5.00  --schedule                              default
% 35.68/5.00  --add_important_lit                     false
% 35.68/5.00  --prop_solver_per_cl                    1000
% 35.68/5.00  --min_unsat_core                        false
% 35.68/5.00  --soft_assumptions                      false
% 35.68/5.00  --soft_lemma_size                       3
% 35.68/5.00  --prop_impl_unit_size                   0
% 35.68/5.00  --prop_impl_unit                        []
% 35.68/5.00  --share_sel_clauses                     true
% 35.68/5.00  --reset_solvers                         false
% 35.68/5.00  --bc_imp_inh                            [conj_cone]
% 35.68/5.00  --conj_cone_tolerance                   3.
% 35.68/5.00  --extra_neg_conj                        none
% 35.68/5.00  --large_theory_mode                     true
% 35.68/5.00  --prolific_symb_bound                   200
% 35.68/5.00  --lt_threshold                          2000
% 35.68/5.00  --clause_weak_htbl                      true
% 35.68/5.00  --gc_record_bc_elim                     false
% 35.68/5.00  
% 35.68/5.00  ------ Preprocessing Options
% 35.68/5.00  
% 35.68/5.00  --preprocessing_flag                    true
% 35.68/5.00  --time_out_prep_mult                    0.1
% 35.68/5.00  --splitting_mode                        input
% 35.68/5.00  --splitting_grd                         true
% 35.68/5.00  --splitting_cvd                         false
% 35.68/5.00  --splitting_cvd_svl                     false
% 35.68/5.00  --splitting_nvd                         32
% 35.68/5.00  --sub_typing                            true
% 35.68/5.00  --prep_gs_sim                           true
% 35.68/5.00  --prep_unflatten                        true
% 35.68/5.00  --prep_res_sim                          true
% 35.68/5.00  --prep_upred                            true
% 35.68/5.00  --prep_sem_filter                       exhaustive
% 35.68/5.00  --prep_sem_filter_out                   false
% 35.68/5.00  --pred_elim                             true
% 35.68/5.00  --res_sim_input                         true
% 35.68/5.00  --eq_ax_congr_red                       true
% 35.68/5.00  --pure_diseq_elim                       true
% 35.68/5.00  --brand_transform                       false
% 35.68/5.00  --non_eq_to_eq                          false
% 35.68/5.00  --prep_def_merge                        true
% 35.68/5.00  --prep_def_merge_prop_impl              false
% 35.68/5.00  --prep_def_merge_mbd                    true
% 35.68/5.00  --prep_def_merge_tr_red                 false
% 35.68/5.00  --prep_def_merge_tr_cl                  false
% 35.68/5.00  --smt_preprocessing                     true
% 35.68/5.00  --smt_ac_axioms                         fast
% 35.68/5.00  --preprocessed_out                      false
% 35.68/5.00  --preprocessed_stats                    false
% 35.68/5.00  
% 35.68/5.00  ------ Abstraction refinement Options
% 35.68/5.00  
% 35.68/5.00  --abstr_ref                             []
% 35.68/5.00  --abstr_ref_prep                        false
% 35.68/5.00  --abstr_ref_until_sat                   false
% 35.68/5.00  --abstr_ref_sig_restrict                funpre
% 35.68/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.68/5.00  --abstr_ref_under                       []
% 35.68/5.00  
% 35.68/5.00  ------ SAT Options
% 35.68/5.00  
% 35.68/5.00  --sat_mode                              false
% 35.68/5.00  --sat_fm_restart_options                ""
% 35.68/5.00  --sat_gr_def                            false
% 35.68/5.00  --sat_epr_types                         true
% 35.68/5.00  --sat_non_cyclic_types                  false
% 35.68/5.00  --sat_finite_models                     false
% 35.68/5.00  --sat_fm_lemmas                         false
% 35.68/5.00  --sat_fm_prep                           false
% 35.68/5.00  --sat_fm_uc_incr                        true
% 35.68/5.00  --sat_out_model                         small
% 35.68/5.00  --sat_out_clauses                       false
% 35.68/5.00  
% 35.68/5.00  ------ QBF Options
% 35.68/5.00  
% 35.68/5.00  --qbf_mode                              false
% 35.68/5.00  --qbf_elim_univ                         false
% 35.68/5.00  --qbf_dom_inst                          none
% 35.68/5.00  --qbf_dom_pre_inst                      false
% 35.68/5.00  --qbf_sk_in                             false
% 35.68/5.00  --qbf_pred_elim                         true
% 35.68/5.00  --qbf_split                             512
% 35.68/5.00  
% 35.68/5.00  ------ BMC1 Options
% 35.68/5.00  
% 35.68/5.00  --bmc1_incremental                      false
% 35.68/5.00  --bmc1_axioms                           reachable_all
% 35.68/5.00  --bmc1_min_bound                        0
% 35.68/5.00  --bmc1_max_bound                        -1
% 35.68/5.00  --bmc1_max_bound_default                -1
% 35.68/5.00  --bmc1_symbol_reachability              true
% 35.68/5.00  --bmc1_property_lemmas                  false
% 35.68/5.00  --bmc1_k_induction                      false
% 35.68/5.00  --bmc1_non_equiv_states                 false
% 35.68/5.00  --bmc1_deadlock                         false
% 35.68/5.00  --bmc1_ucm                              false
% 35.68/5.00  --bmc1_add_unsat_core                   none
% 35.68/5.00  --bmc1_unsat_core_children              false
% 35.68/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.68/5.00  --bmc1_out_stat                         full
% 35.68/5.00  --bmc1_ground_init                      false
% 35.68/5.00  --bmc1_pre_inst_next_state              false
% 35.68/5.00  --bmc1_pre_inst_state                   false
% 35.68/5.00  --bmc1_pre_inst_reach_state             false
% 35.68/5.00  --bmc1_out_unsat_core                   false
% 35.68/5.00  --bmc1_aig_witness_out                  false
% 35.68/5.00  --bmc1_verbose                          false
% 35.68/5.00  --bmc1_dump_clauses_tptp                false
% 35.68/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.68/5.00  --bmc1_dump_file                        -
% 35.68/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.68/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.68/5.00  --bmc1_ucm_extend_mode                  1
% 35.68/5.00  --bmc1_ucm_init_mode                    2
% 35.68/5.00  --bmc1_ucm_cone_mode                    none
% 35.68/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.68/5.00  --bmc1_ucm_relax_model                  4
% 35.68/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.68/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.68/5.00  --bmc1_ucm_layered_model                none
% 35.68/5.00  --bmc1_ucm_max_lemma_size               10
% 35.68/5.00  
% 35.68/5.00  ------ AIG Options
% 35.68/5.00  
% 35.68/5.00  --aig_mode                              false
% 35.68/5.00  
% 35.68/5.00  ------ Instantiation Options
% 35.68/5.00  
% 35.68/5.00  --instantiation_flag                    true
% 35.68/5.00  --inst_sos_flag                         true
% 35.68/5.00  --inst_sos_phase                        true
% 35.68/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.68/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.68/5.00  --inst_lit_sel_side                     num_symb
% 35.68/5.00  --inst_solver_per_active                1400
% 35.68/5.00  --inst_solver_calls_frac                1.
% 35.68/5.00  --inst_passive_queue_type               priority_queues
% 35.68/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.68/5.00  --inst_passive_queues_freq              [25;2]
% 35.68/5.00  --inst_dismatching                      true
% 35.68/5.00  --inst_eager_unprocessed_to_passive     true
% 35.68/5.00  --inst_prop_sim_given                   true
% 35.68/5.00  --inst_prop_sim_new                     false
% 35.68/5.00  --inst_subs_new                         false
% 35.68/5.00  --inst_eq_res_simp                      false
% 35.68/5.00  --inst_subs_given                       false
% 35.68/5.00  --inst_orphan_elimination               true
% 35.68/5.00  --inst_learning_loop_flag               true
% 35.68/5.00  --inst_learning_start                   3000
% 35.68/5.00  --inst_learning_factor                  2
% 35.68/5.00  --inst_start_prop_sim_after_learn       3
% 35.68/5.00  --inst_sel_renew                        solver
% 35.68/5.00  --inst_lit_activity_flag                true
% 35.68/5.00  --inst_restr_to_given                   false
% 35.68/5.00  --inst_activity_threshold               500
% 35.68/5.00  --inst_out_proof                        true
% 35.68/5.00  
% 35.68/5.00  ------ Resolution Options
% 35.68/5.00  
% 35.68/5.00  --resolution_flag                       true
% 35.68/5.00  --res_lit_sel                           adaptive
% 35.68/5.00  --res_lit_sel_side                      none
% 35.68/5.00  --res_ordering                          kbo
% 35.68/5.00  --res_to_prop_solver                    active
% 35.68/5.00  --res_prop_simpl_new                    false
% 35.68/5.00  --res_prop_simpl_given                  true
% 35.68/5.00  --res_passive_queue_type                priority_queues
% 35.68/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.68/5.00  --res_passive_queues_freq               [15;5]
% 35.68/5.00  --res_forward_subs                      full
% 35.68/5.00  --res_backward_subs                     full
% 35.68/5.00  --res_forward_subs_resolution           true
% 35.68/5.00  --res_backward_subs_resolution          true
% 35.68/5.00  --res_orphan_elimination                true
% 35.68/5.00  --res_time_limit                        2.
% 35.68/5.00  --res_out_proof                         true
% 35.68/5.00  
% 35.68/5.00  ------ Superposition Options
% 35.68/5.00  
% 35.68/5.00  --superposition_flag                    true
% 35.68/5.00  --sup_passive_queue_type                priority_queues
% 35.68/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.68/5.00  --sup_passive_queues_freq               [8;1;4]
% 35.68/5.00  --demod_completeness_check              fast
% 35.68/5.00  --demod_use_ground                      true
% 35.68/5.00  --sup_to_prop_solver                    passive
% 35.68/5.00  --sup_prop_simpl_new                    true
% 35.68/5.00  --sup_prop_simpl_given                  true
% 35.68/5.00  --sup_fun_splitting                     true
% 35.68/5.00  --sup_smt_interval                      50000
% 35.68/5.00  
% 35.68/5.00  ------ Superposition Simplification Setup
% 35.68/5.00  
% 35.68/5.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.68/5.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.68/5.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.68/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.68/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.68/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.68/5.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.68/5.00  --sup_immed_triv                        [TrivRules]
% 35.68/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.68/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.68/5.00  --sup_immed_bw_main                     []
% 35.68/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.68/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.68/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.68/5.00  --sup_input_bw                          []
% 35.68/5.00  
% 35.68/5.00  ------ Combination Options
% 35.68/5.00  
% 35.68/5.00  --comb_res_mult                         3
% 35.68/5.00  --comb_sup_mult                         2
% 35.68/5.00  --comb_inst_mult                        10
% 35.68/5.00  
% 35.68/5.00  ------ Debug Options
% 35.68/5.00  
% 35.68/5.00  --dbg_backtrace                         false
% 35.68/5.00  --dbg_dump_prop_clauses                 false
% 35.68/5.00  --dbg_dump_prop_clauses_file            -
% 35.68/5.00  --dbg_out_stat                          false
% 35.68/5.00  ------ Parsing...
% 35.68/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.68/5.00  
% 35.68/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 35.68/5.00  
% 35.68/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.68/5.00  
% 35.68/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.68/5.00  ------ Proving...
% 35.68/5.00  ------ Problem Properties 
% 35.68/5.00  
% 35.68/5.00  
% 35.68/5.00  clauses                                 17
% 35.68/5.00  conjectures                             3
% 35.68/5.00  EPR                                     5
% 35.68/5.00  Horn                                    14
% 35.68/5.00  unary                                   7
% 35.68/5.00  binary                                  8
% 35.68/5.00  lits                                    29
% 35.68/5.00  lits eq                                 5
% 35.68/5.00  fd_pure                                 0
% 35.68/5.00  fd_pseudo                               0
% 35.68/5.00  fd_cond                                 0
% 35.68/5.00  fd_pseudo_cond                          0
% 35.68/5.00  AC symbols                              1
% 35.68/5.00  
% 35.68/5.00  ------ Schedule dynamic 5 is on 
% 35.68/5.00  
% 35.68/5.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.68/5.00  
% 35.68/5.00  
% 35.68/5.00  ------ 
% 35.68/5.00  Current options:
% 35.68/5.00  ------ 
% 35.68/5.00  
% 35.68/5.00  ------ Input Options
% 35.68/5.00  
% 35.68/5.00  --out_options                           all
% 35.68/5.00  --tptp_safe_out                         true
% 35.68/5.00  --problem_path                          ""
% 35.68/5.00  --include_path                          ""
% 35.68/5.00  --clausifier                            res/vclausify_rel
% 35.68/5.00  --clausifier_options                    ""
% 35.68/5.00  --stdin                                 false
% 35.68/5.00  --stats_out                             all
% 35.68/5.00  
% 35.68/5.00  ------ General Options
% 35.68/5.00  
% 35.68/5.00  --fof                                   false
% 35.68/5.00  --time_out_real                         305.
% 35.68/5.00  --time_out_virtual                      -1.
% 35.68/5.00  --symbol_type_check                     false
% 35.68/5.00  --clausify_out                          false
% 35.68/5.00  --sig_cnt_out                           false
% 35.68/5.00  --trig_cnt_out                          false
% 35.68/5.00  --trig_cnt_out_tolerance                1.
% 35.68/5.00  --trig_cnt_out_sk_spl                   false
% 35.68/5.00  --abstr_cl_out                          false
% 35.68/5.00  
% 35.68/5.00  ------ Global Options
% 35.68/5.00  
% 35.68/5.00  --schedule                              default
% 35.68/5.00  --add_important_lit                     false
% 35.68/5.00  --prop_solver_per_cl                    1000
% 35.68/5.00  --min_unsat_core                        false
% 35.68/5.00  --soft_assumptions                      false
% 35.68/5.00  --soft_lemma_size                       3
% 35.68/5.00  --prop_impl_unit_size                   0
% 35.68/5.00  --prop_impl_unit                        []
% 35.68/5.00  --share_sel_clauses                     true
% 35.68/5.00  --reset_solvers                         false
% 35.68/5.00  --bc_imp_inh                            [conj_cone]
% 35.68/5.00  --conj_cone_tolerance                   3.
% 35.68/5.00  --extra_neg_conj                        none
% 35.68/5.00  --large_theory_mode                     true
% 35.68/5.00  --prolific_symb_bound                   200
% 35.68/5.00  --lt_threshold                          2000
% 35.68/5.00  --clause_weak_htbl                      true
% 35.68/5.00  --gc_record_bc_elim                     false
% 35.68/5.00  
% 35.68/5.00  ------ Preprocessing Options
% 35.68/5.00  
% 35.68/5.00  --preprocessing_flag                    true
% 35.68/5.00  --time_out_prep_mult                    0.1
% 35.68/5.00  --splitting_mode                        input
% 35.68/5.00  --splitting_grd                         true
% 35.68/5.00  --splitting_cvd                         false
% 35.68/5.00  --splitting_cvd_svl                     false
% 35.68/5.00  --splitting_nvd                         32
% 35.68/5.00  --sub_typing                            true
% 35.68/5.00  --prep_gs_sim                           true
% 35.68/5.00  --prep_unflatten                        true
% 35.68/5.00  --prep_res_sim                          true
% 35.68/5.00  --prep_upred                            true
% 35.68/5.00  --prep_sem_filter                       exhaustive
% 35.68/5.00  --prep_sem_filter_out                   false
% 35.68/5.00  --pred_elim                             true
% 35.68/5.00  --res_sim_input                         true
% 35.68/5.00  --eq_ax_congr_red                       true
% 35.68/5.00  --pure_diseq_elim                       true
% 35.68/5.00  --brand_transform                       false
% 35.68/5.00  --non_eq_to_eq                          false
% 35.68/5.00  --prep_def_merge                        true
% 35.68/5.00  --prep_def_merge_prop_impl              false
% 35.68/5.00  --prep_def_merge_mbd                    true
% 35.68/5.00  --prep_def_merge_tr_red                 false
% 35.68/5.00  --prep_def_merge_tr_cl                  false
% 35.68/5.00  --smt_preprocessing                     true
% 35.68/5.00  --smt_ac_axioms                         fast
% 35.68/5.00  --preprocessed_out                      false
% 35.68/5.00  --preprocessed_stats                    false
% 35.68/5.00  
% 35.68/5.00  ------ Abstraction refinement Options
% 35.68/5.00  
% 35.68/5.00  --abstr_ref                             []
% 35.68/5.00  --abstr_ref_prep                        false
% 35.68/5.00  --abstr_ref_until_sat                   false
% 35.68/5.00  --abstr_ref_sig_restrict                funpre
% 35.68/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.68/5.00  --abstr_ref_under                       []
% 35.68/5.00  
% 35.68/5.00  ------ SAT Options
% 35.68/5.00  
% 35.68/5.00  --sat_mode                              false
% 35.68/5.00  --sat_fm_restart_options                ""
% 35.68/5.00  --sat_gr_def                            false
% 35.68/5.00  --sat_epr_types                         true
% 35.68/5.00  --sat_non_cyclic_types                  false
% 35.68/5.00  --sat_finite_models                     false
% 35.68/5.00  --sat_fm_lemmas                         false
% 35.68/5.00  --sat_fm_prep                           false
% 35.68/5.00  --sat_fm_uc_incr                        true
% 35.68/5.00  --sat_out_model                         small
% 35.68/5.00  --sat_out_clauses                       false
% 35.68/5.00  
% 35.68/5.00  ------ QBF Options
% 35.68/5.00  
% 35.68/5.00  --qbf_mode                              false
% 35.68/5.00  --qbf_elim_univ                         false
% 35.68/5.00  --qbf_dom_inst                          none
% 35.68/5.00  --qbf_dom_pre_inst                      false
% 35.68/5.00  --qbf_sk_in                             false
% 35.68/5.00  --qbf_pred_elim                         true
% 35.68/5.00  --qbf_split                             512
% 35.68/5.00  
% 35.68/5.00  ------ BMC1 Options
% 35.68/5.00  
% 35.68/5.00  --bmc1_incremental                      false
% 35.68/5.00  --bmc1_axioms                           reachable_all
% 35.68/5.00  --bmc1_min_bound                        0
% 35.68/5.00  --bmc1_max_bound                        -1
% 35.68/5.00  --bmc1_max_bound_default                -1
% 35.68/5.00  --bmc1_symbol_reachability              true
% 35.68/5.00  --bmc1_property_lemmas                  false
% 35.68/5.00  --bmc1_k_induction                      false
% 35.68/5.00  --bmc1_non_equiv_states                 false
% 35.68/5.00  --bmc1_deadlock                         false
% 35.68/5.00  --bmc1_ucm                              false
% 35.68/5.00  --bmc1_add_unsat_core                   none
% 35.68/5.00  --bmc1_unsat_core_children              false
% 35.68/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.68/5.00  --bmc1_out_stat                         full
% 35.68/5.00  --bmc1_ground_init                      false
% 35.68/5.00  --bmc1_pre_inst_next_state              false
% 35.68/5.00  --bmc1_pre_inst_state                   false
% 35.68/5.00  --bmc1_pre_inst_reach_state             false
% 35.68/5.00  --bmc1_out_unsat_core                   false
% 35.68/5.00  --bmc1_aig_witness_out                  false
% 35.68/5.00  --bmc1_verbose                          false
% 35.68/5.00  --bmc1_dump_clauses_tptp                false
% 35.68/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.68/5.00  --bmc1_dump_file                        -
% 35.68/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.68/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.68/5.00  --bmc1_ucm_extend_mode                  1
% 35.68/5.00  --bmc1_ucm_init_mode                    2
% 35.68/5.00  --bmc1_ucm_cone_mode                    none
% 35.68/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.68/5.00  --bmc1_ucm_relax_model                  4
% 35.68/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.68/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.68/5.00  --bmc1_ucm_layered_model                none
% 35.68/5.00  --bmc1_ucm_max_lemma_size               10
% 35.68/5.00  
% 35.68/5.00  ------ AIG Options
% 35.68/5.00  
% 35.68/5.00  --aig_mode                              false
% 35.68/5.00  
% 35.68/5.00  ------ Instantiation Options
% 35.68/5.00  
% 35.68/5.00  --instantiation_flag                    true
% 35.68/5.00  --inst_sos_flag                         true
% 35.68/5.00  --inst_sos_phase                        true
% 35.68/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.68/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.68/5.00  --inst_lit_sel_side                     none
% 35.68/5.00  --inst_solver_per_active                1400
% 35.68/5.00  --inst_solver_calls_frac                1.
% 35.68/5.00  --inst_passive_queue_type               priority_queues
% 35.68/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.68/5.00  --inst_passive_queues_freq              [25;2]
% 35.68/5.00  --inst_dismatching                      true
% 35.68/5.00  --inst_eager_unprocessed_to_passive     true
% 35.68/5.00  --inst_prop_sim_given                   true
% 35.68/5.00  --inst_prop_sim_new                     false
% 35.68/5.00  --inst_subs_new                         false
% 35.68/5.00  --inst_eq_res_simp                      false
% 35.68/5.00  --inst_subs_given                       false
% 35.68/5.00  --inst_orphan_elimination               true
% 35.68/5.00  --inst_learning_loop_flag               true
% 35.68/5.00  --inst_learning_start                   3000
% 35.68/5.00  --inst_learning_factor                  2
% 35.68/5.00  --inst_start_prop_sim_after_learn       3
% 35.68/5.00  --inst_sel_renew                        solver
% 35.68/5.00  --inst_lit_activity_flag                true
% 35.68/5.00  --inst_restr_to_given                   false
% 35.68/5.00  --inst_activity_threshold               500
% 35.68/5.00  --inst_out_proof                        true
% 35.68/5.00  
% 35.68/5.00  ------ Resolution Options
% 35.68/5.00  
% 35.68/5.00  --resolution_flag                       false
% 35.68/5.00  --res_lit_sel                           adaptive
% 35.68/5.00  --res_lit_sel_side                      none
% 35.68/5.00  --res_ordering                          kbo
% 35.68/5.00  --res_to_prop_solver                    active
% 35.68/5.00  --res_prop_simpl_new                    false
% 35.68/5.00  --res_prop_simpl_given                  true
% 35.68/5.00  --res_passive_queue_type                priority_queues
% 35.68/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.68/5.00  --res_passive_queues_freq               [15;5]
% 35.68/5.00  --res_forward_subs                      full
% 35.68/5.00  --res_backward_subs                     full
% 35.68/5.00  --res_forward_subs_resolution           true
% 35.68/5.00  --res_backward_subs_resolution          true
% 35.68/5.00  --res_orphan_elimination                true
% 35.68/5.00  --res_time_limit                        2.
% 35.68/5.00  --res_out_proof                         true
% 35.68/5.00  
% 35.68/5.00  ------ Superposition Options
% 35.68/5.00  
% 35.68/5.00  --superposition_flag                    true
% 35.68/5.00  --sup_passive_queue_type                priority_queues
% 35.68/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.68/5.00  --sup_passive_queues_freq               [8;1;4]
% 35.68/5.00  --demod_completeness_check              fast
% 35.68/5.00  --demod_use_ground                      true
% 35.68/5.00  --sup_to_prop_solver                    passive
% 35.68/5.00  --sup_prop_simpl_new                    true
% 35.68/5.00  --sup_prop_simpl_given                  true
% 35.68/5.00  --sup_fun_splitting                     true
% 35.68/5.00  --sup_smt_interval                      50000
% 35.68/5.00  
% 35.68/5.00  ------ Superposition Simplification Setup
% 35.68/5.00  
% 35.68/5.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.68/5.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.68/5.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.68/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.68/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.68/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.68/5.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.68/5.00  --sup_immed_triv                        [TrivRules]
% 35.68/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.68/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.68/5.00  --sup_immed_bw_main                     []
% 35.68/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.68/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.68/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.68/5.00  --sup_input_bw                          []
% 35.68/5.00  
% 35.68/5.00  ------ Combination Options
% 35.68/5.00  
% 35.68/5.00  --comb_res_mult                         3
% 35.68/5.00  --comb_sup_mult                         2
% 35.68/5.00  --comb_inst_mult                        10
% 35.68/5.00  
% 35.68/5.00  ------ Debug Options
% 35.68/5.00  
% 35.68/5.00  --dbg_backtrace                         false
% 35.68/5.00  --dbg_dump_prop_clauses                 false
% 35.68/5.00  --dbg_dump_prop_clauses_file            -
% 35.68/5.00  --dbg_out_stat                          false
% 35.68/5.00  
% 35.68/5.00  
% 35.68/5.00  
% 35.68/5.00  
% 35.68/5.00  ------ Proving...
% 35.68/5.00  
% 35.68/5.00  
% 35.68/5.00  % SZS status Theorem for theBenchmark.p
% 35.68/5.00  
% 35.68/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.68/5.00  
% 35.68/5.00  fof(f14,conjecture,(
% 35.68/5.00    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 35.68/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.68/5.00  
% 35.68/5.00  fof(f15,negated_conjecture,(
% 35.68/5.00    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 35.68/5.00    inference(negated_conjecture,[],[f14])).
% 35.68/5.00  
% 35.68/5.00  fof(f22,plain,(
% 35.68/5.00    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 35.68/5.00    inference(ennf_transformation,[],[f15])).
% 35.68/5.00  
% 35.68/5.00  fof(f23,plain,(
% 35.68/5.00    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 35.68/5.00    inference(flattening,[],[f22])).
% 35.68/5.00  
% 35.68/5.00  fof(f27,plain,(
% 35.68/5.00    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)))),
% 35.68/5.00    introduced(choice_axiom,[])).
% 35.68/5.00  
% 35.68/5.00  fof(f28,plain,(
% 35.68/5.00    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 35.68/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f27])).
% 35.68/5.00  
% 35.68/5.00  fof(f49,plain,(
% 35.68/5.00    r1_xboole_0(sK3,sK2)),
% 35.68/5.00    inference(cnf_transformation,[],[f28])).
% 35.68/5.00  
% 35.68/5.00  fof(f3,axiom,(
% 35.68/5.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 35.68/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.68/5.00  
% 35.68/5.00  fof(f17,plain,(
% 35.68/5.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 35.68/5.00    inference(ennf_transformation,[],[f3])).
% 35.68/5.00  
% 35.68/5.00  fof(f32,plain,(
% 35.68/5.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 35.68/5.00    inference(cnf_transformation,[],[f17])).
% 35.68/5.00  
% 35.68/5.00  fof(f12,axiom,(
% 35.68/5.00    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 35.68/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.68/5.00  
% 35.68/5.00  fof(f21,plain,(
% 35.68/5.00    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 35.68/5.00    inference(ennf_transformation,[],[f12])).
% 35.68/5.00  
% 35.68/5.00  fof(f45,plain,(
% 35.68/5.00    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 35.68/5.00    inference(cnf_transformation,[],[f21])).
% 35.68/5.00  
% 35.68/5.00  fof(f9,axiom,(
% 35.68/5.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 35.68/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.68/5.00  
% 35.68/5.00  fof(f42,plain,(
% 35.68/5.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 35.68/5.00    inference(cnf_transformation,[],[f9])).
% 35.68/5.00  
% 35.68/5.00  fof(f10,axiom,(
% 35.68/5.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 35.68/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.68/5.00  
% 35.68/5.00  fof(f43,plain,(
% 35.68/5.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 35.68/5.00    inference(cnf_transformation,[],[f10])).
% 35.68/5.00  
% 35.68/5.00  fof(f11,axiom,(
% 35.68/5.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.68/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.68/5.00  
% 35.68/5.00  fof(f44,plain,(
% 35.68/5.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.68/5.00    inference(cnf_transformation,[],[f11])).
% 35.68/5.00  
% 35.68/5.00  fof(f51,plain,(
% 35.68/5.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 35.68/5.00    inference(definition_unfolding,[],[f43,f44])).
% 35.68/5.00  
% 35.68/5.00  fof(f53,plain,(
% 35.68/5.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 35.68/5.00    inference(definition_unfolding,[],[f42,f51])).
% 35.68/5.01  
% 35.68/5.01  fof(f57,plain,(
% 35.68/5.01    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 35.68/5.01    inference(definition_unfolding,[],[f45,f53])).
% 35.68/5.01  
% 35.68/5.01  fof(f2,axiom,(
% 35.68/5.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 35.68/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.68/5.01  
% 35.68/5.01  fof(f24,plain,(
% 35.68/5.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 35.68/5.01    inference(nnf_transformation,[],[f2])).
% 35.68/5.01  
% 35.68/5.01  fof(f30,plain,(
% 35.68/5.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 35.68/5.01    inference(cnf_transformation,[],[f24])).
% 35.68/5.01  
% 35.68/5.01  fof(f48,plain,(
% 35.68/5.01    r2_hidden(sK4,sK3)),
% 35.68/5.01    inference(cnf_transformation,[],[f28])).
% 35.68/5.01  
% 35.68/5.01  fof(f4,axiom,(
% 35.68/5.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 35.68/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.68/5.01  
% 35.68/5.01  fof(f16,plain,(
% 35.68/5.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 35.68/5.01    inference(rectify,[],[f4])).
% 35.68/5.01  
% 35.68/5.01  fof(f18,plain,(
% 35.68/5.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 35.68/5.01    inference(ennf_transformation,[],[f16])).
% 35.68/5.01  
% 35.68/5.01  fof(f25,plain,(
% 35.68/5.01    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 35.68/5.01    introduced(choice_axiom,[])).
% 35.68/5.01  
% 35.68/5.01  fof(f26,plain,(
% 35.68/5.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 35.68/5.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f25])).
% 35.68/5.01  
% 35.68/5.01  fof(f35,plain,(
% 35.68/5.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 35.68/5.01    inference(cnf_transformation,[],[f26])).
% 35.68/5.01  
% 35.68/5.01  fof(f1,axiom,(
% 35.68/5.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.68/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.68/5.01  
% 35.68/5.01  fof(f29,plain,(
% 35.68/5.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.68/5.01    inference(cnf_transformation,[],[f1])).
% 35.68/5.01  
% 35.68/5.01  fof(f6,axiom,(
% 35.68/5.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.68/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.68/5.01  
% 35.68/5.01  fof(f19,plain,(
% 35.68/5.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.68/5.01    inference(ennf_transformation,[],[f6])).
% 35.68/5.01  
% 35.68/5.01  fof(f37,plain,(
% 35.68/5.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.68/5.01    inference(cnf_transformation,[],[f19])).
% 35.68/5.01  
% 35.68/5.01  fof(f47,plain,(
% 35.68/5.01    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 35.68/5.01    inference(cnf_transformation,[],[f28])).
% 35.68/5.01  
% 35.68/5.01  fof(f59,plain,(
% 35.68/5.01    r1_tarski(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4))),
% 35.68/5.01    inference(definition_unfolding,[],[f47,f53])).
% 35.68/5.01  
% 35.68/5.01  fof(f5,axiom,(
% 35.68/5.01    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 35.68/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.68/5.01  
% 35.68/5.01  fof(f36,plain,(
% 35.68/5.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 35.68/5.01    inference(cnf_transformation,[],[f5])).
% 35.68/5.01  
% 35.68/5.01  fof(f7,axiom,(
% 35.68/5.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 35.68/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.68/5.01  
% 35.68/5.01  fof(f38,plain,(
% 35.68/5.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 35.68/5.01    inference(cnf_transformation,[],[f7])).
% 35.68/5.01  
% 35.68/5.01  fof(f31,plain,(
% 35.68/5.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 35.68/5.01    inference(cnf_transformation,[],[f24])).
% 35.68/5.01  
% 35.68/5.01  fof(f8,axiom,(
% 35.68/5.01    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 35.68/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.68/5.01  
% 35.68/5.01  fof(f20,plain,(
% 35.68/5.01    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 35.68/5.01    inference(ennf_transformation,[],[f8])).
% 35.68/5.01  
% 35.68/5.01  fof(f39,plain,(
% 35.68/5.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 35.68/5.01    inference(cnf_transformation,[],[f20])).
% 35.68/5.01  
% 35.68/5.01  fof(f13,axiom,(
% 35.68/5.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 35.68/5.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.68/5.01  
% 35.68/5.01  fof(f46,plain,(
% 35.68/5.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 35.68/5.01    inference(cnf_transformation,[],[f13])).
% 35.68/5.01  
% 35.68/5.01  fof(f52,plain,(
% 35.68/5.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 35.68/5.01    inference(definition_unfolding,[],[f46,f51])).
% 35.68/5.01  
% 35.68/5.01  fof(f56,plain,(
% 35.68/5.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 35.68/5.01    inference(definition_unfolding,[],[f39,f52])).
% 35.68/5.01  
% 35.68/5.01  fof(f50,plain,(
% 35.68/5.01    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 35.68/5.01    inference(cnf_transformation,[],[f28])).
% 35.68/5.01  
% 35.68/5.01  fof(f58,plain,(
% 35.68/5.01    ~r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2)),
% 35.68/5.01    inference(definition_unfolding,[],[f50,f52])).
% 35.68/5.01  
% 35.68/5.01  cnf(c_15,negated_conjecture,
% 35.68/5.01      ( r1_xboole_0(sK3,sK2) ),
% 35.68/5.01      inference(cnf_transformation,[],[f49]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_678,plain,
% 35.68/5.01      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 35.68/5.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_3,plain,
% 35.68/5.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 35.68/5.01      inference(cnf_transformation,[],[f32]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_688,plain,
% 35.68/5.01      ( r1_xboole_0(X0,X1) != iProver_top
% 35.68/5.01      | r1_xboole_0(X1,X0) = iProver_top ),
% 35.68/5.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_1714,plain,
% 35.68/5.01      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_678,c_688]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_13,plain,
% 35.68/5.01      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 35.68/5.01      inference(cnf_transformation,[],[f57]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_680,plain,
% 35.68/5.01      ( r2_hidden(X0,X1) = iProver_top
% 35.68/5.01      | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
% 35.68/5.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_2,plain,
% 35.68/5.01      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 35.68/5.01      inference(cnf_transformation,[],[f30]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_689,plain,
% 35.68/5.01      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 35.68/5.01      | r1_xboole_0(X0,X1) != iProver_top ),
% 35.68/5.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_2560,plain,
% 35.68/5.01      ( k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k1_xboole_0
% 35.68/5.01      | r2_hidden(X0,X1) = iProver_top ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_680,c_689]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_16,negated_conjecture,
% 35.68/5.01      ( r2_hidden(sK4,sK3) ),
% 35.68/5.01      inference(cnf_transformation,[],[f48]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_677,plain,
% 35.68/5.01      ( r2_hidden(sK4,sK3) = iProver_top ),
% 35.68/5.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_4,plain,
% 35.68/5.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 35.68/5.01      inference(cnf_transformation,[],[f35]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_687,plain,
% 35.68/5.01      ( r2_hidden(X0,X1) != iProver_top
% 35.68/5.01      | r2_hidden(X0,X2) != iProver_top
% 35.68/5.01      | r1_xboole_0(X2,X1) != iProver_top ),
% 35.68/5.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_4314,plain,
% 35.68/5.01      ( r2_hidden(sK4,X0) != iProver_top
% 35.68/5.01      | r1_xboole_0(X0,sK3) != iProver_top ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_677,c_687]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_130040,plain,
% 35.68/5.01      ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0) = k1_xboole_0
% 35.68/5.01      | r1_xboole_0(X0,sK3) != iProver_top ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_2560,c_4314]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_133259,plain,
% 35.68/5.01      ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2) = k1_xboole_0 ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_1714,c_130040]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_0,plain,
% 35.68/5.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 35.68/5.01      inference(cnf_transformation,[],[f29]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_133309,plain,
% 35.68/5.01      ( k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_133259,c_0]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_8,plain,
% 35.68/5.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 35.68/5.01      inference(cnf_transformation,[],[f37]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_17,negated_conjecture,
% 35.68/5.01      ( r1_tarski(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 35.68/5.01      inference(cnf_transformation,[],[f59]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_215,plain,
% 35.68/5.01      ( k2_enumset1(sK4,sK4,sK4,sK4) != X0
% 35.68/5.01      | k3_xboole_0(X1,X0) = X1
% 35.68/5.01      | k3_xboole_0(sK1,sK2) != X1 ),
% 35.68/5.01      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_216,plain,
% 35.68/5.01      ( k3_xboole_0(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(sK1,sK2) ),
% 35.68/5.01      inference(unflattening,[status(thm)],[c_215]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_7,plain,
% 35.68/5.01      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 35.68/5.01      inference(cnf_transformation,[],[f36]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_350,plain,
% 35.68/5.01      ( k3_xboole_0(sK1,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_xboole_0(sK1,sK2) ),
% 35.68/5.01      inference(theory_normalisation,[status(thm)],[c_216,c_7,c_0]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_136174,plain,
% 35.68/5.01      ( k3_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK1,sK2) ),
% 35.68/5.01      inference(demodulation,[status(thm)],[c_133309,c_350]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_2561,plain,
% 35.68/5.01      ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_678,c_689]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_2997,plain,
% 35.68/5.01      ( k3_xboole_0(sK3,k3_xboole_0(sK2,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_2561,c_7]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_707,plain,
% 35.68/5.01      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_2999,plain,
% 35.68/5.01      ( k3_xboole_0(sK3,k3_xboole_0(sK2,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_2561,c_707]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_9,plain,
% 35.68/5.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 35.68/5.01      inference(cnf_transformation,[],[f38]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_684,plain,
% 35.68/5.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 35.68/5.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_2558,plain,
% 35.68/5.01      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_684,c_689]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_3007,plain,
% 35.68/5.01      ( k3_xboole_0(sK3,k3_xboole_0(sK2,X0)) = k1_xboole_0 ),
% 35.68/5.01      inference(light_normalisation,[status(thm)],[c_2999,c_2558]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_3008,plain,
% 35.68/5.01      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 35.68/5.01      inference(demodulation,[status(thm)],[c_2997,c_3007]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_705,plain,
% 35.68/5.01      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_1493,plain,
% 35.68/5.01      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_350,c_705]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_3217,plain,
% 35.68/5.01      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,k1_xboole_0) ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_3008,c_1493]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_3221,plain,
% 35.68/5.01      ( k3_xboole_0(sK1,k1_xboole_0) = k1_xboole_0 ),
% 35.68/5.01      inference(demodulation,[status(thm)],[c_3217,c_3008]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_136175,plain,
% 35.68/5.01      ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 35.68/5.01      inference(light_normalisation,[status(thm)],[c_136174,c_3221]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_1,plain,
% 35.68/5.01      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 35.68/5.01      inference(cnf_transformation,[],[f31]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_1546,plain,
% 35.68/5.01      ( r1_xboole_0(X0,sK2) | k3_xboole_0(X0,sK2) != k1_xboole_0 ),
% 35.68/5.01      inference(instantiation,[status(thm)],[c_1]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_75672,plain,
% 35.68/5.01      ( r1_xboole_0(sK1,sK2) | k3_xboole_0(sK1,sK2) != k1_xboole_0 ),
% 35.68/5.01      inference(instantiation,[status(thm)],[c_1546]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_1309,plain,
% 35.68/5.01      ( r1_xboole_0(sK2,sK1) | ~ r1_xboole_0(sK1,sK2) ),
% 35.68/5.01      inference(instantiation,[status(thm)],[c_3]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_852,plain,
% 35.68/5.01      ( r1_xboole_0(X0,sK3) | ~ r1_xboole_0(sK3,X0) ),
% 35.68/5.01      inference(instantiation,[status(thm)],[c_3]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_1069,plain,
% 35.68/5.01      ( r1_xboole_0(sK2,sK3) | ~ r1_xboole_0(sK3,sK2) ),
% 35.68/5.01      inference(instantiation,[status(thm)],[c_852]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_12,plain,
% 35.68/5.01      ( ~ r1_xboole_0(X0,X1)
% 35.68/5.01      | ~ r1_xboole_0(X0,X2)
% 35.68/5.01      | r1_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
% 35.68/5.01      inference(cnf_transformation,[],[f56]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_771,plain,
% 35.68/5.01      ( r1_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)))
% 35.68/5.01      | ~ r1_xboole_0(sK2,sK3)
% 35.68/5.01      | ~ r1_xboole_0(sK2,sK1) ),
% 35.68/5.01      inference(instantiation,[status(thm)],[c_12]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_725,plain,
% 35.68/5.01      ( r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2)
% 35.68/5.01      | ~ r1_xboole_0(sK2,k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3))) ),
% 35.68/5.01      inference(instantiation,[status(thm)],[c_3]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_14,negated_conjecture,
% 35.68/5.01      ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK3)),sK2) ),
% 35.68/5.01      inference(cnf_transformation,[],[f58]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(contradiction,plain,
% 35.68/5.01      ( $false ),
% 35.68/5.01      inference(minisat,
% 35.68/5.01                [status(thm)],
% 35.68/5.01                [c_136175,c_75672,c_1309,c_1069,c_771,c_725,c_14,c_15]) ).
% 35.68/5.01  
% 35.68/5.01  
% 35.68/5.01  % SZS output end CNFRefutation for theBenchmark.p
% 35.68/5.01  
% 35.68/5.01  ------                               Statistics
% 35.68/5.01  
% 35.68/5.01  ------ General
% 35.68/5.01  
% 35.68/5.01  abstr_ref_over_cycles:                  0
% 35.68/5.01  abstr_ref_under_cycles:                 0
% 35.68/5.01  gc_basic_clause_elim:                   0
% 35.68/5.01  forced_gc_time:                         0
% 35.68/5.01  parsing_time:                           0.013
% 35.68/5.01  unif_index_cands_time:                  0.
% 35.68/5.01  unif_index_add_time:                    0.
% 35.68/5.01  orderings_time:                         0.
% 35.68/5.01  out_proof_time:                         0.013
% 35.68/5.01  total_time:                             4.37
% 35.68/5.01  num_of_symbols:                         43
% 35.68/5.01  num_of_terms:                           143330
% 35.68/5.01  
% 35.68/5.01  ------ Preprocessing
% 35.68/5.01  
% 35.68/5.01  num_of_splits:                          0
% 35.68/5.01  num_of_split_atoms:                     0
% 35.68/5.01  num_of_reused_defs:                     0
% 35.68/5.01  num_eq_ax_congr_red:                    6
% 35.68/5.01  num_of_sem_filtered_clauses:            1
% 35.68/5.01  num_of_subtypes:                        1
% 35.68/5.01  monotx_restored_types:                  0
% 35.68/5.01  sat_num_of_epr_types:                   0
% 35.68/5.01  sat_num_of_non_cyclic_types:            0
% 35.68/5.01  sat_guarded_non_collapsed_types:        0
% 35.68/5.01  num_pure_diseq_elim:                    0
% 35.68/5.01  simp_replaced_by:                       0
% 35.68/5.01  res_preprocessed:                       84
% 35.68/5.01  prep_upred:                             0
% 35.68/5.01  prep_unflattend:                        2
% 35.68/5.01  smt_new_axioms:                         0
% 35.68/5.01  pred_elim_cands:                        2
% 35.68/5.01  pred_elim:                              1
% 35.68/5.01  pred_elim_cl:                           1
% 35.68/5.01  pred_elim_cycles:                       3
% 35.68/5.01  merged_defs:                            8
% 35.68/5.01  merged_defs_ncl:                        0
% 35.68/5.01  bin_hyper_res:                          8
% 35.68/5.01  prep_cycles:                            4
% 35.68/5.01  pred_elim_time:                         0.
% 35.68/5.01  splitting_time:                         0.
% 35.68/5.01  sem_filter_time:                        0.
% 35.68/5.01  monotx_time:                            0.
% 35.68/5.01  subtype_inf_time:                       0.
% 35.68/5.01  
% 35.68/5.01  ------ Problem properties
% 35.68/5.01  
% 35.68/5.01  clauses:                                17
% 35.68/5.01  conjectures:                            3
% 35.68/5.01  epr:                                    5
% 35.68/5.01  horn:                                   14
% 35.68/5.01  ground:                                 4
% 35.68/5.01  unary:                                  7
% 35.68/5.01  binary:                                 8
% 35.68/5.01  lits:                                   29
% 35.68/5.01  lits_eq:                                5
% 35.68/5.01  fd_pure:                                0
% 35.68/5.01  fd_pseudo:                              0
% 35.68/5.01  fd_cond:                                0
% 35.68/5.01  fd_pseudo_cond:                         0
% 35.68/5.01  ac_symbols:                             1
% 35.68/5.01  
% 35.68/5.01  ------ Propositional Solver
% 35.68/5.01  
% 35.68/5.01  prop_solver_calls:                      52
% 35.68/5.01  prop_fast_solver_calls:                 1031
% 35.68/5.01  smt_solver_calls:                       0
% 35.68/5.01  smt_fast_solver_calls:                  0
% 35.68/5.01  prop_num_of_clauses:                    51348
% 35.68/5.01  prop_preprocess_simplified:             41202
% 35.68/5.01  prop_fo_subsumed:                       2
% 35.68/5.01  prop_solver_time:                       0.
% 35.68/5.01  smt_solver_time:                        0.
% 35.68/5.01  smt_fast_solver_time:                   0.
% 35.68/5.01  prop_fast_solver_time:                  0.
% 35.68/5.01  prop_unsat_core_time:                   0.005
% 35.68/5.01  
% 35.68/5.01  ------ QBF
% 35.68/5.01  
% 35.68/5.01  qbf_q_res:                              0
% 35.68/5.01  qbf_num_tautologies:                    0
% 35.68/5.01  qbf_prep_cycles:                        0
% 35.68/5.01  
% 35.68/5.01  ------ BMC1
% 35.68/5.01  
% 35.68/5.01  bmc1_current_bound:                     -1
% 35.68/5.01  bmc1_last_solved_bound:                 -1
% 35.68/5.01  bmc1_unsat_core_size:                   -1
% 35.68/5.01  bmc1_unsat_core_parents_size:           -1
% 35.68/5.01  bmc1_merge_next_fun:                    0
% 35.68/5.01  bmc1_unsat_core_clauses_time:           0.
% 35.68/5.01  
% 35.68/5.01  ------ Instantiation
% 35.68/5.01  
% 35.68/5.01  inst_num_of_clauses:                    6741
% 35.68/5.01  inst_num_in_passive:                    1969
% 35.68/5.01  inst_num_in_active:                     1570
% 35.68/5.01  inst_num_in_unprocessed:                3205
% 35.68/5.01  inst_num_of_loops:                      2170
% 35.68/5.01  inst_num_of_learning_restarts:          0
% 35.68/5.01  inst_num_moves_active_passive:          599
% 35.68/5.01  inst_lit_activity:                      0
% 35.68/5.01  inst_lit_activity_moves:                3
% 35.68/5.01  inst_num_tautologies:                   0
% 35.68/5.01  inst_num_prop_implied:                  0
% 35.68/5.01  inst_num_existing_simplified:           0
% 35.68/5.01  inst_num_eq_res_simplified:             0
% 35.68/5.01  inst_num_child_elim:                    0
% 35.68/5.01  inst_num_of_dismatching_blockings:      10851
% 35.68/5.01  inst_num_of_non_proper_insts:           8329
% 35.68/5.01  inst_num_of_duplicates:                 0
% 35.68/5.01  inst_inst_num_from_inst_to_res:         0
% 35.68/5.01  inst_dismatching_checking_time:         0.
% 35.68/5.01  
% 35.68/5.01  ------ Resolution
% 35.68/5.01  
% 35.68/5.01  res_num_of_clauses:                     0
% 35.68/5.01  res_num_in_passive:                     0
% 35.68/5.01  res_num_in_active:                      0
% 35.68/5.01  res_num_of_loops:                       88
% 35.68/5.01  res_forward_subset_subsumed:            831
% 35.68/5.01  res_backward_subset_subsumed:           10
% 35.68/5.01  res_forward_subsumed:                   0
% 35.68/5.01  res_backward_subsumed:                  0
% 35.68/5.01  res_forward_subsumption_resolution:     0
% 35.68/5.01  res_backward_subsumption_resolution:    0
% 35.68/5.01  res_clause_to_clause_subsumption:       142370
% 35.68/5.01  res_orphan_elimination:                 0
% 35.68/5.01  res_tautology_del:                      118
% 35.68/5.01  res_num_eq_res_simplified:              0
% 35.68/5.01  res_num_sel_changes:                    0
% 35.68/5.01  res_moves_from_active_to_pass:          0
% 35.68/5.01  
% 35.68/5.01  ------ Superposition
% 35.68/5.01  
% 35.68/5.01  sup_time_total:                         0.
% 35.68/5.01  sup_time_generating:                    0.
% 35.68/5.01  sup_time_sim_full:                      0.
% 35.68/5.01  sup_time_sim_immed:                     0.
% 35.68/5.01  
% 35.68/5.01  sup_num_of_clauses:                     8947
% 35.68/5.01  sup_num_in_active:                      264
% 35.68/5.01  sup_num_in_passive:                     8683
% 35.68/5.01  sup_num_of_loops:                       433
% 35.68/5.01  sup_fw_superposition:                   24206
% 35.68/5.01  sup_bw_superposition:                   15277
% 35.68/5.01  sup_immediate_simplified:               21771
% 35.68/5.01  sup_given_eliminated:                   3
% 35.68/5.01  comparisons_done:                       0
% 35.68/5.01  comparisons_avoided:                    0
% 35.68/5.01  
% 35.68/5.01  ------ Simplifications
% 35.68/5.01  
% 35.68/5.01  
% 35.68/5.01  sim_fw_subset_subsumed:                 65
% 35.68/5.01  sim_bw_subset_subsumed:                 5
% 35.68/5.01  sim_fw_subsumed:                        1260
% 35.68/5.01  sim_bw_subsumed:                        119
% 35.68/5.01  sim_fw_subsumption_res:                 0
% 35.68/5.01  sim_bw_subsumption_res:                 0
% 35.68/5.01  sim_tautology_del:                      2
% 35.68/5.01  sim_eq_tautology_del:                   1146
% 35.68/5.01  sim_eq_res_simp:                        689
% 35.68/5.01  sim_fw_demodulated:                     12772
% 35.68/5.01  sim_bw_demodulated:                     395
% 35.68/5.01  sim_light_normalised:                   6909
% 35.68/5.01  sim_joinable_taut:                      7314
% 35.68/5.01  sim_joinable_simp:                      0
% 35.68/5.01  sim_ac_normalised:                      0
% 35.68/5.01  sim_smt_subsumption:                    0
% 35.68/5.01  
%------------------------------------------------------------------------------
