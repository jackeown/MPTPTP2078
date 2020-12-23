%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:57 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 230 expanded)
%              Number of clauses        :   78 ( 105 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  257 ( 425 expanded)
%              Number of equality atoms :  118 ( 204 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f21])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK2,sK3)
      & r1_xboole_0(sK2,sK4)
      & r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ r1_tarski(sK2,sK3)
    & r1_xboole_0(sK2,sK4)
    & r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f30])).

fof(f50,plain,(
    r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f40,f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f51,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_660,plain,
    ( r1_xboole_0(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_667,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6549,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_660,c_667])).

cnf(c_14,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7427,plain,
    ( k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6549,c_14])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7432,plain,
    ( k4_xboole_0(sK2,sK4) = sK2 ),
    inference(demodulation,[status(thm)],[c_7427,c_12])).

cnf(c_13,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7673,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK4,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_7432,c_13])).

cnf(c_8868,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,sK4)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_0,c_7673])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_659,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_663,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1874,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = k2_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_659,c_663])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_682,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10,c_12])).

cnf(c_1005,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_682])).

cnf(c_11,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1007,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1005,c_11])).

cnf(c_1308,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1007])).

cnf(c_2148,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1874,c_1308])).

cnf(c_10216,plain,
    ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8868,c_2148])).

cnf(c_11102,plain,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10216,c_11])).

cnf(c_15,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_662,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_872,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_662])).

cnf(c_11218,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK3,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11102,c_872])).

cnf(c_325,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_770,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,sK3)
    | sK3 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_6687,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(sK3,X1))
    | r1_tarski(sK2,sK3)
    | sK3 != k2_xboole_0(sK3,X1)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_11028,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK3,X0))
    | r1_tarski(sK2,sK3)
    | sK3 != k2_xboole_0(sK3,X0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_6687])).

cnf(c_11029,plain,
    ( sK3 != k2_xboole_0(sK3,X0)
    | sK2 != sK2
    | r1_tarski(sK2,k2_xboole_0(sK3,X0)) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11028])).

cnf(c_11031,plain,
    ( sK3 != k2_xboole_0(sK3,k1_xboole_0)
    | sK2 != sK2
    | r1_tarski(sK2,k2_xboole_0(sK3,k1_xboole_0)) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_11029])).

cnf(c_3447,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4)))
    | X2 != X0
    | k4_xboole_0(X3,k4_xboole_0(X3,X4)) != X1 ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_3449,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3447])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3419,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK0(X2,sK3),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3425,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK0(k1_xboole_0,sK3),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_3419])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2275,plain,
    ( ~ r2_hidden(sK0(X0,sK3),X0)
    | r2_hidden(sK0(X0,sK3),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3418,plain,
    ( ~ r2_hidden(sK0(X0,sK3),X0)
    | r2_hidden(sK0(X0,sK3),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(instantiation,[status(thm)],[c_2275])).

cnf(c_3421,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK3),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
    | ~ r2_hidden(sK0(k1_xboole_0,sK3),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_3418])).

cnf(c_2395,plain,
    ( k2_xboole_0(sK3,X0) = k2_xboole_0(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2397,plain,
    ( k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_2395])).

cnf(c_323,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_794,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_1797,plain,
    ( X0 != k2_xboole_0(X1,sK3)
    | sK3 = X0
    | sK3 != k2_xboole_0(X1,sK3) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_2394,plain,
    ( k2_xboole_0(sK3,X0) != k2_xboole_0(X0,sK3)
    | sK3 != k2_xboole_0(X0,sK3)
    | sK3 = k2_xboole_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1797])).

cnf(c_2396,plain,
    ( k2_xboole_0(sK3,k1_xboole_0) != k2_xboole_0(k1_xboole_0,sK3)
    | sK3 = k2_xboole_0(sK3,k1_xboole_0)
    | sK3 != k2_xboole_0(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_2394])).

cnf(c_999,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_12,c_13])).

cnf(c_1720,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_999,c_682])).

cnf(c_1845,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1720,c_12])).

cnf(c_986,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_682,c_11])).

cnf(c_1129,plain,
    ( r1_tarski(k1_xboole_0,k2_xboole_0(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_986,c_872])).

cnf(c_2009,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1845,c_1129])).

cnf(c_2014,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2009])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1149,plain,
    ( r2_hidden(sK0(X0,sK3),X0)
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1156,plain,
    ( r2_hidden(sK0(k1_xboole_0,sK3),k1_xboole_0)
    | r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_973,plain,
    ( ~ r1_tarski(X0,sK3)
    | k2_xboole_0(X0,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_976,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | k2_xboole_0(k1_xboole_0,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_855,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_972,plain,
    ( k2_xboole_0(X0,sK3) != sK3
    | sK3 = k2_xboole_0(X0,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_974,plain,
    ( k2_xboole_0(k1_xboole_0,sK3) != sK3
    | sK3 = k2_xboole_0(k1_xboole_0,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_322,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_845,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_789,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_334,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_42,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_29,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11218,c_11031,c_3449,c_3425,c_3421,c_2397,c_2396,c_2014,c_1156,c_976,c_974,c_845,c_789,c_334,c_42,c_29,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:15:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.80/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.02  
% 3.80/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.80/1.02  
% 3.80/1.02  ------  iProver source info
% 3.80/1.02  
% 3.80/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.80/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.80/1.02  git: non_committed_changes: false
% 3.80/1.02  git: last_make_outside_of_git: false
% 3.80/1.02  
% 3.80/1.02  ------ 
% 3.80/1.02  
% 3.80/1.02  ------ Input Options
% 3.80/1.02  
% 3.80/1.02  --out_options                           all
% 3.80/1.02  --tptp_safe_out                         true
% 3.80/1.02  --problem_path                          ""
% 3.80/1.02  --include_path                          ""
% 3.80/1.02  --clausifier                            res/vclausify_rel
% 3.80/1.02  --clausifier_options                    --mode clausify
% 3.80/1.02  --stdin                                 false
% 3.80/1.02  --stats_out                             all
% 3.80/1.02  
% 3.80/1.02  ------ General Options
% 3.80/1.02  
% 3.80/1.02  --fof                                   false
% 3.80/1.02  --time_out_real                         305.
% 3.80/1.02  --time_out_virtual                      -1.
% 3.80/1.02  --symbol_type_check                     false
% 3.80/1.02  --clausify_out                          false
% 3.80/1.02  --sig_cnt_out                           false
% 3.80/1.02  --trig_cnt_out                          false
% 3.80/1.02  --trig_cnt_out_tolerance                1.
% 3.80/1.02  --trig_cnt_out_sk_spl                   false
% 3.80/1.02  --abstr_cl_out                          false
% 3.80/1.02  
% 3.80/1.02  ------ Global Options
% 3.80/1.02  
% 3.80/1.02  --schedule                              default
% 3.80/1.02  --add_important_lit                     false
% 3.80/1.02  --prop_solver_per_cl                    1000
% 3.80/1.02  --min_unsat_core                        false
% 3.80/1.02  --soft_assumptions                      false
% 3.80/1.02  --soft_lemma_size                       3
% 3.80/1.02  --prop_impl_unit_size                   0
% 3.80/1.02  --prop_impl_unit                        []
% 3.80/1.02  --share_sel_clauses                     true
% 3.80/1.02  --reset_solvers                         false
% 3.80/1.02  --bc_imp_inh                            [conj_cone]
% 3.80/1.02  --conj_cone_tolerance                   3.
% 3.80/1.02  --extra_neg_conj                        none
% 3.80/1.02  --large_theory_mode                     true
% 3.80/1.02  --prolific_symb_bound                   200
% 3.80/1.02  --lt_threshold                          2000
% 3.80/1.02  --clause_weak_htbl                      true
% 3.80/1.02  --gc_record_bc_elim                     false
% 3.80/1.02  
% 3.80/1.02  ------ Preprocessing Options
% 3.80/1.02  
% 3.80/1.02  --preprocessing_flag                    true
% 3.80/1.02  --time_out_prep_mult                    0.1
% 3.80/1.02  --splitting_mode                        input
% 3.80/1.02  --splitting_grd                         true
% 3.80/1.02  --splitting_cvd                         false
% 3.80/1.02  --splitting_cvd_svl                     false
% 3.80/1.02  --splitting_nvd                         32
% 3.80/1.02  --sub_typing                            true
% 3.80/1.02  --prep_gs_sim                           true
% 3.80/1.02  --prep_unflatten                        true
% 3.80/1.02  --prep_res_sim                          true
% 3.80/1.02  --prep_upred                            true
% 3.80/1.02  --prep_sem_filter                       exhaustive
% 3.80/1.02  --prep_sem_filter_out                   false
% 3.80/1.02  --pred_elim                             true
% 3.80/1.02  --res_sim_input                         true
% 3.80/1.02  --eq_ax_congr_red                       true
% 3.80/1.02  --pure_diseq_elim                       true
% 3.80/1.02  --brand_transform                       false
% 3.80/1.02  --non_eq_to_eq                          false
% 3.80/1.02  --prep_def_merge                        true
% 3.80/1.02  --prep_def_merge_prop_impl              false
% 3.80/1.02  --prep_def_merge_mbd                    true
% 3.80/1.02  --prep_def_merge_tr_red                 false
% 3.80/1.02  --prep_def_merge_tr_cl                  false
% 3.80/1.02  --smt_preprocessing                     true
% 3.80/1.02  --smt_ac_axioms                         fast
% 3.80/1.02  --preprocessed_out                      false
% 3.80/1.02  --preprocessed_stats                    false
% 3.80/1.02  
% 3.80/1.02  ------ Abstraction refinement Options
% 3.80/1.02  
% 3.80/1.02  --abstr_ref                             []
% 3.80/1.02  --abstr_ref_prep                        false
% 3.80/1.02  --abstr_ref_until_sat                   false
% 3.80/1.02  --abstr_ref_sig_restrict                funpre
% 3.80/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/1.02  --abstr_ref_under                       []
% 3.80/1.02  
% 3.80/1.02  ------ SAT Options
% 3.80/1.02  
% 3.80/1.02  --sat_mode                              false
% 3.80/1.02  --sat_fm_restart_options                ""
% 3.80/1.02  --sat_gr_def                            false
% 3.80/1.02  --sat_epr_types                         true
% 3.80/1.02  --sat_non_cyclic_types                  false
% 3.80/1.02  --sat_finite_models                     false
% 3.80/1.02  --sat_fm_lemmas                         false
% 3.80/1.02  --sat_fm_prep                           false
% 3.80/1.02  --sat_fm_uc_incr                        true
% 3.80/1.02  --sat_out_model                         small
% 3.80/1.02  --sat_out_clauses                       false
% 3.80/1.02  
% 3.80/1.02  ------ QBF Options
% 3.80/1.02  
% 3.80/1.02  --qbf_mode                              false
% 3.80/1.02  --qbf_elim_univ                         false
% 3.80/1.02  --qbf_dom_inst                          none
% 3.80/1.02  --qbf_dom_pre_inst                      false
% 3.80/1.02  --qbf_sk_in                             false
% 3.80/1.02  --qbf_pred_elim                         true
% 3.80/1.02  --qbf_split                             512
% 3.80/1.02  
% 3.80/1.02  ------ BMC1 Options
% 3.80/1.02  
% 3.80/1.02  --bmc1_incremental                      false
% 3.80/1.02  --bmc1_axioms                           reachable_all
% 3.80/1.02  --bmc1_min_bound                        0
% 3.80/1.02  --bmc1_max_bound                        -1
% 3.80/1.02  --bmc1_max_bound_default                -1
% 3.80/1.02  --bmc1_symbol_reachability              true
% 3.80/1.02  --bmc1_property_lemmas                  false
% 3.80/1.02  --bmc1_k_induction                      false
% 3.80/1.02  --bmc1_non_equiv_states                 false
% 3.80/1.02  --bmc1_deadlock                         false
% 3.80/1.02  --bmc1_ucm                              false
% 3.80/1.02  --bmc1_add_unsat_core                   none
% 3.80/1.02  --bmc1_unsat_core_children              false
% 3.80/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/1.02  --bmc1_out_stat                         full
% 3.80/1.02  --bmc1_ground_init                      false
% 3.80/1.02  --bmc1_pre_inst_next_state              false
% 3.80/1.02  --bmc1_pre_inst_state                   false
% 3.80/1.02  --bmc1_pre_inst_reach_state             false
% 3.80/1.02  --bmc1_out_unsat_core                   false
% 3.80/1.02  --bmc1_aig_witness_out                  false
% 3.80/1.02  --bmc1_verbose                          false
% 3.80/1.02  --bmc1_dump_clauses_tptp                false
% 3.80/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.80/1.02  --bmc1_dump_file                        -
% 3.80/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.80/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.80/1.02  --bmc1_ucm_extend_mode                  1
% 3.80/1.02  --bmc1_ucm_init_mode                    2
% 3.80/1.02  --bmc1_ucm_cone_mode                    none
% 3.80/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.80/1.02  --bmc1_ucm_relax_model                  4
% 3.80/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.80/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/1.02  --bmc1_ucm_layered_model                none
% 3.80/1.02  --bmc1_ucm_max_lemma_size               10
% 3.80/1.02  
% 3.80/1.02  ------ AIG Options
% 3.80/1.02  
% 3.80/1.02  --aig_mode                              false
% 3.80/1.02  
% 3.80/1.02  ------ Instantiation Options
% 3.80/1.02  
% 3.80/1.02  --instantiation_flag                    true
% 3.80/1.02  --inst_sos_flag                         false
% 3.80/1.02  --inst_sos_phase                        true
% 3.80/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/1.02  --inst_lit_sel_side                     num_symb
% 3.80/1.02  --inst_solver_per_active                1400
% 3.80/1.02  --inst_solver_calls_frac                1.
% 3.80/1.02  --inst_passive_queue_type               priority_queues
% 3.80/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/1.02  --inst_passive_queues_freq              [25;2]
% 3.80/1.02  --inst_dismatching                      true
% 3.80/1.02  --inst_eager_unprocessed_to_passive     true
% 3.80/1.02  --inst_prop_sim_given                   true
% 3.80/1.02  --inst_prop_sim_new                     false
% 3.80/1.02  --inst_subs_new                         false
% 3.80/1.02  --inst_eq_res_simp                      false
% 3.80/1.02  --inst_subs_given                       false
% 3.80/1.02  --inst_orphan_elimination               true
% 3.80/1.02  --inst_learning_loop_flag               true
% 3.80/1.02  --inst_learning_start                   3000
% 3.80/1.02  --inst_learning_factor                  2
% 3.80/1.02  --inst_start_prop_sim_after_learn       3
% 3.80/1.02  --inst_sel_renew                        solver
% 3.80/1.02  --inst_lit_activity_flag                true
% 3.80/1.02  --inst_restr_to_given                   false
% 3.80/1.02  --inst_activity_threshold               500
% 3.80/1.02  --inst_out_proof                        true
% 3.80/1.02  
% 3.80/1.02  ------ Resolution Options
% 3.80/1.02  
% 3.80/1.02  --resolution_flag                       true
% 3.80/1.02  --res_lit_sel                           adaptive
% 3.80/1.02  --res_lit_sel_side                      none
% 3.80/1.02  --res_ordering                          kbo
% 3.80/1.02  --res_to_prop_solver                    active
% 3.80/1.02  --res_prop_simpl_new                    false
% 3.80/1.02  --res_prop_simpl_given                  true
% 3.80/1.02  --res_passive_queue_type                priority_queues
% 3.80/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/1.02  --res_passive_queues_freq               [15;5]
% 3.80/1.02  --res_forward_subs                      full
% 3.80/1.02  --res_backward_subs                     full
% 3.80/1.02  --res_forward_subs_resolution           true
% 3.80/1.02  --res_backward_subs_resolution          true
% 3.80/1.02  --res_orphan_elimination                true
% 3.80/1.02  --res_time_limit                        2.
% 3.80/1.02  --res_out_proof                         true
% 3.80/1.02  
% 3.80/1.02  ------ Superposition Options
% 3.80/1.02  
% 3.80/1.02  --superposition_flag                    true
% 3.80/1.02  --sup_passive_queue_type                priority_queues
% 3.80/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.80/1.02  --demod_completeness_check              fast
% 3.80/1.02  --demod_use_ground                      true
% 3.80/1.02  --sup_to_prop_solver                    passive
% 3.80/1.02  --sup_prop_simpl_new                    true
% 3.80/1.02  --sup_prop_simpl_given                  true
% 3.80/1.02  --sup_fun_splitting                     false
% 3.80/1.02  --sup_smt_interval                      50000
% 3.80/1.02  
% 3.80/1.02  ------ Superposition Simplification Setup
% 3.80/1.02  
% 3.80/1.02  --sup_indices_passive                   []
% 3.80/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.80/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.80/1.02  --sup_full_bw                           [BwDemod]
% 3.80/1.02  --sup_immed_triv                        [TrivRules]
% 3.80/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.80/1.02  --sup_immed_bw_main                     []
% 3.80/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.80/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.80/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.80/1.02  
% 3.80/1.02  ------ Combination Options
% 3.80/1.02  
% 3.80/1.02  --comb_res_mult                         3
% 3.80/1.02  --comb_sup_mult                         2
% 3.80/1.02  --comb_inst_mult                        10
% 3.80/1.02  
% 3.80/1.02  ------ Debug Options
% 3.80/1.02  
% 3.80/1.02  --dbg_backtrace                         false
% 3.80/1.02  --dbg_dump_prop_clauses                 false
% 3.80/1.02  --dbg_dump_prop_clauses_file            -
% 3.80/1.02  --dbg_out_stat                          false
% 3.80/1.02  ------ Parsing...
% 3.80/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.80/1.02  
% 3.80/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.80/1.02  
% 3.80/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.80/1.02  
% 3.80/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.80/1.02  ------ Proving...
% 3.80/1.02  ------ Problem Properties 
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  clauses                                 19
% 3.80/1.02  conjectures                             3
% 3.80/1.02  EPR                                     4
% 3.80/1.02  Horn                                    17
% 3.80/1.02  unary                                   10
% 3.80/1.02  binary                                  8
% 3.80/1.02  lits                                    29
% 3.80/1.02  lits eq                                 9
% 3.80/1.02  fd_pure                                 0
% 3.80/1.02  fd_pseudo                               0
% 3.80/1.02  fd_cond                                 0
% 3.80/1.02  fd_pseudo_cond                          0
% 3.80/1.02  AC symbols                              0
% 3.80/1.02  
% 3.80/1.02  ------ Schedule dynamic 5 is on 
% 3.80/1.02  
% 3.80/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  ------ 
% 3.80/1.02  Current options:
% 3.80/1.02  ------ 
% 3.80/1.02  
% 3.80/1.02  ------ Input Options
% 3.80/1.02  
% 3.80/1.02  --out_options                           all
% 3.80/1.02  --tptp_safe_out                         true
% 3.80/1.02  --problem_path                          ""
% 3.80/1.02  --include_path                          ""
% 3.80/1.02  --clausifier                            res/vclausify_rel
% 3.80/1.02  --clausifier_options                    --mode clausify
% 3.80/1.02  --stdin                                 false
% 3.80/1.02  --stats_out                             all
% 3.80/1.02  
% 3.80/1.02  ------ General Options
% 3.80/1.02  
% 3.80/1.02  --fof                                   false
% 3.80/1.02  --time_out_real                         305.
% 3.80/1.02  --time_out_virtual                      -1.
% 3.80/1.02  --symbol_type_check                     false
% 3.80/1.02  --clausify_out                          false
% 3.80/1.02  --sig_cnt_out                           false
% 3.80/1.02  --trig_cnt_out                          false
% 3.80/1.02  --trig_cnt_out_tolerance                1.
% 3.80/1.02  --trig_cnt_out_sk_spl                   false
% 3.80/1.02  --abstr_cl_out                          false
% 3.80/1.02  
% 3.80/1.02  ------ Global Options
% 3.80/1.02  
% 3.80/1.02  --schedule                              default
% 3.80/1.02  --add_important_lit                     false
% 3.80/1.02  --prop_solver_per_cl                    1000
% 3.80/1.02  --min_unsat_core                        false
% 3.80/1.02  --soft_assumptions                      false
% 3.80/1.02  --soft_lemma_size                       3
% 3.80/1.02  --prop_impl_unit_size                   0
% 3.80/1.02  --prop_impl_unit                        []
% 3.80/1.02  --share_sel_clauses                     true
% 3.80/1.02  --reset_solvers                         false
% 3.80/1.02  --bc_imp_inh                            [conj_cone]
% 3.80/1.02  --conj_cone_tolerance                   3.
% 3.80/1.02  --extra_neg_conj                        none
% 3.80/1.02  --large_theory_mode                     true
% 3.80/1.02  --prolific_symb_bound                   200
% 3.80/1.02  --lt_threshold                          2000
% 3.80/1.02  --clause_weak_htbl                      true
% 3.80/1.02  --gc_record_bc_elim                     false
% 3.80/1.02  
% 3.80/1.02  ------ Preprocessing Options
% 3.80/1.02  
% 3.80/1.02  --preprocessing_flag                    true
% 3.80/1.02  --time_out_prep_mult                    0.1
% 3.80/1.02  --splitting_mode                        input
% 3.80/1.02  --splitting_grd                         true
% 3.80/1.02  --splitting_cvd                         false
% 3.80/1.02  --splitting_cvd_svl                     false
% 3.80/1.02  --splitting_nvd                         32
% 3.80/1.02  --sub_typing                            true
% 3.80/1.02  --prep_gs_sim                           true
% 3.80/1.02  --prep_unflatten                        true
% 3.80/1.02  --prep_res_sim                          true
% 3.80/1.02  --prep_upred                            true
% 3.80/1.02  --prep_sem_filter                       exhaustive
% 3.80/1.02  --prep_sem_filter_out                   false
% 3.80/1.02  --pred_elim                             true
% 3.80/1.02  --res_sim_input                         true
% 3.80/1.02  --eq_ax_congr_red                       true
% 3.80/1.02  --pure_diseq_elim                       true
% 3.80/1.02  --brand_transform                       false
% 3.80/1.02  --non_eq_to_eq                          false
% 3.80/1.02  --prep_def_merge                        true
% 3.80/1.02  --prep_def_merge_prop_impl              false
% 3.80/1.02  --prep_def_merge_mbd                    true
% 3.80/1.02  --prep_def_merge_tr_red                 false
% 3.80/1.02  --prep_def_merge_tr_cl                  false
% 3.80/1.02  --smt_preprocessing                     true
% 3.80/1.02  --smt_ac_axioms                         fast
% 3.80/1.02  --preprocessed_out                      false
% 3.80/1.02  --preprocessed_stats                    false
% 3.80/1.02  
% 3.80/1.02  ------ Abstraction refinement Options
% 3.80/1.02  
% 3.80/1.02  --abstr_ref                             []
% 3.80/1.02  --abstr_ref_prep                        false
% 3.80/1.02  --abstr_ref_until_sat                   false
% 3.80/1.02  --abstr_ref_sig_restrict                funpre
% 3.80/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.80/1.02  --abstr_ref_under                       []
% 3.80/1.02  
% 3.80/1.02  ------ SAT Options
% 3.80/1.02  
% 3.80/1.02  --sat_mode                              false
% 3.80/1.02  --sat_fm_restart_options                ""
% 3.80/1.02  --sat_gr_def                            false
% 3.80/1.02  --sat_epr_types                         true
% 3.80/1.02  --sat_non_cyclic_types                  false
% 3.80/1.02  --sat_finite_models                     false
% 3.80/1.02  --sat_fm_lemmas                         false
% 3.80/1.02  --sat_fm_prep                           false
% 3.80/1.02  --sat_fm_uc_incr                        true
% 3.80/1.02  --sat_out_model                         small
% 3.80/1.02  --sat_out_clauses                       false
% 3.80/1.02  
% 3.80/1.02  ------ QBF Options
% 3.80/1.02  
% 3.80/1.02  --qbf_mode                              false
% 3.80/1.02  --qbf_elim_univ                         false
% 3.80/1.02  --qbf_dom_inst                          none
% 3.80/1.02  --qbf_dom_pre_inst                      false
% 3.80/1.02  --qbf_sk_in                             false
% 3.80/1.02  --qbf_pred_elim                         true
% 3.80/1.02  --qbf_split                             512
% 3.80/1.02  
% 3.80/1.02  ------ BMC1 Options
% 3.80/1.02  
% 3.80/1.02  --bmc1_incremental                      false
% 3.80/1.02  --bmc1_axioms                           reachable_all
% 3.80/1.02  --bmc1_min_bound                        0
% 3.80/1.02  --bmc1_max_bound                        -1
% 3.80/1.02  --bmc1_max_bound_default                -1
% 3.80/1.02  --bmc1_symbol_reachability              true
% 3.80/1.02  --bmc1_property_lemmas                  false
% 3.80/1.02  --bmc1_k_induction                      false
% 3.80/1.02  --bmc1_non_equiv_states                 false
% 3.80/1.02  --bmc1_deadlock                         false
% 3.80/1.02  --bmc1_ucm                              false
% 3.80/1.02  --bmc1_add_unsat_core                   none
% 3.80/1.02  --bmc1_unsat_core_children              false
% 3.80/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.80/1.02  --bmc1_out_stat                         full
% 3.80/1.02  --bmc1_ground_init                      false
% 3.80/1.02  --bmc1_pre_inst_next_state              false
% 3.80/1.02  --bmc1_pre_inst_state                   false
% 3.80/1.02  --bmc1_pre_inst_reach_state             false
% 3.80/1.02  --bmc1_out_unsat_core                   false
% 3.80/1.02  --bmc1_aig_witness_out                  false
% 3.80/1.02  --bmc1_verbose                          false
% 3.80/1.02  --bmc1_dump_clauses_tptp                false
% 3.80/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.80/1.02  --bmc1_dump_file                        -
% 3.80/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.80/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.80/1.02  --bmc1_ucm_extend_mode                  1
% 3.80/1.02  --bmc1_ucm_init_mode                    2
% 3.80/1.02  --bmc1_ucm_cone_mode                    none
% 3.80/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.80/1.02  --bmc1_ucm_relax_model                  4
% 3.80/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.80/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.80/1.02  --bmc1_ucm_layered_model                none
% 3.80/1.02  --bmc1_ucm_max_lemma_size               10
% 3.80/1.02  
% 3.80/1.02  ------ AIG Options
% 3.80/1.02  
% 3.80/1.02  --aig_mode                              false
% 3.80/1.02  
% 3.80/1.02  ------ Instantiation Options
% 3.80/1.02  
% 3.80/1.02  --instantiation_flag                    true
% 3.80/1.02  --inst_sos_flag                         false
% 3.80/1.02  --inst_sos_phase                        true
% 3.80/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.80/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.80/1.02  --inst_lit_sel_side                     none
% 3.80/1.02  --inst_solver_per_active                1400
% 3.80/1.02  --inst_solver_calls_frac                1.
% 3.80/1.02  --inst_passive_queue_type               priority_queues
% 3.80/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.80/1.02  --inst_passive_queues_freq              [25;2]
% 3.80/1.02  --inst_dismatching                      true
% 3.80/1.02  --inst_eager_unprocessed_to_passive     true
% 3.80/1.02  --inst_prop_sim_given                   true
% 3.80/1.02  --inst_prop_sim_new                     false
% 3.80/1.02  --inst_subs_new                         false
% 3.80/1.02  --inst_eq_res_simp                      false
% 3.80/1.02  --inst_subs_given                       false
% 3.80/1.02  --inst_orphan_elimination               true
% 3.80/1.02  --inst_learning_loop_flag               true
% 3.80/1.02  --inst_learning_start                   3000
% 3.80/1.02  --inst_learning_factor                  2
% 3.80/1.02  --inst_start_prop_sim_after_learn       3
% 3.80/1.02  --inst_sel_renew                        solver
% 3.80/1.02  --inst_lit_activity_flag                true
% 3.80/1.02  --inst_restr_to_given                   false
% 3.80/1.02  --inst_activity_threshold               500
% 3.80/1.02  --inst_out_proof                        true
% 3.80/1.02  
% 3.80/1.02  ------ Resolution Options
% 3.80/1.02  
% 3.80/1.02  --resolution_flag                       false
% 3.80/1.02  --res_lit_sel                           adaptive
% 3.80/1.02  --res_lit_sel_side                      none
% 3.80/1.02  --res_ordering                          kbo
% 3.80/1.02  --res_to_prop_solver                    active
% 3.80/1.02  --res_prop_simpl_new                    false
% 3.80/1.02  --res_prop_simpl_given                  true
% 3.80/1.02  --res_passive_queue_type                priority_queues
% 3.80/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.80/1.02  --res_passive_queues_freq               [15;5]
% 3.80/1.02  --res_forward_subs                      full
% 3.80/1.02  --res_backward_subs                     full
% 3.80/1.02  --res_forward_subs_resolution           true
% 3.80/1.02  --res_backward_subs_resolution          true
% 3.80/1.02  --res_orphan_elimination                true
% 3.80/1.02  --res_time_limit                        2.
% 3.80/1.02  --res_out_proof                         true
% 3.80/1.02  
% 3.80/1.02  ------ Superposition Options
% 3.80/1.02  
% 3.80/1.02  --superposition_flag                    true
% 3.80/1.02  --sup_passive_queue_type                priority_queues
% 3.80/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.80/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.80/1.02  --demod_completeness_check              fast
% 3.80/1.02  --demod_use_ground                      true
% 3.80/1.02  --sup_to_prop_solver                    passive
% 3.80/1.02  --sup_prop_simpl_new                    true
% 3.80/1.02  --sup_prop_simpl_given                  true
% 3.80/1.02  --sup_fun_splitting                     false
% 3.80/1.02  --sup_smt_interval                      50000
% 3.80/1.02  
% 3.80/1.02  ------ Superposition Simplification Setup
% 3.80/1.02  
% 3.80/1.02  --sup_indices_passive                   []
% 3.80/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.80/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.80/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.80/1.02  --sup_full_bw                           [BwDemod]
% 3.80/1.02  --sup_immed_triv                        [TrivRules]
% 3.80/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.80/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.80/1.02  --sup_immed_bw_main                     []
% 3.80/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.80/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.80/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.80/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.80/1.02  
% 3.80/1.02  ------ Combination Options
% 3.80/1.02  
% 3.80/1.02  --comb_res_mult                         3
% 3.80/1.02  --comb_sup_mult                         2
% 3.80/1.02  --comb_inst_mult                        10
% 3.80/1.02  
% 3.80/1.02  ------ Debug Options
% 3.80/1.02  
% 3.80/1.02  --dbg_backtrace                         false
% 3.80/1.02  --dbg_dump_prop_clauses                 false
% 3.80/1.02  --dbg_dump_prop_clauses_file            -
% 3.80/1.02  --dbg_out_stat                          false
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  ------ Proving...
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  % SZS status Theorem for theBenchmark.p
% 3.80/1.02  
% 3.80/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.80/1.02  
% 3.80/1.02  fof(f1,axiom,(
% 3.80/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f32,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.80/1.02    inference(cnf_transformation,[],[f1])).
% 3.80/1.02  
% 3.80/1.02  fof(f14,conjecture,(
% 3.80/1.02    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f15,negated_conjecture,(
% 3.80/1.02    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 3.80/1.02    inference(negated_conjecture,[],[f14])).
% 3.80/1.02  
% 3.80/1.02  fof(f21,plain,(
% 3.80/1.02    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 3.80/1.02    inference(ennf_transformation,[],[f15])).
% 3.80/1.02  
% 3.80/1.02  fof(f22,plain,(
% 3.80/1.02    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.80/1.02    inference(flattening,[],[f21])).
% 3.80/1.02  
% 3.80/1.02  fof(f30,plain,(
% 3.80/1.02    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK2,sK3) & r1_xboole_0(sK2,sK4) & r1_tarski(sK2,k2_xboole_0(sK3,sK4)))),
% 3.80/1.02    introduced(choice_axiom,[])).
% 3.80/1.02  
% 3.80/1.02  fof(f31,plain,(
% 3.80/1.02    ~r1_tarski(sK2,sK3) & r1_xboole_0(sK2,sK4) & r1_tarski(sK2,k2_xboole_0(sK3,sK4))),
% 3.80/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f30])).
% 3.80/1.02  
% 3.80/1.02  fof(f50,plain,(
% 3.80/1.02    r1_xboole_0(sK2,sK4)),
% 3.80/1.02    inference(cnf_transformation,[],[f31])).
% 3.80/1.02  
% 3.80/1.02  fof(f3,axiom,(
% 3.80/1.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f27,plain,(
% 3.80/1.02    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.80/1.02    inference(nnf_transformation,[],[f3])).
% 3.80/1.02  
% 3.80/1.02  fof(f36,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.80/1.02    inference(cnf_transformation,[],[f27])).
% 3.80/1.02  
% 3.80/1.02  fof(f12,axiom,(
% 3.80/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f47,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.80/1.02    inference(cnf_transformation,[],[f12])).
% 3.80/1.02  
% 3.80/1.02  fof(f53,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.80/1.02    inference(definition_unfolding,[],[f36,f47])).
% 3.80/1.02  
% 3.80/1.02  fof(f11,axiom,(
% 3.80/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f46,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.80/1.02    inference(cnf_transformation,[],[f11])).
% 3.80/1.02  
% 3.80/1.02  fof(f57,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.80/1.02    inference(definition_unfolding,[],[f46,f47])).
% 3.80/1.02  
% 3.80/1.02  fof(f9,axiom,(
% 3.80/1.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f44,plain,(
% 3.80/1.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.80/1.02    inference(cnf_transformation,[],[f9])).
% 3.80/1.02  
% 3.80/1.02  fof(f10,axiom,(
% 3.80/1.02    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f45,plain,(
% 3.80/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.80/1.02    inference(cnf_transformation,[],[f10])).
% 3.80/1.02  
% 3.80/1.02  fof(f49,plain,(
% 3.80/1.02    r1_tarski(sK2,k2_xboole_0(sK3,sK4))),
% 3.80/1.02    inference(cnf_transformation,[],[f31])).
% 3.80/1.02  
% 3.80/1.02  fof(f6,axiom,(
% 3.80/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f20,plain,(
% 3.80/1.02    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.80/1.02    inference(ennf_transformation,[],[f6])).
% 3.80/1.02  
% 3.80/1.02  fof(f41,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.80/1.02    inference(cnf_transformation,[],[f20])).
% 3.80/1.02  
% 3.80/1.02  fof(f7,axiom,(
% 3.80/1.02    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f42,plain,(
% 3.80/1.02    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.80/1.02    inference(cnf_transformation,[],[f7])).
% 3.80/1.02  
% 3.80/1.02  fof(f56,plain,(
% 3.80/1.02    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.80/1.02    inference(definition_unfolding,[],[f42,f47])).
% 3.80/1.02  
% 3.80/1.02  fof(f8,axiom,(
% 3.80/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f43,plain,(
% 3.80/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.80/1.02    inference(cnf_transformation,[],[f8])).
% 3.80/1.02  
% 3.80/1.02  fof(f13,axiom,(
% 3.80/1.02    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f48,plain,(
% 3.80/1.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.80/1.02    inference(cnf_transformation,[],[f13])).
% 3.80/1.02  
% 3.80/1.02  fof(f5,axiom,(
% 3.80/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f16,plain,(
% 3.80/1.02    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.80/1.02    inference(rectify,[],[f5])).
% 3.80/1.02  
% 3.80/1.02  fof(f19,plain,(
% 3.80/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.80/1.02    inference(ennf_transformation,[],[f16])).
% 3.80/1.02  
% 3.80/1.02  fof(f28,plain,(
% 3.80/1.02    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.80/1.02    introduced(choice_axiom,[])).
% 3.80/1.02  
% 3.80/1.02  fof(f29,plain,(
% 3.80/1.02    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.80/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f28])).
% 3.80/1.02  
% 3.80/1.02  fof(f40,plain,(
% 3.80/1.02    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.80/1.02    inference(cnf_transformation,[],[f29])).
% 3.80/1.02  
% 3.80/1.02  fof(f54,plain,(
% 3.80/1.02    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.80/1.02    inference(definition_unfolding,[],[f40,f47])).
% 3.80/1.02  
% 3.80/1.02  fof(f2,axiom,(
% 3.80/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.80/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.80/1.02  
% 3.80/1.02  fof(f17,plain,(
% 3.80/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.80/1.02    inference(ennf_transformation,[],[f2])).
% 3.80/1.02  
% 3.80/1.02  fof(f23,plain,(
% 3.80/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.80/1.02    inference(nnf_transformation,[],[f17])).
% 3.80/1.02  
% 3.80/1.02  fof(f24,plain,(
% 3.80/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.80/1.02    inference(rectify,[],[f23])).
% 3.80/1.02  
% 3.80/1.02  fof(f25,plain,(
% 3.80/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.80/1.02    introduced(choice_axiom,[])).
% 3.80/1.02  
% 3.80/1.02  fof(f26,plain,(
% 3.80/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.80/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 3.80/1.02  
% 3.80/1.02  fof(f33,plain,(
% 3.80/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.80/1.02    inference(cnf_transformation,[],[f26])).
% 3.80/1.02  
% 3.80/1.02  fof(f34,plain,(
% 3.80/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.80/1.02    inference(cnf_transformation,[],[f26])).
% 3.80/1.02  
% 3.80/1.02  fof(f37,plain,(
% 3.80/1.02    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.80/1.02    inference(cnf_transformation,[],[f27])).
% 3.80/1.02  
% 3.80/1.02  fof(f52,plain,(
% 3.80/1.02    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.80/1.02    inference(definition_unfolding,[],[f37,f47])).
% 3.80/1.02  
% 3.80/1.02  fof(f51,plain,(
% 3.80/1.02    ~r1_tarski(sK2,sK3)),
% 3.80/1.02    inference(cnf_transformation,[],[f31])).
% 3.80/1.02  
% 3.80/1.02  cnf(c_0,plain,
% 3.80/1.02      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.80/1.02      inference(cnf_transformation,[],[f32]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_17,negated_conjecture,
% 3.80/1.02      ( r1_xboole_0(sK2,sK4) ),
% 3.80/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_660,plain,
% 3.80/1.02      ( r1_xboole_0(sK2,sK4) = iProver_top ),
% 3.80/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_5,plain,
% 3.80/1.02      ( ~ r1_xboole_0(X0,X1)
% 3.80/1.02      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.80/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_667,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.80/1.02      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.80/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_6549,plain,
% 3.80/1.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k1_xboole_0 ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_660,c_667]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_14,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.80/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_7427,plain,
% 3.80/1.02      ( k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,k1_xboole_0) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_6549,c_14]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_12,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.80/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_7432,plain,
% 3.80/1.02      ( k4_xboole_0(sK2,sK4) = sK2 ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_7427,c_12]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_13,plain,
% 3.80/1.02      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.80/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_7673,plain,
% 3.80/1.02      ( k4_xboole_0(sK2,k2_xboole_0(sK4,X0)) = k4_xboole_0(sK2,X0) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_7432,c_13]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_8868,plain,
% 3.80/1.02      ( k4_xboole_0(sK2,k2_xboole_0(X0,sK4)) = k4_xboole_0(sK2,X0) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_0,c_7673]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_18,negated_conjecture,
% 3.80/1.02      ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
% 3.80/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_659,plain,
% 3.80/1.02      ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) = iProver_top ),
% 3.80/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_9,plain,
% 3.80/1.02      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.80/1.02      inference(cnf_transformation,[],[f41]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_663,plain,
% 3.80/1.02      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.80/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1874,plain,
% 3.80/1.02      ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = k2_xboole_0(sK3,sK4) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_659,c_663]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_10,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.80/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_682,plain,
% 3.80/1.02      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.80/1.02      inference(light_normalisation,[status(thm)],[c_10,c_12]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1005,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_13,c_682]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_11,plain,
% 3.80/1.02      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.80/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1007,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 3.80/1.02      inference(demodulation,[status(thm)],[c_1005,c_11]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1308,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_0,c_1007]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_2148,plain,
% 3.80/1.02      ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = k1_xboole_0 ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_1874,c_1308]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_10216,plain,
% 3.80/1.02      ( k4_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_8868,c_2148]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_11102,plain,
% 3.80/1.02      ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k1_xboole_0) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_10216,c_11]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_15,plain,
% 3.80/1.02      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.80/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_662,plain,
% 3.80/1.02      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 3.80/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_872,plain,
% 3.80/1.02      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_0,c_662]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_11218,plain,
% 3.80/1.02      ( r1_tarski(sK2,k2_xboole_0(sK3,k1_xboole_0)) = iProver_top ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_11102,c_872]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_325,plain,
% 3.80/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.80/1.02      theory(equality) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_770,plain,
% 3.80/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,sK3) | sK3 != X1 | sK2 != X0 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_325]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_6687,plain,
% 3.80/1.02      ( ~ r1_tarski(X0,k2_xboole_0(sK3,X1))
% 3.80/1.02      | r1_tarski(sK2,sK3)
% 3.80/1.02      | sK3 != k2_xboole_0(sK3,X1)
% 3.80/1.02      | sK2 != X0 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_770]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_11028,plain,
% 3.80/1.02      ( ~ r1_tarski(sK2,k2_xboole_0(sK3,X0))
% 3.80/1.02      | r1_tarski(sK2,sK3)
% 3.80/1.02      | sK3 != k2_xboole_0(sK3,X0)
% 3.80/1.02      | sK2 != sK2 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_6687]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_11029,plain,
% 3.80/1.02      ( sK3 != k2_xboole_0(sK3,X0)
% 3.80/1.02      | sK2 != sK2
% 3.80/1.02      | r1_tarski(sK2,k2_xboole_0(sK3,X0)) != iProver_top
% 3.80/1.02      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.80/1.02      inference(predicate_to_equality,[status(thm)],[c_11028]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_11031,plain,
% 3.80/1.02      ( sK3 != k2_xboole_0(sK3,k1_xboole_0)
% 3.80/1.02      | sK2 != sK2
% 3.80/1.02      | r1_tarski(sK2,k2_xboole_0(sK3,k1_xboole_0)) != iProver_top
% 3.80/1.02      | r1_tarski(sK2,sK3) = iProver_top ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_11029]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_3447,plain,
% 3.80/1.02      ( ~ r1_tarski(X0,X1)
% 3.80/1.02      | r1_tarski(X2,k4_xboole_0(X3,k4_xboole_0(X3,X4)))
% 3.80/1.02      | X2 != X0
% 3.80/1.02      | k4_xboole_0(X3,k4_xboole_0(X3,X4)) != X1 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_325]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_3449,plain,
% 3.80/1.02      ( r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
% 3.80/1.02      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.80/1.02      | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
% 3.80/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_3447]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_7,plain,
% 3.80/1.02      ( ~ r1_xboole_0(X0,X1)
% 3.80/1.02      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.80/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_3419,plain,
% 3.80/1.02      ( ~ r1_xboole_0(X0,X1)
% 3.80/1.02      | ~ r2_hidden(sK0(X2,sK3),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_3425,plain,
% 3.80/1.02      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.80/1.02      | ~ r2_hidden(sK0(k1_xboole_0,sK3),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_3419]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_3,plain,
% 3.80/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.80/1.02      inference(cnf_transformation,[],[f33]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_2275,plain,
% 3.80/1.02      ( ~ r2_hidden(sK0(X0,sK3),X0)
% 3.80/1.02      | r2_hidden(sK0(X0,sK3),X1)
% 3.80/1.02      | ~ r1_tarski(X0,X1) ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_3418,plain,
% 3.80/1.02      ( ~ r2_hidden(sK0(X0,sK3),X0)
% 3.80/1.02      | r2_hidden(sK0(X0,sK3),k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.80/1.02      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_2275]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_3421,plain,
% 3.80/1.02      ( r2_hidden(sK0(k1_xboole_0,sK3),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
% 3.80/1.02      | ~ r2_hidden(sK0(k1_xboole_0,sK3),k1_xboole_0)
% 3.80/1.02      | ~ r1_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_3418]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_2395,plain,
% 3.80/1.02      ( k2_xboole_0(sK3,X0) = k2_xboole_0(X0,sK3) ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_2397,plain,
% 3.80/1.02      ( k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(k1_xboole_0,sK3) ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_2395]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_323,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_794,plain,
% 3.80/1.02      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_323]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1797,plain,
% 3.80/1.02      ( X0 != k2_xboole_0(X1,sK3)
% 3.80/1.02      | sK3 = X0
% 3.80/1.02      | sK3 != k2_xboole_0(X1,sK3) ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_794]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_2394,plain,
% 3.80/1.02      ( k2_xboole_0(sK3,X0) != k2_xboole_0(X0,sK3)
% 3.80/1.02      | sK3 != k2_xboole_0(X0,sK3)
% 3.80/1.02      | sK3 = k2_xboole_0(sK3,X0) ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_1797]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_2396,plain,
% 3.80/1.02      ( k2_xboole_0(sK3,k1_xboole_0) != k2_xboole_0(k1_xboole_0,sK3)
% 3.80/1.02      | sK3 = k2_xboole_0(sK3,k1_xboole_0)
% 3.80/1.02      | sK3 != k2_xboole_0(k1_xboole_0,sK3) ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_2394]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_999,plain,
% 3.80/1.02      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_12,c_13]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1720,plain,
% 3.80/1.02      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) = k1_xboole_0 ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_999,c_682]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1845,plain,
% 3.80/1.02      ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_1720,c_12]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_986,plain,
% 3.80/1.02      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_682,c_11]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1129,plain,
% 3.80/1.02      ( r1_tarski(k1_xboole_0,k2_xboole_0(X0,X0)) = iProver_top ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_986,c_872]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_2009,plain,
% 3.80/1.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.80/1.02      inference(superposition,[status(thm)],[c_1845,c_1129]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_2014,plain,
% 3.80/1.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.80/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2009]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_2,plain,
% 3.80/1.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.80/1.02      inference(cnf_transformation,[],[f34]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1149,plain,
% 3.80/1.02      ( r2_hidden(sK0(X0,sK3),X0) | r1_tarski(X0,sK3) ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_1156,plain,
% 3.80/1.02      ( r2_hidden(sK0(k1_xboole_0,sK3),k1_xboole_0)
% 3.80/1.02      | r1_tarski(k1_xboole_0,sK3) ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_1149]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_973,plain,
% 3.80/1.02      ( ~ r1_tarski(X0,sK3) | k2_xboole_0(X0,sK3) = sK3 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_976,plain,
% 3.80/1.02      ( ~ r1_tarski(k1_xboole_0,sK3)
% 3.80/1.02      | k2_xboole_0(k1_xboole_0,sK3) = sK3 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_973]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_855,plain,
% 3.80/1.02      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_794]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_972,plain,
% 3.80/1.02      ( k2_xboole_0(X0,sK3) != sK3
% 3.80/1.02      | sK3 = k2_xboole_0(X0,sK3)
% 3.80/1.02      | sK3 != sK3 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_855]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_974,plain,
% 3.80/1.02      ( k2_xboole_0(k1_xboole_0,sK3) != sK3
% 3.80/1.02      | sK3 = k2_xboole_0(k1_xboole_0,sK3)
% 3.80/1.02      | sK3 != sK3 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_972]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_322,plain,( X0 = X0 ),theory(equality) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_845,plain,
% 3.80/1.02      ( sK2 = sK2 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_322]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_789,plain,
% 3.80/1.02      ( sK3 = sK3 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_322]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_334,plain,
% 3.80/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_322]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_4,plain,
% 3.80/1.02      ( r1_xboole_0(X0,X1)
% 3.80/1.02      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.80/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_42,plain,
% 3.80/1.02      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.80/1.02      | k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_29,plain,
% 3.80/1.02      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 3.80/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_16,negated_conjecture,
% 3.80/1.02      ( ~ r1_tarski(sK2,sK3) ),
% 3.80/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(c_21,plain,
% 3.80/1.02      ( r1_tarski(sK2,sK3) != iProver_top ),
% 3.80/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.80/1.02  
% 3.80/1.02  cnf(contradiction,plain,
% 3.80/1.02      ( $false ),
% 3.80/1.02      inference(minisat,
% 3.80/1.02                [status(thm)],
% 3.80/1.02                [c_11218,c_11031,c_3449,c_3425,c_3421,c_2397,c_2396,
% 3.80/1.02                 c_2014,c_1156,c_976,c_974,c_845,c_789,c_334,c_42,c_29,
% 3.80/1.02                 c_21]) ).
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.80/1.02  
% 3.80/1.02  ------                               Statistics
% 3.80/1.02  
% 3.80/1.02  ------ General
% 3.80/1.02  
% 3.80/1.02  abstr_ref_over_cycles:                  0
% 3.80/1.02  abstr_ref_under_cycles:                 0
% 3.80/1.02  gc_basic_clause_elim:                   0
% 3.80/1.02  forced_gc_time:                         0
% 3.80/1.02  parsing_time:                           0.007
% 3.80/1.02  unif_index_cands_time:                  0.
% 3.80/1.02  unif_index_add_time:                    0.
% 3.80/1.02  orderings_time:                         0.
% 3.80/1.02  out_proof_time:                         0.006
% 3.80/1.02  total_time:                             0.323
% 3.80/1.02  num_of_symbols:                         42
% 3.80/1.02  num_of_terms:                           10191
% 3.80/1.02  
% 3.80/1.02  ------ Preprocessing
% 3.80/1.02  
% 3.80/1.02  num_of_splits:                          0
% 3.80/1.02  num_of_split_atoms:                     0
% 3.80/1.02  num_of_reused_defs:                     0
% 3.80/1.02  num_eq_ax_congr_red:                    8
% 3.80/1.02  num_of_sem_filtered_clauses:            1
% 3.80/1.02  num_of_subtypes:                        0
% 3.80/1.02  monotx_restored_types:                  0
% 3.80/1.02  sat_num_of_epr_types:                   0
% 3.80/1.02  sat_num_of_non_cyclic_types:            0
% 3.80/1.02  sat_guarded_non_collapsed_types:        0
% 3.80/1.02  num_pure_diseq_elim:                    0
% 3.80/1.02  simp_replaced_by:                       0
% 3.80/1.02  res_preprocessed:                       72
% 3.80/1.02  prep_upred:                             0
% 3.80/1.02  prep_unflattend:                        17
% 3.80/1.02  smt_new_axioms:                         0
% 3.80/1.02  pred_elim_cands:                        3
% 3.80/1.02  pred_elim:                              0
% 3.80/1.02  pred_elim_cl:                           0
% 3.80/1.02  pred_elim_cycles:                       1
% 3.80/1.02  merged_defs:                            6
% 3.80/1.02  merged_defs_ncl:                        0
% 3.80/1.02  bin_hyper_res:                          6
% 3.80/1.02  prep_cycles:                            3
% 3.80/1.02  pred_elim_time:                         0.002
% 3.80/1.02  splitting_time:                         0.
% 3.80/1.02  sem_filter_time:                        0.
% 3.80/1.02  monotx_time:                            0.
% 3.80/1.02  subtype_inf_time:                       0.
% 3.80/1.02  
% 3.80/1.02  ------ Problem properties
% 3.80/1.02  
% 3.80/1.02  clauses:                                19
% 3.80/1.02  conjectures:                            3
% 3.80/1.02  epr:                                    4
% 3.80/1.02  horn:                                   17
% 3.80/1.02  ground:                                 3
% 3.80/1.02  unary:                                  10
% 3.80/1.02  binary:                                 8
% 3.80/1.02  lits:                                   29
% 3.80/1.02  lits_eq:                                9
% 3.80/1.02  fd_pure:                                0
% 3.80/1.02  fd_pseudo:                              0
% 3.80/1.02  fd_cond:                                0
% 3.80/1.02  fd_pseudo_cond:                         0
% 3.80/1.02  ac_symbols:                             0
% 3.80/1.02  
% 3.80/1.02  ------ Propositional Solver
% 3.80/1.02  
% 3.80/1.02  prop_solver_calls:                      28
% 3.80/1.02  prop_fast_solver_calls:                 410
% 3.80/1.02  smt_solver_calls:                       0
% 3.80/1.02  smt_fast_solver_calls:                  0
% 3.80/1.02  prop_num_of_clauses:                    3955
% 3.80/1.02  prop_preprocess_simplified:             7003
% 3.80/1.02  prop_fo_subsumed:                       1
% 3.80/1.02  prop_solver_time:                       0.
% 3.80/1.02  smt_solver_time:                        0.
% 3.80/1.02  smt_fast_solver_time:                   0.
% 3.80/1.02  prop_fast_solver_time:                  0.
% 3.80/1.02  prop_unsat_core_time:                   0.
% 3.80/1.02  
% 3.80/1.02  ------ QBF
% 3.80/1.02  
% 3.80/1.02  qbf_q_res:                              0
% 3.80/1.02  qbf_num_tautologies:                    0
% 3.80/1.02  qbf_prep_cycles:                        0
% 3.80/1.02  
% 3.80/1.02  ------ BMC1
% 3.80/1.02  
% 3.80/1.02  bmc1_current_bound:                     -1
% 3.80/1.02  bmc1_last_solved_bound:                 -1
% 3.80/1.02  bmc1_unsat_core_size:                   -1
% 3.80/1.02  bmc1_unsat_core_parents_size:           -1
% 3.80/1.02  bmc1_merge_next_fun:                    0
% 3.80/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.80/1.02  
% 3.80/1.02  ------ Instantiation
% 3.80/1.02  
% 3.80/1.02  inst_num_of_clauses:                    965
% 3.80/1.02  inst_num_in_passive:                    497
% 3.80/1.02  inst_num_in_active:                     439
% 3.80/1.02  inst_num_in_unprocessed:                29
% 3.80/1.02  inst_num_of_loops:                      510
% 3.80/1.02  inst_num_of_learning_restarts:          0
% 3.80/1.02  inst_num_moves_active_passive:          65
% 3.80/1.02  inst_lit_activity:                      0
% 3.80/1.02  inst_lit_activity_moves:                0
% 3.80/1.02  inst_num_tautologies:                   0
% 3.80/1.02  inst_num_prop_implied:                  0
% 3.80/1.02  inst_num_existing_simplified:           0
% 3.80/1.02  inst_num_eq_res_simplified:             0
% 3.80/1.02  inst_num_child_elim:                    0
% 3.80/1.02  inst_num_of_dismatching_blockings:      284
% 3.80/1.02  inst_num_of_non_proper_insts:           884
% 3.80/1.02  inst_num_of_duplicates:                 0
% 3.80/1.02  inst_inst_num_from_inst_to_res:         0
% 3.80/1.02  inst_dismatching_checking_time:         0.
% 3.80/1.02  
% 3.80/1.02  ------ Resolution
% 3.80/1.02  
% 3.80/1.02  res_num_of_clauses:                     0
% 3.80/1.02  res_num_in_passive:                     0
% 3.80/1.02  res_num_in_active:                      0
% 3.80/1.02  res_num_of_loops:                       75
% 3.80/1.02  res_forward_subset_subsumed:            59
% 3.80/1.02  res_backward_subset_subsumed:           0
% 3.80/1.02  res_forward_subsumed:                   0
% 3.80/1.02  res_backward_subsumed:                  0
% 3.80/1.02  res_forward_subsumption_resolution:     0
% 3.80/1.02  res_backward_subsumption_resolution:    0
% 3.80/1.02  res_clause_to_clause_subsumption:       4583
% 3.80/1.02  res_orphan_elimination:                 0
% 3.80/1.02  res_tautology_del:                      93
% 3.80/1.02  res_num_eq_res_simplified:              0
% 3.80/1.02  res_num_sel_changes:                    0
% 3.80/1.02  res_moves_from_active_to_pass:          0
% 3.80/1.02  
% 3.80/1.02  ------ Superposition
% 3.80/1.02  
% 3.80/1.02  sup_time_total:                         0.
% 3.80/1.02  sup_time_generating:                    0.
% 3.80/1.02  sup_time_sim_full:                      0.
% 3.80/1.02  sup_time_sim_immed:                     0.
% 3.80/1.02  
% 3.80/1.02  sup_num_of_clauses:                     487
% 3.80/1.02  sup_num_in_active:                      92
% 3.80/1.02  sup_num_in_passive:                     395
% 3.80/1.02  sup_num_of_loops:                       101
% 3.80/1.02  sup_fw_superposition:                   751
% 3.80/1.02  sup_bw_superposition:                   852
% 3.80/1.02  sup_immediate_simplified:               698
% 3.80/1.02  sup_given_eliminated:                   8
% 3.80/1.02  comparisons_done:                       0
% 3.80/1.02  comparisons_avoided:                    0
% 3.80/1.02  
% 3.80/1.02  ------ Simplifications
% 3.80/1.02  
% 3.80/1.02  
% 3.80/1.02  sim_fw_subset_subsumed:                 6
% 3.80/1.02  sim_bw_subset_subsumed:                 4
% 3.80/1.02  sim_fw_subsumed:                        266
% 3.80/1.02  sim_bw_subsumed:                        10
% 3.80/1.02  sim_fw_subsumption_res:                 0
% 3.80/1.02  sim_bw_subsumption_res:                 0
% 3.80/1.02  sim_tautology_del:                      1
% 3.80/1.02  sim_eq_tautology_del:                   94
% 3.80/1.02  sim_eq_res_simp:                        5
% 3.80/1.02  sim_fw_demodulated:                     200
% 3.80/1.02  sim_bw_demodulated:                     23
% 3.80/1.02  sim_light_normalised:                   295
% 3.80/1.02  sim_joinable_taut:                      0
% 3.80/1.02  sim_joinable_simp:                      0
% 3.80/1.02  sim_ac_normalised:                      0
% 3.80/1.02  sim_smt_subsumption:                    0
% 3.80/1.02  
%------------------------------------------------------------------------------
