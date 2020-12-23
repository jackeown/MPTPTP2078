%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:37 EST 2020

% Result     : Theorem 7.39s
% Output     : CNFRefutation 7.39s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 338 expanded)
%              Number of clauses        :   71 ( 131 expanded)
%              Number of leaves         :   21 (  78 expanded)
%              Depth                    :   22
%              Number of atoms          :  284 ( 823 expanded)
%              Number of equality atoms :   78 ( 182 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f27])).

fof(f34,plain,
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

fof(f35,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f34])).

fof(f55,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f66,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f55,f61])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f32])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f60])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f58,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
    inference(definition_unfolding,[],[f58,f59])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_187,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_624,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_194,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | k3_xboole_0(X0_41,X1_41) = X0_41 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_617,plain,
    ( k3_xboole_0(X0_41,X1_41) = X0_41
    | r1_tarski(X0_41,X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_194])).

cnf(c_1215,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_624,c_617])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_203,plain,
    ( k3_xboole_0(X0_41,X1_41) = k3_xboole_0(X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_193,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X0_41,k3_xboole_0(X1_41,X2_41)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_618,plain,
    ( r1_xboole_0(X0_41,X1_41) != iProver_top
    | r1_xboole_0(X0_41,k3_xboole_0(X1_41,X2_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_1869,plain,
    ( r1_xboole_0(X0_41,X1_41) != iProver_top
    | r1_xboole_0(X0_41,k3_xboole_0(X2_41,X1_41)) = iProver_top ),
    inference(superposition,[status(thm)],[c_203,c_618])).

cnf(c_3343,plain,
    ( r1_xboole_0(X0_41,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r1_xboole_0(X0_41,k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1215,c_1869])).

cnf(c_208,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_206,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_1235,plain,
    ( X0_41 != X1_41
    | X1_41 = X0_41 ),
    inference(resolution,[status(thm)],[c_208,c_206])).

cnf(c_2781,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | X0_41 = k3_xboole_0(X0_41,X1_41) ),
    inference(resolution,[status(thm)],[c_1235,c_194])).

cnf(c_211,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X2_41,X3_41)
    | X2_41 != X0_41
    | X3_41 != X1_41 ),
    theory(equality)).

cnf(c_1415,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X2_41,X1_41)
    | X2_41 != X0_41 ),
    inference(resolution,[status(thm)],[c_211,c_206])).

cnf(c_2803,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_xboole_0(X0_41,X2_41)
    | ~ r1_xboole_0(k3_xboole_0(X0_41,X1_41),X2_41) ),
    inference(resolution,[status(thm)],[c_2781,c_1415])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_196,plain,
    ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
    | ~ r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_197,plain,
    ( r2_hidden(sK0(X0_41,X1_41),X0_41)
    | r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1061,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(k3_xboole_0(X0_41,X1_41),X2_41) ),
    inference(resolution,[status(thm)],[c_196,c_197])).

cnf(c_4757,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X0_41,X2_41) ),
    inference(resolution,[status(thm)],[c_2803,c_1061])).

cnf(c_4784,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41)
    | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(resolution,[status(thm)],[c_4757,c_187])).

cnf(c_4798,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_4784,c_1061])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_199,plain,
    ( ~ r2_hidden(X0_42,X0_41)
    | ~ r2_hidden(X0_42,X1_41)
    | ~ r1_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_798,plain,
    ( ~ r2_hidden(X0_42,sK3)
    | ~ r2_hidden(X0_42,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_199])).

cnf(c_800,plain,
    ( ~ r2_hidden(sK5,sK3)
    | ~ r2_hidden(sK5,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | r1_xboole_0(k2_enumset1(X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_191,plain,
    ( r2_hidden(X0_42,X0_41)
    | r2_hidden(X1_42,X0_41)
    | r1_xboole_0(k2_enumset1(X1_42,X1_42,X1_42,X0_42),X0_41) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_934,plain,
    ( r2_hidden(X0_42,sK3)
    | r2_hidden(X1_42,sK3)
    | r1_xboole_0(k2_enumset1(X1_42,X1_42,X1_42,X0_42),sK3) ),
    inference(instantiation,[status(thm)],[c_191])).

cnf(c_936,plain,
    ( r2_hidden(sK5,sK3)
    | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_934])).

cnf(c_1927,plain,
    ( ~ r1_xboole_0(k3_xboole_0(X0_41,X1_41),X2_41)
    | r1_xboole_0(k3_xboole_0(X1_41,X0_41),X2_41) ),
    inference(resolution,[status(thm)],[c_1415,c_203])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_200,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_887,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(k3_xboole_0(X1_41,X2_41),X0_41) ),
    inference(resolution,[status(thm)],[c_193,c_200])).

cnf(c_1942,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | r1_xboole_0(k3_xboole_0(X2_41,X1_41),X0_41) ),
    inference(resolution,[status(thm)],[c_1927,c_887])).

cnf(c_4810,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3)
    | r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41) ),
    inference(resolution,[status(thm)],[c_4784,c_1942])).

cnf(c_5060,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4798,c_16,c_15,c_800,c_936,c_4810])).

cnf(c_5074,plain,
    ( r1_xboole_0(X0_41,k3_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_5060,c_200])).

cnf(c_5079,plain,
    ( r1_xboole_0(X0_41,k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5074])).

cnf(c_21162,plain,
    ( r1_xboole_0(X0_41,k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3343,c_5079])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_201,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X0_41,X1_41) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_610,plain,
    ( k3_xboole_0(X0_41,X1_41) = k1_xboole_0
    | r1_xboole_0(X0_41,X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_201])).

cnf(c_21172,plain,
    ( k3_xboole_0(X0_41,k3_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_21162,c_610])).

cnf(c_21274,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),X0_41) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_21172,c_203])).

cnf(c_21671,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_21274,c_1215])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_202,plain,
    ( r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X0_41,X1_41) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_609,plain,
    ( k3_xboole_0(X0_41,X1_41) != k1_xboole_0
    | r1_xboole_0(X0_41,X1_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_202])).

cnf(c_878,plain,
    ( k3_xboole_0(X0_41,X1_41) != k1_xboole_0
    | r1_xboole_0(X1_41,X0_41) = iProver_top ),
    inference(superposition,[status(thm)],[c_203,c_609])).

cnf(c_21770,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_21671,c_878])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_192,plain,
    ( ~ r1_xboole_0(X0_41,X1_41)
    | k3_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X2_41,X1_41)))) = k3_xboole_0(X0_41,X2_41) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_619,plain,
    ( k3_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X2_41,X1_41)))) = k3_xboole_0(X0_41,X2_41)
    | r1_xboole_0(X0_41,X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_22163,plain,
    ( k3_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2)))) = k3_xboole_0(sK3,X0_41) ),
    inference(superposition,[status(thm)],[c_21770,c_619])).

cnf(c_23135,plain,
    ( k3_xboole_0(sK3,X0_41) != k1_xboole_0
    | r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2))),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_22163,c_878])).

cnf(c_23324,plain,
    ( k3_xboole_0(sK3,sK4) != k1_xboole_0
    | r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_23135])).

cnf(c_852,plain,
    ( ~ r1_xboole_0(sK3,sK4)
    | k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_736,plain,
    ( r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_21,plain,
    ( r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23324,c_852,c_736,c_21,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:03:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.39/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.39/1.49  
% 7.39/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.39/1.49  
% 7.39/1.49  ------  iProver source info
% 7.39/1.49  
% 7.39/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.39/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.39/1.49  git: non_committed_changes: false
% 7.39/1.49  git: last_make_outside_of_git: false
% 7.39/1.49  
% 7.39/1.49  ------ 
% 7.39/1.49  
% 7.39/1.49  ------ Input Options
% 7.39/1.49  
% 7.39/1.49  --out_options                           all
% 7.39/1.49  --tptp_safe_out                         true
% 7.39/1.49  --problem_path                          ""
% 7.39/1.49  --include_path                          ""
% 7.39/1.49  --clausifier                            res/vclausify_rel
% 7.39/1.49  --clausifier_options                    --mode clausify
% 7.39/1.49  --stdin                                 false
% 7.39/1.49  --stats_out                             sel
% 7.39/1.49  
% 7.39/1.49  ------ General Options
% 7.39/1.49  
% 7.39/1.49  --fof                                   false
% 7.39/1.49  --time_out_real                         604.99
% 7.39/1.49  --time_out_virtual                      -1.
% 7.39/1.49  --symbol_type_check                     false
% 7.39/1.49  --clausify_out                          false
% 7.39/1.49  --sig_cnt_out                           false
% 7.39/1.49  --trig_cnt_out                          false
% 7.39/1.49  --trig_cnt_out_tolerance                1.
% 7.39/1.49  --trig_cnt_out_sk_spl                   false
% 7.39/1.49  --abstr_cl_out                          false
% 7.39/1.49  
% 7.39/1.49  ------ Global Options
% 7.39/1.49  
% 7.39/1.49  --schedule                              none
% 7.39/1.49  --add_important_lit                     false
% 7.39/1.49  --prop_solver_per_cl                    1000
% 7.39/1.49  --min_unsat_core                        false
% 7.39/1.49  --soft_assumptions                      false
% 7.39/1.49  --soft_lemma_size                       3
% 7.39/1.49  --prop_impl_unit_size                   0
% 7.39/1.49  --prop_impl_unit                        []
% 7.39/1.49  --share_sel_clauses                     true
% 7.39/1.49  --reset_solvers                         false
% 7.39/1.49  --bc_imp_inh                            [conj_cone]
% 7.39/1.49  --conj_cone_tolerance                   3.
% 7.39/1.49  --extra_neg_conj                        none
% 7.39/1.49  --large_theory_mode                     true
% 7.39/1.49  --prolific_symb_bound                   200
% 7.39/1.49  --lt_threshold                          2000
% 7.39/1.49  --clause_weak_htbl                      true
% 7.39/1.49  --gc_record_bc_elim                     false
% 7.39/1.49  
% 7.39/1.49  ------ Preprocessing Options
% 7.39/1.49  
% 7.39/1.49  --preprocessing_flag                    true
% 7.39/1.49  --time_out_prep_mult                    0.1
% 7.39/1.49  --splitting_mode                        input
% 7.39/1.49  --splitting_grd                         true
% 7.39/1.49  --splitting_cvd                         false
% 7.39/1.49  --splitting_cvd_svl                     false
% 7.39/1.49  --splitting_nvd                         32
% 7.39/1.49  --sub_typing                            true
% 7.39/1.49  --prep_gs_sim                           false
% 7.39/1.49  --prep_unflatten                        true
% 7.39/1.49  --prep_res_sim                          true
% 7.39/1.49  --prep_upred                            true
% 7.39/1.49  --prep_sem_filter                       exhaustive
% 7.39/1.49  --prep_sem_filter_out                   false
% 7.39/1.49  --pred_elim                             false
% 7.39/1.49  --res_sim_input                         true
% 7.39/1.49  --eq_ax_congr_red                       true
% 7.39/1.49  --pure_diseq_elim                       true
% 7.39/1.49  --brand_transform                       false
% 7.39/1.49  --non_eq_to_eq                          false
% 7.39/1.49  --prep_def_merge                        true
% 7.39/1.49  --prep_def_merge_prop_impl              false
% 7.39/1.49  --prep_def_merge_mbd                    true
% 7.39/1.49  --prep_def_merge_tr_red                 false
% 7.39/1.49  --prep_def_merge_tr_cl                  false
% 7.39/1.49  --smt_preprocessing                     true
% 7.39/1.49  --smt_ac_axioms                         fast
% 7.39/1.49  --preprocessed_out                      false
% 7.39/1.49  --preprocessed_stats                    false
% 7.39/1.49  
% 7.39/1.49  ------ Abstraction refinement Options
% 7.39/1.49  
% 7.39/1.49  --abstr_ref                             []
% 7.39/1.49  --abstr_ref_prep                        false
% 7.39/1.49  --abstr_ref_until_sat                   false
% 7.39/1.49  --abstr_ref_sig_restrict                funpre
% 7.39/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.39/1.49  --abstr_ref_under                       []
% 7.39/1.49  
% 7.39/1.49  ------ SAT Options
% 7.39/1.49  
% 7.39/1.49  --sat_mode                              false
% 7.39/1.49  --sat_fm_restart_options                ""
% 7.39/1.49  --sat_gr_def                            false
% 7.39/1.49  --sat_epr_types                         true
% 7.39/1.49  --sat_non_cyclic_types                  false
% 7.39/1.49  --sat_finite_models                     false
% 7.39/1.49  --sat_fm_lemmas                         false
% 7.39/1.49  --sat_fm_prep                           false
% 7.39/1.49  --sat_fm_uc_incr                        true
% 7.39/1.49  --sat_out_model                         small
% 7.39/1.49  --sat_out_clauses                       false
% 7.39/1.49  
% 7.39/1.49  ------ QBF Options
% 7.39/1.49  
% 7.39/1.49  --qbf_mode                              false
% 7.39/1.49  --qbf_elim_univ                         false
% 7.39/1.49  --qbf_dom_inst                          none
% 7.39/1.49  --qbf_dom_pre_inst                      false
% 7.39/1.49  --qbf_sk_in                             false
% 7.39/1.49  --qbf_pred_elim                         true
% 7.39/1.49  --qbf_split                             512
% 7.39/1.49  
% 7.39/1.49  ------ BMC1 Options
% 7.39/1.49  
% 7.39/1.49  --bmc1_incremental                      false
% 7.39/1.49  --bmc1_axioms                           reachable_all
% 7.39/1.49  --bmc1_min_bound                        0
% 7.39/1.49  --bmc1_max_bound                        -1
% 7.39/1.49  --bmc1_max_bound_default                -1
% 7.39/1.49  --bmc1_symbol_reachability              true
% 7.39/1.49  --bmc1_property_lemmas                  false
% 7.39/1.49  --bmc1_k_induction                      false
% 7.39/1.49  --bmc1_non_equiv_states                 false
% 7.39/1.49  --bmc1_deadlock                         false
% 7.39/1.49  --bmc1_ucm                              false
% 7.39/1.49  --bmc1_add_unsat_core                   none
% 7.39/1.49  --bmc1_unsat_core_children              false
% 7.39/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.39/1.49  --bmc1_out_stat                         full
% 7.39/1.49  --bmc1_ground_init                      false
% 7.39/1.49  --bmc1_pre_inst_next_state              false
% 7.39/1.49  --bmc1_pre_inst_state                   false
% 7.39/1.49  --bmc1_pre_inst_reach_state             false
% 7.39/1.49  --bmc1_out_unsat_core                   false
% 7.39/1.49  --bmc1_aig_witness_out                  false
% 7.39/1.49  --bmc1_verbose                          false
% 7.39/1.49  --bmc1_dump_clauses_tptp                false
% 7.39/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.39/1.49  --bmc1_dump_file                        -
% 7.39/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.39/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.39/1.49  --bmc1_ucm_extend_mode                  1
% 7.39/1.49  --bmc1_ucm_init_mode                    2
% 7.39/1.49  --bmc1_ucm_cone_mode                    none
% 7.39/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.39/1.49  --bmc1_ucm_relax_model                  4
% 7.39/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.39/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.39/1.49  --bmc1_ucm_layered_model                none
% 7.39/1.49  --bmc1_ucm_max_lemma_size               10
% 7.39/1.49  
% 7.39/1.49  ------ AIG Options
% 7.39/1.49  
% 7.39/1.49  --aig_mode                              false
% 7.39/1.49  
% 7.39/1.49  ------ Instantiation Options
% 7.39/1.49  
% 7.39/1.49  --instantiation_flag                    true
% 7.39/1.49  --inst_sos_flag                         false
% 7.39/1.49  --inst_sos_phase                        true
% 7.39/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.39/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.39/1.49  --inst_lit_sel_side                     num_symb
% 7.39/1.49  --inst_solver_per_active                1400
% 7.39/1.49  --inst_solver_calls_frac                1.
% 7.39/1.49  --inst_passive_queue_type               priority_queues
% 7.39/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.39/1.49  --inst_passive_queues_freq              [25;2]
% 7.39/1.49  --inst_dismatching                      true
% 7.39/1.49  --inst_eager_unprocessed_to_passive     true
% 7.39/1.49  --inst_prop_sim_given                   true
% 7.39/1.49  --inst_prop_sim_new                     false
% 7.39/1.49  --inst_subs_new                         false
% 7.39/1.49  --inst_eq_res_simp                      false
% 7.39/1.49  --inst_subs_given                       false
% 7.39/1.49  --inst_orphan_elimination               true
% 7.39/1.49  --inst_learning_loop_flag               true
% 7.39/1.49  --inst_learning_start                   3000
% 7.39/1.49  --inst_learning_factor                  2
% 7.39/1.49  --inst_start_prop_sim_after_learn       3
% 7.39/1.49  --inst_sel_renew                        solver
% 7.39/1.49  --inst_lit_activity_flag                true
% 7.39/1.49  --inst_restr_to_given                   false
% 7.39/1.49  --inst_activity_threshold               500
% 7.39/1.49  --inst_out_proof                        true
% 7.39/1.49  
% 7.39/1.49  ------ Resolution Options
% 7.39/1.49  
% 7.39/1.49  --resolution_flag                       true
% 7.39/1.49  --res_lit_sel                           adaptive
% 7.39/1.49  --res_lit_sel_side                      none
% 7.39/1.49  --res_ordering                          kbo
% 7.39/1.49  --res_to_prop_solver                    active
% 7.39/1.49  --res_prop_simpl_new                    false
% 7.39/1.49  --res_prop_simpl_given                  true
% 7.39/1.49  --res_passive_queue_type                priority_queues
% 7.39/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.39/1.49  --res_passive_queues_freq               [15;5]
% 7.39/1.49  --res_forward_subs                      full
% 7.39/1.49  --res_backward_subs                     full
% 7.39/1.49  --res_forward_subs_resolution           true
% 7.39/1.49  --res_backward_subs_resolution          true
% 7.39/1.49  --res_orphan_elimination                true
% 7.39/1.49  --res_time_limit                        2.
% 7.39/1.49  --res_out_proof                         true
% 7.39/1.49  
% 7.39/1.49  ------ Superposition Options
% 7.39/1.49  
% 7.39/1.49  --superposition_flag                    true
% 7.39/1.49  --sup_passive_queue_type                priority_queues
% 7.39/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.39/1.49  --sup_passive_queues_freq               [1;4]
% 7.39/1.49  --demod_completeness_check              fast
% 7.39/1.49  --demod_use_ground                      true
% 7.39/1.49  --sup_to_prop_solver                    passive
% 7.39/1.49  --sup_prop_simpl_new                    true
% 7.39/1.49  --sup_prop_simpl_given                  true
% 7.39/1.49  --sup_fun_splitting                     false
% 7.39/1.49  --sup_smt_interval                      50000
% 7.39/1.49  
% 7.39/1.49  ------ Superposition Simplification Setup
% 7.39/1.49  
% 7.39/1.49  --sup_indices_passive                   []
% 7.39/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.39/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.39/1.49  --sup_full_bw                           [BwDemod]
% 7.39/1.49  --sup_immed_triv                        [TrivRules]
% 7.39/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.39/1.49  --sup_immed_bw_main                     []
% 7.39/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.39/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.39/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.39/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.39/1.49  
% 7.39/1.49  ------ Combination Options
% 7.39/1.49  
% 7.39/1.49  --comb_res_mult                         3
% 7.39/1.49  --comb_sup_mult                         2
% 7.39/1.49  --comb_inst_mult                        10
% 7.39/1.49  
% 7.39/1.49  ------ Debug Options
% 7.39/1.49  
% 7.39/1.49  --dbg_backtrace                         false
% 7.39/1.49  --dbg_dump_prop_clauses                 false
% 7.39/1.49  --dbg_dump_prop_clauses_file            -
% 7.39/1.49  --dbg_out_stat                          false
% 7.39/1.49  ------ Parsing...
% 7.39/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.39/1.49  
% 7.39/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.39/1.49  
% 7.39/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.39/1.49  
% 7.39/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.39/1.49  ------ Proving...
% 7.39/1.49  ------ Problem Properties 
% 7.39/1.49  
% 7.39/1.49  
% 7.39/1.49  clauses                                 18
% 7.39/1.49  conjectures                             4
% 7.39/1.49  EPR                                     4
% 7.39/1.49  Horn                                    14
% 7.39/1.49  unary                                   6
% 7.39/1.49  binary                                  10
% 7.39/1.49  lits                                    32
% 7.39/1.49  lits eq                                 6
% 7.39/1.49  fd_pure                                 0
% 7.39/1.49  fd_pseudo                               0
% 7.39/1.49  fd_cond                                 0
% 7.39/1.49  fd_pseudo_cond                          0
% 7.39/1.49  AC symbols                              0
% 7.39/1.49  
% 7.39/1.49  ------ Input Options Time Limit: Unbounded
% 7.39/1.49  
% 7.39/1.49  
% 7.39/1.49  ------ 
% 7.39/1.49  Current options:
% 7.39/1.49  ------ 
% 7.39/1.49  
% 7.39/1.49  ------ Input Options
% 7.39/1.49  
% 7.39/1.49  --out_options                           all
% 7.39/1.49  --tptp_safe_out                         true
% 7.39/1.49  --problem_path                          ""
% 7.39/1.49  --include_path                          ""
% 7.39/1.49  --clausifier                            res/vclausify_rel
% 7.39/1.49  --clausifier_options                    --mode clausify
% 7.39/1.49  --stdin                                 false
% 7.39/1.49  --stats_out                             sel
% 7.39/1.49  
% 7.39/1.49  ------ General Options
% 7.39/1.49  
% 7.39/1.49  --fof                                   false
% 7.39/1.49  --time_out_real                         604.99
% 7.39/1.49  --time_out_virtual                      -1.
% 7.39/1.49  --symbol_type_check                     false
% 7.39/1.49  --clausify_out                          false
% 7.39/1.49  --sig_cnt_out                           false
% 7.39/1.49  --trig_cnt_out                          false
% 7.39/1.49  --trig_cnt_out_tolerance                1.
% 7.39/1.49  --trig_cnt_out_sk_spl                   false
% 7.39/1.49  --abstr_cl_out                          false
% 7.39/1.49  
% 7.39/1.49  ------ Global Options
% 7.39/1.49  
% 7.39/1.49  --schedule                              none
% 7.39/1.49  --add_important_lit                     false
% 7.39/1.49  --prop_solver_per_cl                    1000
% 7.39/1.49  --min_unsat_core                        false
% 7.39/1.49  --soft_assumptions                      false
% 7.39/1.49  --soft_lemma_size                       3
% 7.39/1.49  --prop_impl_unit_size                   0
% 7.39/1.49  --prop_impl_unit                        []
% 7.39/1.49  --share_sel_clauses                     true
% 7.39/1.49  --reset_solvers                         false
% 7.39/1.49  --bc_imp_inh                            [conj_cone]
% 7.39/1.49  --conj_cone_tolerance                   3.
% 7.39/1.49  --extra_neg_conj                        none
% 7.39/1.49  --large_theory_mode                     true
% 7.39/1.49  --prolific_symb_bound                   200
% 7.39/1.49  --lt_threshold                          2000
% 7.39/1.49  --clause_weak_htbl                      true
% 7.39/1.49  --gc_record_bc_elim                     false
% 7.39/1.49  
% 7.39/1.49  ------ Preprocessing Options
% 7.39/1.49  
% 7.39/1.49  --preprocessing_flag                    true
% 7.39/1.49  --time_out_prep_mult                    0.1
% 7.39/1.49  --splitting_mode                        input
% 7.39/1.49  --splitting_grd                         true
% 7.39/1.49  --splitting_cvd                         false
% 7.39/1.49  --splitting_cvd_svl                     false
% 7.39/1.49  --splitting_nvd                         32
% 7.39/1.49  --sub_typing                            true
% 7.39/1.49  --prep_gs_sim                           false
% 7.39/1.49  --prep_unflatten                        true
% 7.39/1.49  --prep_res_sim                          true
% 7.39/1.49  --prep_upred                            true
% 7.39/1.49  --prep_sem_filter                       exhaustive
% 7.39/1.49  --prep_sem_filter_out                   false
% 7.39/1.49  --pred_elim                             false
% 7.39/1.49  --res_sim_input                         true
% 7.39/1.49  --eq_ax_congr_red                       true
% 7.39/1.49  --pure_diseq_elim                       true
% 7.39/1.49  --brand_transform                       false
% 7.39/1.49  --non_eq_to_eq                          false
% 7.39/1.49  --prep_def_merge                        true
% 7.39/1.49  --prep_def_merge_prop_impl              false
% 7.39/1.49  --prep_def_merge_mbd                    true
% 7.39/1.49  --prep_def_merge_tr_red                 false
% 7.39/1.49  --prep_def_merge_tr_cl                  false
% 7.39/1.49  --smt_preprocessing                     true
% 7.39/1.49  --smt_ac_axioms                         fast
% 7.39/1.49  --preprocessed_out                      false
% 7.39/1.49  --preprocessed_stats                    false
% 7.39/1.49  
% 7.39/1.49  ------ Abstraction refinement Options
% 7.39/1.49  
% 7.39/1.49  --abstr_ref                             []
% 7.39/1.49  --abstr_ref_prep                        false
% 7.39/1.49  --abstr_ref_until_sat                   false
% 7.39/1.49  --abstr_ref_sig_restrict                funpre
% 7.39/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.39/1.49  --abstr_ref_under                       []
% 7.39/1.49  
% 7.39/1.49  ------ SAT Options
% 7.39/1.49  
% 7.39/1.49  --sat_mode                              false
% 7.39/1.49  --sat_fm_restart_options                ""
% 7.39/1.49  --sat_gr_def                            false
% 7.39/1.49  --sat_epr_types                         true
% 7.39/1.49  --sat_non_cyclic_types                  false
% 7.39/1.49  --sat_finite_models                     false
% 7.39/1.49  --sat_fm_lemmas                         false
% 7.39/1.49  --sat_fm_prep                           false
% 7.39/1.49  --sat_fm_uc_incr                        true
% 7.39/1.49  --sat_out_model                         small
% 7.39/1.49  --sat_out_clauses                       false
% 7.39/1.49  
% 7.39/1.49  ------ QBF Options
% 7.39/1.49  
% 7.39/1.49  --qbf_mode                              false
% 7.39/1.49  --qbf_elim_univ                         false
% 7.39/1.49  --qbf_dom_inst                          none
% 7.39/1.49  --qbf_dom_pre_inst                      false
% 7.39/1.49  --qbf_sk_in                             false
% 7.39/1.49  --qbf_pred_elim                         true
% 7.39/1.49  --qbf_split                             512
% 7.39/1.49  
% 7.39/1.49  ------ BMC1 Options
% 7.39/1.49  
% 7.39/1.49  --bmc1_incremental                      false
% 7.39/1.49  --bmc1_axioms                           reachable_all
% 7.39/1.49  --bmc1_min_bound                        0
% 7.39/1.49  --bmc1_max_bound                        -1
% 7.39/1.49  --bmc1_max_bound_default                -1
% 7.39/1.49  --bmc1_symbol_reachability              true
% 7.39/1.49  --bmc1_property_lemmas                  false
% 7.39/1.49  --bmc1_k_induction                      false
% 7.39/1.49  --bmc1_non_equiv_states                 false
% 7.39/1.49  --bmc1_deadlock                         false
% 7.39/1.49  --bmc1_ucm                              false
% 7.39/1.49  --bmc1_add_unsat_core                   none
% 7.39/1.49  --bmc1_unsat_core_children              false
% 7.39/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.39/1.49  --bmc1_out_stat                         full
% 7.39/1.49  --bmc1_ground_init                      false
% 7.39/1.49  --bmc1_pre_inst_next_state              false
% 7.39/1.49  --bmc1_pre_inst_state                   false
% 7.39/1.49  --bmc1_pre_inst_reach_state             false
% 7.39/1.49  --bmc1_out_unsat_core                   false
% 7.39/1.49  --bmc1_aig_witness_out                  false
% 7.39/1.49  --bmc1_verbose                          false
% 7.39/1.49  --bmc1_dump_clauses_tptp                false
% 7.39/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.39/1.49  --bmc1_dump_file                        -
% 7.39/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.39/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.39/1.49  --bmc1_ucm_extend_mode                  1
% 7.39/1.49  --bmc1_ucm_init_mode                    2
% 7.39/1.49  --bmc1_ucm_cone_mode                    none
% 7.39/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.39/1.49  --bmc1_ucm_relax_model                  4
% 7.39/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.39/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.39/1.49  --bmc1_ucm_layered_model                none
% 7.39/1.49  --bmc1_ucm_max_lemma_size               10
% 7.39/1.49  
% 7.39/1.49  ------ AIG Options
% 7.39/1.49  
% 7.39/1.49  --aig_mode                              false
% 7.39/1.49  
% 7.39/1.49  ------ Instantiation Options
% 7.39/1.49  
% 7.39/1.49  --instantiation_flag                    true
% 7.39/1.49  --inst_sos_flag                         false
% 7.39/1.49  --inst_sos_phase                        true
% 7.39/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.39/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.39/1.49  --inst_lit_sel_side                     num_symb
% 7.39/1.49  --inst_solver_per_active                1400
% 7.39/1.49  --inst_solver_calls_frac                1.
% 7.39/1.49  --inst_passive_queue_type               priority_queues
% 7.39/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.39/1.49  --inst_passive_queues_freq              [25;2]
% 7.39/1.49  --inst_dismatching                      true
% 7.39/1.49  --inst_eager_unprocessed_to_passive     true
% 7.39/1.49  --inst_prop_sim_given                   true
% 7.39/1.49  --inst_prop_sim_new                     false
% 7.39/1.49  --inst_subs_new                         false
% 7.39/1.49  --inst_eq_res_simp                      false
% 7.39/1.49  --inst_subs_given                       false
% 7.39/1.49  --inst_orphan_elimination               true
% 7.39/1.49  --inst_learning_loop_flag               true
% 7.39/1.49  --inst_learning_start                   3000
% 7.39/1.49  --inst_learning_factor                  2
% 7.39/1.49  --inst_start_prop_sim_after_learn       3
% 7.39/1.49  --inst_sel_renew                        solver
% 7.39/1.49  --inst_lit_activity_flag                true
% 7.39/1.49  --inst_restr_to_given                   false
% 7.39/1.49  --inst_activity_threshold               500
% 7.39/1.49  --inst_out_proof                        true
% 7.39/1.49  
% 7.39/1.49  ------ Resolution Options
% 7.39/1.49  
% 7.39/1.49  --resolution_flag                       true
% 7.39/1.49  --res_lit_sel                           adaptive
% 7.39/1.49  --res_lit_sel_side                      none
% 7.39/1.49  --res_ordering                          kbo
% 7.39/1.49  --res_to_prop_solver                    active
% 7.39/1.49  --res_prop_simpl_new                    false
% 7.39/1.49  --res_prop_simpl_given                  true
% 7.39/1.50  --res_passive_queue_type                priority_queues
% 7.39/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.39/1.50  --res_passive_queues_freq               [15;5]
% 7.39/1.50  --res_forward_subs                      full
% 7.39/1.50  --res_backward_subs                     full
% 7.39/1.50  --res_forward_subs_resolution           true
% 7.39/1.50  --res_backward_subs_resolution          true
% 7.39/1.50  --res_orphan_elimination                true
% 7.39/1.50  --res_time_limit                        2.
% 7.39/1.50  --res_out_proof                         true
% 7.39/1.50  
% 7.39/1.50  ------ Superposition Options
% 7.39/1.50  
% 7.39/1.50  --superposition_flag                    true
% 7.39/1.50  --sup_passive_queue_type                priority_queues
% 7.39/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.39/1.50  --sup_passive_queues_freq               [1;4]
% 7.39/1.50  --demod_completeness_check              fast
% 7.39/1.50  --demod_use_ground                      true
% 7.39/1.50  --sup_to_prop_solver                    passive
% 7.39/1.50  --sup_prop_simpl_new                    true
% 7.39/1.50  --sup_prop_simpl_given                  true
% 7.39/1.50  --sup_fun_splitting                     false
% 7.39/1.50  --sup_smt_interval                      50000
% 7.39/1.50  
% 7.39/1.50  ------ Superposition Simplification Setup
% 7.39/1.50  
% 7.39/1.50  --sup_indices_passive                   []
% 7.39/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.39/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.39/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.39/1.50  --sup_full_bw                           [BwDemod]
% 7.39/1.50  --sup_immed_triv                        [TrivRules]
% 7.39/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.39/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.39/1.50  --sup_immed_bw_main                     []
% 7.39/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.39/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.39/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.39/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.39/1.50  
% 7.39/1.50  ------ Combination Options
% 7.39/1.50  
% 7.39/1.50  --comb_res_mult                         3
% 7.39/1.50  --comb_sup_mult                         2
% 7.39/1.50  --comb_inst_mult                        10
% 7.39/1.50  
% 7.39/1.50  ------ Debug Options
% 7.39/1.50  
% 7.39/1.50  --dbg_backtrace                         false
% 7.39/1.50  --dbg_dump_prop_clauses                 false
% 7.39/1.50  --dbg_dump_prop_clauses_file            -
% 7.39/1.50  --dbg_out_stat                          false
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  ------ Proving...
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  % SZS status Theorem for theBenchmark.p
% 7.39/1.50  
% 7.39/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.39/1.50  
% 7.39/1.50  fof(f16,conjecture,(
% 7.39/1.50    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.39/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f17,negated_conjecture,(
% 7.39/1.50    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 7.39/1.50    inference(negated_conjecture,[],[f16])).
% 7.39/1.50  
% 7.39/1.50  fof(f27,plain,(
% 7.39/1.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 7.39/1.50    inference(ennf_transformation,[],[f17])).
% 7.39/1.50  
% 7.39/1.50  fof(f28,plain,(
% 7.39/1.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 7.39/1.50    inference(flattening,[],[f27])).
% 7.39/1.50  
% 7.39/1.50  fof(f34,plain,(
% 7.39/1.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 7.39/1.50    introduced(choice_axiom,[])).
% 7.39/1.50  
% 7.39/1.50  fof(f35,plain,(
% 7.39/1.50    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 7.39/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f34])).
% 7.39/1.50  
% 7.39/1.50  fof(f55,plain,(
% 7.39/1.50    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 7.39/1.50    inference(cnf_transformation,[],[f35])).
% 7.39/1.50  
% 7.39/1.50  fof(f12,axiom,(
% 7.39/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.39/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f51,plain,(
% 7.39/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f12])).
% 7.39/1.50  
% 7.39/1.50  fof(f13,axiom,(
% 7.39/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.39/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f52,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f13])).
% 7.39/1.50  
% 7.39/1.50  fof(f14,axiom,(
% 7.39/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.39/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f53,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f14])).
% 7.39/1.50  
% 7.39/1.50  fof(f60,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.39/1.50    inference(definition_unfolding,[],[f52,f53])).
% 7.39/1.50  
% 7.39/1.50  fof(f61,plain,(
% 7.39/1.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.39/1.50    inference(definition_unfolding,[],[f51,f60])).
% 7.39/1.50  
% 7.39/1.50  fof(f66,plain,(
% 7.39/1.50    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))),
% 7.39/1.50    inference(definition_unfolding,[],[f55,f61])).
% 7.39/1.50  
% 7.39/1.50  fof(f8,axiom,(
% 7.39/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.39/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f23,plain,(
% 7.39/1.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.39/1.50    inference(ennf_transformation,[],[f8])).
% 7.39/1.50  
% 7.39/1.50  fof(f47,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f23])).
% 7.39/1.50  
% 7.39/1.50  fof(f2,axiom,(
% 7.39/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.39/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f37,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f2])).
% 7.39/1.50  
% 7.39/1.50  fof(f9,axiom,(
% 7.39/1.50    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 7.39/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f24,plain,(
% 7.39/1.50    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 7.39/1.50    inference(ennf_transformation,[],[f9])).
% 7.39/1.50  
% 7.39/1.50  fof(f48,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 7.39/1.50    inference(cnf_transformation,[],[f24])).
% 7.39/1.50  
% 7.39/1.50  fof(f6,axiom,(
% 7.39/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.39/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f19,plain,(
% 7.39/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.39/1.50    inference(rectify,[],[f6])).
% 7.39/1.50  
% 7.39/1.50  fof(f22,plain,(
% 7.39/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.39/1.50    inference(ennf_transformation,[],[f19])).
% 7.39/1.50  
% 7.39/1.50  fof(f32,plain,(
% 7.39/1.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 7.39/1.50    introduced(choice_axiom,[])).
% 7.39/1.50  
% 7.39/1.50  fof(f33,plain,(
% 7.39/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.39/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f32])).
% 7.39/1.50  
% 7.39/1.50  fof(f45,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.39/1.50    inference(cnf_transformation,[],[f33])).
% 7.39/1.50  
% 7.39/1.50  fof(f5,axiom,(
% 7.39/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.39/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f18,plain,(
% 7.39/1.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.39/1.50    inference(rectify,[],[f5])).
% 7.39/1.50  
% 7.39/1.50  fof(f21,plain,(
% 7.39/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.39/1.50    inference(ennf_transformation,[],[f18])).
% 7.39/1.50  
% 7.39/1.50  fof(f30,plain,(
% 7.39/1.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.39/1.50    introduced(choice_axiom,[])).
% 7.39/1.50  
% 7.39/1.50  fof(f31,plain,(
% 7.39/1.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.39/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f30])).
% 7.39/1.50  
% 7.39/1.50  fof(f41,plain,(
% 7.39/1.50    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f31])).
% 7.39/1.50  
% 7.39/1.50  fof(f56,plain,(
% 7.39/1.50    r2_hidden(sK5,sK4)),
% 7.39/1.50    inference(cnf_transformation,[],[f35])).
% 7.39/1.50  
% 7.39/1.50  fof(f57,plain,(
% 7.39/1.50    r1_xboole_0(sK4,sK3)),
% 7.39/1.50    inference(cnf_transformation,[],[f35])).
% 7.39/1.50  
% 7.39/1.50  fof(f43,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f31])).
% 7.39/1.50  
% 7.39/1.50  fof(f15,axiom,(
% 7.39/1.50    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 7.39/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f26,plain,(
% 7.39/1.50    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 7.39/1.50    inference(ennf_transformation,[],[f15])).
% 7.39/1.50  
% 7.39/1.50  fof(f54,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f26])).
% 7.39/1.50  
% 7.39/1.50  fof(f64,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 7.39/1.50    inference(definition_unfolding,[],[f54,f60])).
% 7.39/1.50  
% 7.39/1.50  fof(f4,axiom,(
% 7.39/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.39/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f20,plain,(
% 7.39/1.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.39/1.50    inference(ennf_transformation,[],[f4])).
% 7.39/1.50  
% 7.39/1.50  fof(f40,plain,(
% 7.39/1.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f20])).
% 7.39/1.50  
% 7.39/1.50  fof(f3,axiom,(
% 7.39/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.39/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f29,plain,(
% 7.39/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.39/1.50    inference(nnf_transformation,[],[f3])).
% 7.39/1.50  
% 7.39/1.50  fof(f38,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f29])).
% 7.39/1.50  
% 7.39/1.50  fof(f39,plain,(
% 7.39/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.39/1.50    inference(cnf_transformation,[],[f29])).
% 7.39/1.50  
% 7.39/1.50  fof(f10,axiom,(
% 7.39/1.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 7.39/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f25,plain,(
% 7.39/1.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 7.39/1.50    inference(ennf_transformation,[],[f10])).
% 7.39/1.50  
% 7.39/1.50  fof(f49,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 7.39/1.50    inference(cnf_transformation,[],[f25])).
% 7.39/1.50  
% 7.39/1.50  fof(f11,axiom,(
% 7.39/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.39/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f50,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.39/1.50    inference(cnf_transformation,[],[f11])).
% 7.39/1.50  
% 7.39/1.50  fof(f7,axiom,(
% 7.39/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.39/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.39/1.50  
% 7.39/1.50  fof(f46,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.39/1.50    inference(cnf_transformation,[],[f7])).
% 7.39/1.50  
% 7.39/1.50  fof(f59,plain,(
% 7.39/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 7.39/1.50    inference(definition_unfolding,[],[f50,f46])).
% 7.39/1.50  
% 7.39/1.50  fof(f63,plain,(
% 7.39/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) | ~r1_xboole_0(X0,X1)) )),
% 7.39/1.50    inference(definition_unfolding,[],[f49,f59])).
% 7.39/1.50  
% 7.39/1.50  fof(f58,plain,(
% 7.39/1.50    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 7.39/1.50    inference(cnf_transformation,[],[f35])).
% 7.39/1.50  
% 7.39/1.50  fof(f65,plain,(
% 7.39/1.50    ~r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3)),
% 7.39/1.50    inference(definition_unfolding,[],[f58,f59])).
% 7.39/1.50  
% 7.39/1.50  cnf(c_17,negated_conjecture,
% 7.39/1.50      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 7.39/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_187,negated_conjecture,
% 7.39/1.50      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_17]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_624,plain,
% 7.39/1.50      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_10,plain,
% 7.39/1.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.39/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_194,plain,
% 7.39/1.50      ( ~ r1_tarski(X0_41,X1_41) | k3_xboole_0(X0_41,X1_41) = X0_41 ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_617,plain,
% 7.39/1.50      ( k3_xboole_0(X0_41,X1_41) = X0_41
% 7.39/1.50      | r1_tarski(X0_41,X1_41) != iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_194]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1215,plain,
% 7.39/1.50      ( k3_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = k3_xboole_0(sK2,sK3) ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_624,c_617]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1,plain,
% 7.39/1.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.39/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_203,plain,
% 7.39/1.50      ( k3_xboole_0(X0_41,X1_41) = k3_xboole_0(X1_41,X0_41) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_11,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 7.39/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_193,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0_41,X1_41)
% 7.39/1.50      | r1_xboole_0(X0_41,k3_xboole_0(X1_41,X2_41)) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_11]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_618,plain,
% 7.39/1.50      ( r1_xboole_0(X0_41,X1_41) != iProver_top
% 7.39/1.50      | r1_xboole_0(X0_41,k3_xboole_0(X1_41,X2_41)) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1869,plain,
% 7.39/1.50      ( r1_xboole_0(X0_41,X1_41) != iProver_top
% 7.39/1.50      | r1_xboole_0(X0_41,k3_xboole_0(X2_41,X1_41)) = iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_203,c_618]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_3343,plain,
% 7.39/1.50      ( r1_xboole_0(X0_41,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 7.39/1.50      | r1_xboole_0(X0_41,k3_xboole_0(sK2,sK3)) = iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_1215,c_1869]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_208,plain,
% 7.39/1.50      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 7.39/1.50      theory(equality) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_206,plain,( X0_41 = X0_41 ),theory(equality) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1235,plain,
% 7.39/1.50      ( X0_41 != X1_41 | X1_41 = X0_41 ),
% 7.39/1.50      inference(resolution,[status(thm)],[c_208,c_206]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_2781,plain,
% 7.39/1.50      ( ~ r1_tarski(X0_41,X1_41) | X0_41 = k3_xboole_0(X0_41,X1_41) ),
% 7.39/1.50      inference(resolution,[status(thm)],[c_1235,c_194]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_211,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0_41,X1_41)
% 7.39/1.50      | r1_xboole_0(X2_41,X3_41)
% 7.39/1.50      | X2_41 != X0_41
% 7.39/1.50      | X3_41 != X1_41 ),
% 7.39/1.50      theory(equality) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1415,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0_41,X1_41)
% 7.39/1.50      | r1_xboole_0(X2_41,X1_41)
% 7.39/1.50      | X2_41 != X0_41 ),
% 7.39/1.50      inference(resolution,[status(thm)],[c_211,c_206]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_2803,plain,
% 7.39/1.50      ( ~ r1_tarski(X0_41,X1_41)
% 7.39/1.50      | r1_xboole_0(X0_41,X2_41)
% 7.39/1.50      | ~ r1_xboole_0(k3_xboole_0(X0_41,X1_41),X2_41) ),
% 7.39/1.50      inference(resolution,[status(thm)],[c_2781,c_1415]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_8,plain,
% 7.39/1.50      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 7.39/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_196,plain,
% 7.39/1.50      ( ~ r2_hidden(X0_42,k3_xboole_0(X0_41,X1_41))
% 7.39/1.50      | ~ r1_xboole_0(X0_41,X1_41) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_7,plain,
% 7.39/1.50      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 7.39/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_197,plain,
% 7.39/1.50      ( r2_hidden(sK0(X0_41,X1_41),X0_41) | r1_xboole_0(X0_41,X1_41) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1061,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0_41,X1_41)
% 7.39/1.50      | r1_xboole_0(k3_xboole_0(X0_41,X1_41),X2_41) ),
% 7.39/1.50      inference(resolution,[status(thm)],[c_196,c_197]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_4757,plain,
% 7.39/1.50      ( ~ r1_tarski(X0_41,X1_41)
% 7.39/1.50      | ~ r1_xboole_0(X0_41,X1_41)
% 7.39/1.50      | r1_xboole_0(X0_41,X2_41) ),
% 7.39/1.50      inference(resolution,[status(thm)],[c_2803,c_1061]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_4784,plain,
% 7.39/1.50      ( r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41)
% 7.39/1.50      | ~ r1_xboole_0(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 7.39/1.50      inference(resolution,[status(thm)],[c_4757,c_187]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_4798,plain,
% 7.39/1.50      ( r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41)
% 7.39/1.50      | ~ r1_xboole_0(sK2,sK3) ),
% 7.39/1.50      inference(resolution,[status(thm)],[c_4784,c_1061]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_16,negated_conjecture,
% 7.39/1.50      ( r2_hidden(sK5,sK4) ),
% 7.39/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_15,negated_conjecture,
% 7.39/1.50      ( r1_xboole_0(sK4,sK3) ),
% 7.39/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_5,plain,
% 7.39/1.50      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 7.39/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_199,plain,
% 7.39/1.50      ( ~ r2_hidden(X0_42,X0_41)
% 7.39/1.50      | ~ r2_hidden(X0_42,X1_41)
% 7.39/1.50      | ~ r1_xboole_0(X0_41,X1_41) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_798,plain,
% 7.39/1.50      ( ~ r2_hidden(X0_42,sK3)
% 7.39/1.50      | ~ r2_hidden(X0_42,sK4)
% 7.39/1.50      | ~ r1_xboole_0(sK4,sK3) ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_199]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_800,plain,
% 7.39/1.50      ( ~ r2_hidden(sK5,sK3)
% 7.39/1.50      | ~ r2_hidden(sK5,sK4)
% 7.39/1.50      | ~ r1_xboole_0(sK4,sK3) ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_798]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_13,plain,
% 7.39/1.50      ( r2_hidden(X0,X1)
% 7.39/1.50      | r2_hidden(X2,X1)
% 7.39/1.50      | r1_xboole_0(k2_enumset1(X2,X2,X2,X0),X1) ),
% 7.39/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_191,plain,
% 7.39/1.50      ( r2_hidden(X0_42,X0_41)
% 7.39/1.50      | r2_hidden(X1_42,X0_41)
% 7.39/1.50      | r1_xboole_0(k2_enumset1(X1_42,X1_42,X1_42,X0_42),X0_41) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_934,plain,
% 7.39/1.50      ( r2_hidden(X0_42,sK3)
% 7.39/1.50      | r2_hidden(X1_42,sK3)
% 7.39/1.50      | r1_xboole_0(k2_enumset1(X1_42,X1_42,X1_42,X0_42),sK3) ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_191]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_936,plain,
% 7.39/1.50      ( r2_hidden(sK5,sK3)
% 7.39/1.50      | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3) ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_934]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1927,plain,
% 7.39/1.50      ( ~ r1_xboole_0(k3_xboole_0(X0_41,X1_41),X2_41)
% 7.39/1.50      | r1_xboole_0(k3_xboole_0(X1_41,X0_41),X2_41) ),
% 7.39/1.50      inference(resolution,[status(thm)],[c_1415,c_203]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_4,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.39/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_200,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0_41,X1_41) | r1_xboole_0(X1_41,X0_41) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_887,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0_41,X1_41)
% 7.39/1.50      | r1_xboole_0(k3_xboole_0(X1_41,X2_41),X0_41) ),
% 7.39/1.50      inference(resolution,[status(thm)],[c_193,c_200]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_1942,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0_41,X1_41)
% 7.39/1.50      | r1_xboole_0(k3_xboole_0(X2_41,X1_41),X0_41) ),
% 7.39/1.50      inference(resolution,[status(thm)],[c_1927,c_887]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_4810,plain,
% 7.39/1.50      ( ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK3)
% 7.39/1.50      | r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41) ),
% 7.39/1.50      inference(resolution,[status(thm)],[c_4784,c_1942]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_5060,plain,
% 7.39/1.50      ( r1_xboole_0(k3_xboole_0(sK2,sK3),X0_41) ),
% 7.39/1.50      inference(global_propositional_subsumption,
% 7.39/1.50                [status(thm)],
% 7.39/1.50                [c_4798,c_16,c_15,c_800,c_936,c_4810]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_5074,plain,
% 7.39/1.50      ( r1_xboole_0(X0_41,k3_xboole_0(sK2,sK3)) ),
% 7.39/1.50      inference(resolution,[status(thm)],[c_5060,c_200]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_5079,plain,
% 7.39/1.50      ( r1_xboole_0(X0_41,k3_xboole_0(sK2,sK3)) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_5074]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_21162,plain,
% 7.39/1.50      ( r1_xboole_0(X0_41,k3_xboole_0(sK2,sK3)) = iProver_top ),
% 7.39/1.50      inference(global_propositional_subsumption,
% 7.39/1.50                [status(thm)],
% 7.39/1.50                [c_3343,c_5079]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_3,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.39/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_201,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0_41,X1_41)
% 7.39/1.50      | k3_xboole_0(X0_41,X1_41) = k1_xboole_0 ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_610,plain,
% 7.39/1.50      ( k3_xboole_0(X0_41,X1_41) = k1_xboole_0
% 7.39/1.50      | r1_xboole_0(X0_41,X1_41) != iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_201]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_21172,plain,
% 7.39/1.50      ( k3_xboole_0(X0_41,k3_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_21162,c_610]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_21274,plain,
% 7.39/1.50      ( k3_xboole_0(k3_xboole_0(sK2,sK3),X0_41) = k1_xboole_0 ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_21172,c_203]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_21671,plain,
% 7.39/1.50      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.39/1.50      inference(demodulation,[status(thm)],[c_21274,c_1215]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_2,plain,
% 7.39/1.50      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.39/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_202,plain,
% 7.39/1.50      ( r1_xboole_0(X0_41,X1_41)
% 7.39/1.50      | k3_xboole_0(X0_41,X1_41) != k1_xboole_0 ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_609,plain,
% 7.39/1.50      ( k3_xboole_0(X0_41,X1_41) != k1_xboole_0
% 7.39/1.50      | r1_xboole_0(X0_41,X1_41) = iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_202]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_878,plain,
% 7.39/1.50      ( k3_xboole_0(X0_41,X1_41) != k1_xboole_0
% 7.39/1.50      | r1_xboole_0(X1_41,X0_41) = iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_203,c_609]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_21770,plain,
% 7.39/1.50      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_21671,c_878]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_12,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.39/1.50      | k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_xboole_0(X0,X2) ),
% 7.39/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_192,plain,
% 7.39/1.50      ( ~ r1_xboole_0(X0_41,X1_41)
% 7.39/1.50      | k3_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X2_41,X1_41)))) = k3_xboole_0(X0_41,X2_41) ),
% 7.39/1.50      inference(subtyping,[status(esa)],[c_12]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_619,plain,
% 7.39/1.50      ( k3_xboole_0(X0_41,k5_xboole_0(X1_41,k5_xboole_0(X2_41,k3_xboole_0(X2_41,X1_41)))) = k3_xboole_0(X0_41,X2_41)
% 7.39/1.50      | r1_xboole_0(X0_41,X1_41) != iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_22163,plain,
% 7.39/1.50      ( k3_xboole_0(sK3,k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2)))) = k3_xboole_0(sK3,X0_41) ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_21770,c_619]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_23135,plain,
% 7.39/1.50      ( k3_xboole_0(sK3,X0_41) != k1_xboole_0
% 7.39/1.50      | r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(X0_41,k3_xboole_0(X0_41,sK2))),sK3) = iProver_top ),
% 7.39/1.50      inference(superposition,[status(thm)],[c_22163,c_878]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_23324,plain,
% 7.39/1.50      ( k3_xboole_0(sK3,sK4) != k1_xboole_0
% 7.39/1.50      | r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) = iProver_top ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_23135]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_852,plain,
% 7.39/1.50      ( ~ r1_xboole_0(sK3,sK4) | k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_201]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_736,plain,
% 7.39/1.50      ( r1_xboole_0(sK3,sK4) | ~ r1_xboole_0(sK4,sK3) ),
% 7.39/1.50      inference(instantiation,[status(thm)],[c_200]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_14,negated_conjecture,
% 7.39/1.50      ( ~ r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) ),
% 7.39/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(c_21,plain,
% 7.39/1.50      ( r1_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK4,k3_xboole_0(sK4,sK2))),sK3) != iProver_top ),
% 7.39/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.39/1.50  
% 7.39/1.50  cnf(contradiction,plain,
% 7.39/1.50      ( $false ),
% 7.39/1.50      inference(minisat,[status(thm)],[c_23324,c_852,c_736,c_21,c_15]) ).
% 7.39/1.50  
% 7.39/1.50  
% 7.39/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.39/1.50  
% 7.39/1.50  ------                               Statistics
% 7.39/1.50  
% 7.39/1.50  ------ Selected
% 7.39/1.50  
% 7.39/1.50  total_time:                             0.704
% 7.39/1.50  
%------------------------------------------------------------------------------
