%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:10 EST 2020

% Result     : Theorem 6.42s
% Output     : CNFRefutation 6.42s
% Verified   : 
% Statistics : Number of formulae       :  102 (3845 expanded)
%              Number of clauses        :   50 ( 568 expanded)
%              Number of leaves         :   16 (1241 expanded)
%              Depth                    :   21
%              Number of atoms          :  135 (4063 expanded)
%              Number of equality atoms :   91 (3748 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f35,f29])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f46])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f45,f47])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f36,f47,f47])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) ),
    inference(definition_unfolding,[],[f33,f29,f29,f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK0),sK1) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).

fof(f43,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f30,f45])).

fof(f44,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(definition_unfolding,[],[f44,f45,f48])).

cnf(c_10,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_8,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_239,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_240,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_354,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_239,c_240])).

cnf(c_1260,plain,
    ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_354])).

cnf(c_2292,plain,
    ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_1260])).

cnf(c_2469,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_2292])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_780,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_6,c_6])).

cnf(c_10850,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_780,c_2469])).

cnf(c_10907,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,X1)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,X1)),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_2469,c_10850])).

cnf(c_629,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_8,c_10])).

cnf(c_3218,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_629,c_10])).

cnf(c_10973,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_10850,c_3218])).

cnf(c_10980,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,X1)) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,X0)) ),
    inference(demodulation,[status(thm)],[c_10973,c_10850])).

cnf(c_4418,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X0))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_2469,c_3218])).

cnf(c_4458,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_4418,c_6])).

cnf(c_10982,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_10980,c_4458])).

cnf(c_10926,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_6,c_10850])).

cnf(c_10966,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,X0)))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_10850,c_10850])).

cnf(c_11002,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_10966,c_10850,c_10982])).

cnf(c_11076,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_10926,c_11002])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_241,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_353,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_241,c_240])).

cnf(c_11078,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_11076,c_353,c_2469,c_4458])).

cnf(c_11157,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))))) = k5_xboole_0(X1,X1) ),
    inference(light_normalisation,[status(thm)],[c_10907,c_10982,c_11078])).

cnf(c_11159,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(X1,X1) ),
    inference(light_normalisation,[status(thm)],[c_11157,c_6,c_10850])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_91,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_12])).

cnf(c_92,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unflattening,[status(thm)],[c_91])).

cnf(c_238,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_92])).

cnf(c_355,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_238,c_240])).

cnf(c_633,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_355,c_10])).

cnf(c_11376,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_11159,c_633])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_634,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_3])).

cnf(c_1392,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_634])).

cnf(c_9133,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X1,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_10,c_4458])).

cnf(c_9372,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_1392,c_9133])).

cnf(c_9380,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_9372,c_3])).

cnf(c_11379,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_11159,c_9380])).

cnf(c_11457,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_11376,c_11379])).

cnf(c_11,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3191,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(demodulation,[status(thm)],[c_629,c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11457,c_3191])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:52:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 6.42/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.42/1.50  
% 6.42/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.42/1.50  
% 6.42/1.50  ------  iProver source info
% 6.42/1.50  
% 6.42/1.50  git: date: 2020-06-30 10:37:57 +0100
% 6.42/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.42/1.50  git: non_committed_changes: false
% 6.42/1.50  git: last_make_outside_of_git: false
% 6.42/1.50  
% 6.42/1.50  ------ 
% 6.42/1.50  
% 6.42/1.50  ------ Input Options
% 6.42/1.50  
% 6.42/1.50  --out_options                           all
% 6.42/1.50  --tptp_safe_out                         true
% 6.42/1.50  --problem_path                          ""
% 6.42/1.50  --include_path                          ""
% 6.42/1.50  --clausifier                            res/vclausify_rel
% 6.42/1.50  --clausifier_options                    --mode clausify
% 6.42/1.50  --stdin                                 false
% 6.42/1.50  --stats_out                             all
% 6.42/1.50  
% 6.42/1.50  ------ General Options
% 6.42/1.50  
% 6.42/1.50  --fof                                   false
% 6.42/1.50  --time_out_real                         305.
% 6.42/1.50  --time_out_virtual                      -1.
% 6.42/1.50  --symbol_type_check                     false
% 6.42/1.50  --clausify_out                          false
% 6.42/1.50  --sig_cnt_out                           false
% 6.42/1.50  --trig_cnt_out                          false
% 6.42/1.50  --trig_cnt_out_tolerance                1.
% 6.42/1.50  --trig_cnt_out_sk_spl                   false
% 6.42/1.50  --abstr_cl_out                          false
% 6.42/1.50  
% 6.42/1.50  ------ Global Options
% 6.42/1.50  
% 6.42/1.50  --schedule                              default
% 6.42/1.50  --add_important_lit                     false
% 6.42/1.50  --prop_solver_per_cl                    1000
% 6.42/1.50  --min_unsat_core                        false
% 6.42/1.50  --soft_assumptions                      false
% 6.42/1.50  --soft_lemma_size                       3
% 6.42/1.50  --prop_impl_unit_size                   0
% 6.42/1.50  --prop_impl_unit                        []
% 6.42/1.50  --share_sel_clauses                     true
% 6.42/1.50  --reset_solvers                         false
% 6.42/1.50  --bc_imp_inh                            [conj_cone]
% 6.42/1.50  --conj_cone_tolerance                   3.
% 6.42/1.50  --extra_neg_conj                        none
% 6.42/1.50  --large_theory_mode                     true
% 6.42/1.50  --prolific_symb_bound                   200
% 6.42/1.50  --lt_threshold                          2000
% 6.42/1.50  --clause_weak_htbl                      true
% 6.42/1.50  --gc_record_bc_elim                     false
% 6.42/1.50  
% 6.42/1.50  ------ Preprocessing Options
% 6.42/1.50  
% 6.42/1.50  --preprocessing_flag                    true
% 6.42/1.50  --time_out_prep_mult                    0.1
% 6.42/1.50  --splitting_mode                        input
% 6.42/1.50  --splitting_grd                         true
% 6.42/1.50  --splitting_cvd                         false
% 6.42/1.50  --splitting_cvd_svl                     false
% 6.42/1.50  --splitting_nvd                         32
% 6.42/1.50  --sub_typing                            true
% 6.42/1.50  --prep_gs_sim                           true
% 6.42/1.50  --prep_unflatten                        true
% 6.42/1.50  --prep_res_sim                          true
% 6.42/1.50  --prep_upred                            true
% 6.42/1.50  --prep_sem_filter                       exhaustive
% 6.42/1.50  --prep_sem_filter_out                   false
% 6.42/1.50  --pred_elim                             true
% 6.42/1.50  --res_sim_input                         true
% 6.42/1.50  --eq_ax_congr_red                       true
% 6.42/1.50  --pure_diseq_elim                       true
% 6.42/1.50  --brand_transform                       false
% 6.42/1.50  --non_eq_to_eq                          false
% 6.42/1.50  --prep_def_merge                        true
% 6.42/1.50  --prep_def_merge_prop_impl              false
% 6.42/1.50  --prep_def_merge_mbd                    true
% 6.42/1.50  --prep_def_merge_tr_red                 false
% 6.42/1.50  --prep_def_merge_tr_cl                  false
% 6.42/1.50  --smt_preprocessing                     true
% 6.42/1.50  --smt_ac_axioms                         fast
% 6.42/1.50  --preprocessed_out                      false
% 6.42/1.50  --preprocessed_stats                    false
% 6.42/1.50  
% 6.42/1.50  ------ Abstraction refinement Options
% 6.42/1.50  
% 6.42/1.50  --abstr_ref                             []
% 6.42/1.50  --abstr_ref_prep                        false
% 6.42/1.50  --abstr_ref_until_sat                   false
% 6.42/1.50  --abstr_ref_sig_restrict                funpre
% 6.42/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.42/1.50  --abstr_ref_under                       []
% 6.42/1.50  
% 6.42/1.50  ------ SAT Options
% 6.42/1.50  
% 6.42/1.50  --sat_mode                              false
% 6.42/1.50  --sat_fm_restart_options                ""
% 6.42/1.50  --sat_gr_def                            false
% 6.42/1.50  --sat_epr_types                         true
% 6.42/1.50  --sat_non_cyclic_types                  false
% 6.42/1.50  --sat_finite_models                     false
% 6.42/1.50  --sat_fm_lemmas                         false
% 6.42/1.50  --sat_fm_prep                           false
% 6.42/1.50  --sat_fm_uc_incr                        true
% 6.42/1.50  --sat_out_model                         small
% 6.42/1.50  --sat_out_clauses                       false
% 6.42/1.50  
% 6.42/1.50  ------ QBF Options
% 6.42/1.50  
% 6.42/1.50  --qbf_mode                              false
% 6.42/1.50  --qbf_elim_univ                         false
% 6.42/1.50  --qbf_dom_inst                          none
% 6.42/1.50  --qbf_dom_pre_inst                      false
% 6.42/1.50  --qbf_sk_in                             false
% 6.42/1.50  --qbf_pred_elim                         true
% 6.42/1.50  --qbf_split                             512
% 6.42/1.50  
% 6.42/1.50  ------ BMC1 Options
% 6.42/1.50  
% 6.42/1.50  --bmc1_incremental                      false
% 6.42/1.50  --bmc1_axioms                           reachable_all
% 6.42/1.50  --bmc1_min_bound                        0
% 6.42/1.50  --bmc1_max_bound                        -1
% 6.42/1.50  --bmc1_max_bound_default                -1
% 6.42/1.50  --bmc1_symbol_reachability              true
% 6.42/1.50  --bmc1_property_lemmas                  false
% 6.42/1.50  --bmc1_k_induction                      false
% 6.42/1.50  --bmc1_non_equiv_states                 false
% 6.42/1.50  --bmc1_deadlock                         false
% 6.42/1.50  --bmc1_ucm                              false
% 6.42/1.50  --bmc1_add_unsat_core                   none
% 6.42/1.50  --bmc1_unsat_core_children              false
% 6.42/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.42/1.50  --bmc1_out_stat                         full
% 6.42/1.50  --bmc1_ground_init                      false
% 6.42/1.50  --bmc1_pre_inst_next_state              false
% 6.42/1.50  --bmc1_pre_inst_state                   false
% 6.42/1.50  --bmc1_pre_inst_reach_state             false
% 6.42/1.50  --bmc1_out_unsat_core                   false
% 6.42/1.50  --bmc1_aig_witness_out                  false
% 6.42/1.50  --bmc1_verbose                          false
% 6.42/1.50  --bmc1_dump_clauses_tptp                false
% 6.42/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.42/1.50  --bmc1_dump_file                        -
% 6.42/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.42/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.42/1.50  --bmc1_ucm_extend_mode                  1
% 6.42/1.50  --bmc1_ucm_init_mode                    2
% 6.42/1.50  --bmc1_ucm_cone_mode                    none
% 6.42/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.42/1.50  --bmc1_ucm_relax_model                  4
% 6.42/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.42/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.42/1.50  --bmc1_ucm_layered_model                none
% 6.42/1.51  --bmc1_ucm_max_lemma_size               10
% 6.42/1.51  
% 6.42/1.51  ------ AIG Options
% 6.42/1.51  
% 6.42/1.51  --aig_mode                              false
% 6.42/1.51  
% 6.42/1.51  ------ Instantiation Options
% 6.42/1.51  
% 6.42/1.51  --instantiation_flag                    true
% 6.42/1.51  --inst_sos_flag                         false
% 6.42/1.51  --inst_sos_phase                        true
% 6.42/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.42/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.42/1.51  --inst_lit_sel_side                     num_symb
% 6.42/1.51  --inst_solver_per_active                1400
% 6.42/1.51  --inst_solver_calls_frac                1.
% 6.42/1.51  --inst_passive_queue_type               priority_queues
% 6.42/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.42/1.51  --inst_passive_queues_freq              [25;2]
% 6.42/1.51  --inst_dismatching                      true
% 6.42/1.51  --inst_eager_unprocessed_to_passive     true
% 6.42/1.51  --inst_prop_sim_given                   true
% 6.42/1.51  --inst_prop_sim_new                     false
% 6.42/1.51  --inst_subs_new                         false
% 6.42/1.51  --inst_eq_res_simp                      false
% 6.42/1.51  --inst_subs_given                       false
% 6.42/1.51  --inst_orphan_elimination               true
% 6.42/1.51  --inst_learning_loop_flag               true
% 6.42/1.51  --inst_learning_start                   3000
% 6.42/1.51  --inst_learning_factor                  2
% 6.42/1.51  --inst_start_prop_sim_after_learn       3
% 6.42/1.51  --inst_sel_renew                        solver
% 6.42/1.51  --inst_lit_activity_flag                true
% 6.42/1.51  --inst_restr_to_given                   false
% 6.42/1.51  --inst_activity_threshold               500
% 6.42/1.51  --inst_out_proof                        true
% 6.42/1.51  
% 6.42/1.51  ------ Resolution Options
% 6.42/1.51  
% 6.42/1.51  --resolution_flag                       true
% 6.42/1.51  --res_lit_sel                           adaptive
% 6.42/1.51  --res_lit_sel_side                      none
% 6.42/1.51  --res_ordering                          kbo
% 6.42/1.51  --res_to_prop_solver                    active
% 6.42/1.51  --res_prop_simpl_new                    false
% 6.42/1.51  --res_prop_simpl_given                  true
% 6.42/1.51  --res_passive_queue_type                priority_queues
% 6.42/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.42/1.51  --res_passive_queues_freq               [15;5]
% 6.42/1.51  --res_forward_subs                      full
% 6.42/1.51  --res_backward_subs                     full
% 6.42/1.51  --res_forward_subs_resolution           true
% 6.42/1.51  --res_backward_subs_resolution          true
% 6.42/1.51  --res_orphan_elimination                true
% 6.42/1.51  --res_time_limit                        2.
% 6.42/1.51  --res_out_proof                         true
% 6.42/1.51  
% 6.42/1.51  ------ Superposition Options
% 6.42/1.51  
% 6.42/1.51  --superposition_flag                    true
% 6.42/1.51  --sup_passive_queue_type                priority_queues
% 6.42/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.42/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.42/1.51  --demod_completeness_check              fast
% 6.42/1.51  --demod_use_ground                      true
% 6.42/1.51  --sup_to_prop_solver                    passive
% 6.42/1.51  --sup_prop_simpl_new                    true
% 6.42/1.51  --sup_prop_simpl_given                  true
% 6.42/1.51  --sup_fun_splitting                     false
% 6.42/1.51  --sup_smt_interval                      50000
% 6.42/1.51  
% 6.42/1.51  ------ Superposition Simplification Setup
% 6.42/1.51  
% 6.42/1.51  --sup_indices_passive                   []
% 6.42/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.42/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.42/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.42/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.42/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.42/1.51  --sup_full_bw                           [BwDemod]
% 6.42/1.51  --sup_immed_triv                        [TrivRules]
% 6.42/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.42/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.42/1.51  --sup_immed_bw_main                     []
% 6.42/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.42/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 6.42/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.42/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.42/1.51  
% 6.42/1.51  ------ Combination Options
% 6.42/1.51  
% 6.42/1.51  --comb_res_mult                         3
% 6.42/1.51  --comb_sup_mult                         2
% 6.42/1.51  --comb_inst_mult                        10
% 6.42/1.51  
% 6.42/1.51  ------ Debug Options
% 6.42/1.51  
% 6.42/1.51  --dbg_backtrace                         false
% 6.42/1.51  --dbg_dump_prop_clauses                 false
% 6.42/1.51  --dbg_dump_prop_clauses_file            -
% 6.42/1.51  --dbg_out_stat                          false
% 6.42/1.51  ------ Parsing...
% 6.42/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.42/1.51  
% 6.42/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.42/1.51  
% 6.42/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.42/1.51  
% 6.42/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.42/1.51  ------ Proving...
% 6.42/1.51  ------ Problem Properties 
% 6.42/1.51  
% 6.42/1.51  
% 6.42/1.51  clauses                                 11
% 6.42/1.51  conjectures                             1
% 6.42/1.51  EPR                                     2
% 6.42/1.51  Horn                                    11
% 6.42/1.51  unary                                   9
% 6.42/1.51  binary                                  1
% 6.42/1.51  lits                                    14
% 6.42/1.51  lits eq                                 8
% 6.42/1.51  fd_pure                                 0
% 6.42/1.51  fd_pseudo                               0
% 6.42/1.51  fd_cond                                 0
% 6.42/1.51  fd_pseudo_cond                          1
% 6.42/1.51  AC symbols                              0
% 6.42/1.51  
% 6.42/1.51  ------ Schedule dynamic 5 is on 
% 6.42/1.51  
% 6.42/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.42/1.51  
% 6.42/1.51  
% 6.42/1.51  ------ 
% 6.42/1.51  Current options:
% 6.42/1.51  ------ 
% 6.42/1.51  
% 6.42/1.51  ------ Input Options
% 6.42/1.51  
% 6.42/1.51  --out_options                           all
% 6.42/1.51  --tptp_safe_out                         true
% 6.42/1.51  --problem_path                          ""
% 6.42/1.51  --include_path                          ""
% 6.42/1.51  --clausifier                            res/vclausify_rel
% 6.42/1.51  --clausifier_options                    --mode clausify
% 6.42/1.51  --stdin                                 false
% 6.42/1.51  --stats_out                             all
% 6.42/1.51  
% 6.42/1.51  ------ General Options
% 6.42/1.51  
% 6.42/1.51  --fof                                   false
% 6.42/1.51  --time_out_real                         305.
% 6.42/1.51  --time_out_virtual                      -1.
% 6.42/1.51  --symbol_type_check                     false
% 6.42/1.51  --clausify_out                          false
% 6.42/1.51  --sig_cnt_out                           false
% 6.42/1.51  --trig_cnt_out                          false
% 6.42/1.51  --trig_cnt_out_tolerance                1.
% 6.42/1.51  --trig_cnt_out_sk_spl                   false
% 6.42/1.51  --abstr_cl_out                          false
% 6.42/1.51  
% 6.42/1.51  ------ Global Options
% 6.42/1.51  
% 6.42/1.51  --schedule                              default
% 6.42/1.51  --add_important_lit                     false
% 6.42/1.51  --prop_solver_per_cl                    1000
% 6.42/1.51  --min_unsat_core                        false
% 6.42/1.51  --soft_assumptions                      false
% 6.42/1.51  --soft_lemma_size                       3
% 6.42/1.51  --prop_impl_unit_size                   0
% 6.42/1.51  --prop_impl_unit                        []
% 6.42/1.51  --share_sel_clauses                     true
% 6.42/1.51  --reset_solvers                         false
% 6.42/1.51  --bc_imp_inh                            [conj_cone]
% 6.42/1.51  --conj_cone_tolerance                   3.
% 6.42/1.51  --extra_neg_conj                        none
% 6.42/1.51  --large_theory_mode                     true
% 6.42/1.51  --prolific_symb_bound                   200
% 6.42/1.51  --lt_threshold                          2000
% 6.42/1.51  --clause_weak_htbl                      true
% 6.42/1.51  --gc_record_bc_elim                     false
% 6.42/1.51  
% 6.42/1.51  ------ Preprocessing Options
% 6.42/1.51  
% 6.42/1.51  --preprocessing_flag                    true
% 6.42/1.51  --time_out_prep_mult                    0.1
% 6.42/1.51  --splitting_mode                        input
% 6.42/1.51  --splitting_grd                         true
% 6.42/1.51  --splitting_cvd                         false
% 6.42/1.51  --splitting_cvd_svl                     false
% 6.42/1.51  --splitting_nvd                         32
% 6.42/1.51  --sub_typing                            true
% 6.42/1.51  --prep_gs_sim                           true
% 6.42/1.51  --prep_unflatten                        true
% 6.42/1.51  --prep_res_sim                          true
% 6.42/1.51  --prep_upred                            true
% 6.42/1.51  --prep_sem_filter                       exhaustive
% 6.42/1.51  --prep_sem_filter_out                   false
% 6.42/1.51  --pred_elim                             true
% 6.42/1.51  --res_sim_input                         true
% 6.42/1.51  --eq_ax_congr_red                       true
% 6.42/1.51  --pure_diseq_elim                       true
% 6.42/1.51  --brand_transform                       false
% 6.42/1.51  --non_eq_to_eq                          false
% 6.42/1.51  --prep_def_merge                        true
% 6.42/1.51  --prep_def_merge_prop_impl              false
% 6.42/1.51  --prep_def_merge_mbd                    true
% 6.42/1.51  --prep_def_merge_tr_red                 false
% 6.42/1.51  --prep_def_merge_tr_cl                  false
% 6.42/1.51  --smt_preprocessing                     true
% 6.42/1.51  --smt_ac_axioms                         fast
% 6.42/1.51  --preprocessed_out                      false
% 6.42/1.51  --preprocessed_stats                    false
% 6.42/1.51  
% 6.42/1.51  ------ Abstraction refinement Options
% 6.42/1.51  
% 6.42/1.51  --abstr_ref                             []
% 6.42/1.51  --abstr_ref_prep                        false
% 6.42/1.51  --abstr_ref_until_sat                   false
% 6.42/1.51  --abstr_ref_sig_restrict                funpre
% 6.42/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.42/1.51  --abstr_ref_under                       []
% 6.42/1.51  
% 6.42/1.51  ------ SAT Options
% 6.42/1.51  
% 6.42/1.51  --sat_mode                              false
% 6.42/1.51  --sat_fm_restart_options                ""
% 6.42/1.51  --sat_gr_def                            false
% 6.42/1.51  --sat_epr_types                         true
% 6.42/1.51  --sat_non_cyclic_types                  false
% 6.42/1.51  --sat_finite_models                     false
% 6.42/1.51  --sat_fm_lemmas                         false
% 6.42/1.51  --sat_fm_prep                           false
% 6.42/1.51  --sat_fm_uc_incr                        true
% 6.42/1.51  --sat_out_model                         small
% 6.42/1.51  --sat_out_clauses                       false
% 6.42/1.51  
% 6.42/1.51  ------ QBF Options
% 6.42/1.51  
% 6.42/1.51  --qbf_mode                              false
% 6.42/1.51  --qbf_elim_univ                         false
% 6.42/1.51  --qbf_dom_inst                          none
% 6.42/1.51  --qbf_dom_pre_inst                      false
% 6.42/1.51  --qbf_sk_in                             false
% 6.42/1.51  --qbf_pred_elim                         true
% 6.42/1.51  --qbf_split                             512
% 6.42/1.51  
% 6.42/1.51  ------ BMC1 Options
% 6.42/1.51  
% 6.42/1.51  --bmc1_incremental                      false
% 6.42/1.51  --bmc1_axioms                           reachable_all
% 6.42/1.51  --bmc1_min_bound                        0
% 6.42/1.51  --bmc1_max_bound                        -1
% 6.42/1.51  --bmc1_max_bound_default                -1
% 6.42/1.51  --bmc1_symbol_reachability              true
% 6.42/1.51  --bmc1_property_lemmas                  false
% 6.42/1.51  --bmc1_k_induction                      false
% 6.42/1.51  --bmc1_non_equiv_states                 false
% 6.42/1.51  --bmc1_deadlock                         false
% 6.42/1.51  --bmc1_ucm                              false
% 6.42/1.51  --bmc1_add_unsat_core                   none
% 6.42/1.51  --bmc1_unsat_core_children              false
% 6.42/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 6.42/1.51  --bmc1_out_stat                         full
% 6.42/1.51  --bmc1_ground_init                      false
% 6.42/1.51  --bmc1_pre_inst_next_state              false
% 6.42/1.51  --bmc1_pre_inst_state                   false
% 6.42/1.51  --bmc1_pre_inst_reach_state             false
% 6.42/1.51  --bmc1_out_unsat_core                   false
% 6.42/1.51  --bmc1_aig_witness_out                  false
% 6.42/1.51  --bmc1_verbose                          false
% 6.42/1.51  --bmc1_dump_clauses_tptp                false
% 6.42/1.51  --bmc1_dump_unsat_core_tptp             false
% 6.42/1.51  --bmc1_dump_file                        -
% 6.42/1.51  --bmc1_ucm_expand_uc_limit              128
% 6.42/1.51  --bmc1_ucm_n_expand_iterations          6
% 6.42/1.51  --bmc1_ucm_extend_mode                  1
% 6.42/1.51  --bmc1_ucm_init_mode                    2
% 6.42/1.51  --bmc1_ucm_cone_mode                    none
% 6.42/1.51  --bmc1_ucm_reduced_relation_type        0
% 6.42/1.51  --bmc1_ucm_relax_model                  4
% 6.42/1.51  --bmc1_ucm_full_tr_after_sat            true
% 6.42/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 6.42/1.51  --bmc1_ucm_layered_model                none
% 6.42/1.51  --bmc1_ucm_max_lemma_size               10
% 6.42/1.51  
% 6.42/1.51  ------ AIG Options
% 6.42/1.51  
% 6.42/1.51  --aig_mode                              false
% 6.42/1.51  
% 6.42/1.51  ------ Instantiation Options
% 6.42/1.51  
% 6.42/1.51  --instantiation_flag                    true
% 6.42/1.51  --inst_sos_flag                         false
% 6.42/1.51  --inst_sos_phase                        true
% 6.42/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.42/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.42/1.51  --inst_lit_sel_side                     none
% 6.42/1.51  --inst_solver_per_active                1400
% 6.42/1.51  --inst_solver_calls_frac                1.
% 6.42/1.51  --inst_passive_queue_type               priority_queues
% 6.42/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.42/1.51  --inst_passive_queues_freq              [25;2]
% 6.42/1.51  --inst_dismatching                      true
% 6.42/1.51  --inst_eager_unprocessed_to_passive     true
% 6.42/1.51  --inst_prop_sim_given                   true
% 6.42/1.51  --inst_prop_sim_new                     false
% 6.42/1.51  --inst_subs_new                         false
% 6.42/1.51  --inst_eq_res_simp                      false
% 6.42/1.51  --inst_subs_given                       false
% 6.42/1.51  --inst_orphan_elimination               true
% 6.42/1.51  --inst_learning_loop_flag               true
% 6.42/1.51  --inst_learning_start                   3000
% 6.42/1.51  --inst_learning_factor                  2
% 6.42/1.51  --inst_start_prop_sim_after_learn       3
% 6.42/1.51  --inst_sel_renew                        solver
% 6.42/1.51  --inst_lit_activity_flag                true
% 6.42/1.51  --inst_restr_to_given                   false
% 6.42/1.51  --inst_activity_threshold               500
% 6.42/1.51  --inst_out_proof                        true
% 6.42/1.51  
% 6.42/1.51  ------ Resolution Options
% 6.42/1.51  
% 6.42/1.51  --resolution_flag                       false
% 6.42/1.51  --res_lit_sel                           adaptive
% 6.42/1.51  --res_lit_sel_side                      none
% 6.42/1.51  --res_ordering                          kbo
% 6.42/1.51  --res_to_prop_solver                    active
% 6.42/1.51  --res_prop_simpl_new                    false
% 6.42/1.51  --res_prop_simpl_given                  true
% 6.42/1.51  --res_passive_queue_type                priority_queues
% 6.42/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.42/1.51  --res_passive_queues_freq               [15;5]
% 6.42/1.51  --res_forward_subs                      full
% 6.42/1.51  --res_backward_subs                     full
% 6.42/1.51  --res_forward_subs_resolution           true
% 6.42/1.51  --res_backward_subs_resolution          true
% 6.42/1.51  --res_orphan_elimination                true
% 6.42/1.51  --res_time_limit                        2.
% 6.42/1.51  --res_out_proof                         true
% 6.42/1.51  
% 6.42/1.51  ------ Superposition Options
% 6.42/1.51  
% 6.42/1.51  --superposition_flag                    true
% 6.42/1.51  --sup_passive_queue_type                priority_queues
% 6.42/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.42/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.42/1.51  --demod_completeness_check              fast
% 6.42/1.51  --demod_use_ground                      true
% 6.42/1.51  --sup_to_prop_solver                    passive
% 6.42/1.51  --sup_prop_simpl_new                    true
% 6.42/1.51  --sup_prop_simpl_given                  true
% 6.42/1.51  --sup_fun_splitting                     false
% 6.42/1.51  --sup_smt_interval                      50000
% 6.42/1.51  
% 6.42/1.51  ------ Superposition Simplification Setup
% 6.42/1.51  
% 6.42/1.51  --sup_indices_passive                   []
% 6.42/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.42/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.42/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.42/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.42/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.42/1.51  --sup_full_bw                           [BwDemod]
% 6.42/1.51  --sup_immed_triv                        [TrivRules]
% 6.42/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.42/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.42/1.51  --sup_immed_bw_main                     []
% 6.42/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.42/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 6.42/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.42/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.42/1.51  
% 6.42/1.51  ------ Combination Options
% 6.42/1.51  
% 6.42/1.51  --comb_res_mult                         3
% 6.42/1.51  --comb_sup_mult                         2
% 6.42/1.51  --comb_inst_mult                        10
% 6.42/1.51  
% 6.42/1.51  ------ Debug Options
% 6.42/1.51  
% 6.42/1.51  --dbg_backtrace                         false
% 6.42/1.51  --dbg_dump_prop_clauses                 false
% 6.42/1.51  --dbg_dump_prop_clauses_file            -
% 6.42/1.51  --dbg_out_stat                          false
% 6.42/1.51  
% 6.42/1.51  
% 6.42/1.51  
% 6.42/1.51  
% 6.42/1.51  ------ Proving...
% 6.42/1.51  
% 6.42/1.51  
% 6.42/1.51  % SZS status Theorem for theBenchmark.p
% 6.42/1.51  
% 6.42/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 6.42/1.51  
% 6.42/1.51  fof(f15,axiom,(
% 6.42/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.42/1.51  
% 6.42/1.51  fof(f42,plain,(
% 6.42/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.42/1.51    inference(cnf_transformation,[],[f15])).
% 6.42/1.51  
% 6.42/1.51  fof(f8,axiom,(
% 6.42/1.51    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 6.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.42/1.51  
% 6.42/1.51  fof(f35,plain,(
% 6.42/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 6.42/1.51    inference(cnf_transformation,[],[f8])).
% 6.42/1.51  
% 6.42/1.51  fof(f2,axiom,(
% 6.42/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.42/1.51  
% 6.42/1.51  fof(f29,plain,(
% 6.42/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.42/1.51    inference(cnf_transformation,[],[f2])).
% 6.42/1.51  
% 6.42/1.51  fof(f45,plain,(
% 6.42/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 6.42/1.51    inference(definition_unfolding,[],[f35,f29])).
% 6.42/1.51  
% 6.42/1.51  fof(f11,axiom,(
% 6.42/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.42/1.51  
% 6.42/1.51  fof(f38,plain,(
% 6.42/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.42/1.51    inference(cnf_transformation,[],[f11])).
% 6.42/1.51  
% 6.42/1.51  fof(f12,axiom,(
% 6.42/1.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.42/1.51  
% 6.42/1.51  fof(f39,plain,(
% 6.42/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.42/1.51    inference(cnf_transformation,[],[f12])).
% 6.42/1.51  
% 6.42/1.51  fof(f13,axiom,(
% 6.42/1.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.42/1.51  
% 6.42/1.51  fof(f40,plain,(
% 6.42/1.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.42/1.51    inference(cnf_transformation,[],[f13])).
% 6.42/1.51  
% 6.42/1.51  fof(f46,plain,(
% 6.42/1.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 6.42/1.51    inference(definition_unfolding,[],[f39,f40])).
% 6.42/1.51  
% 6.42/1.51  fof(f47,plain,(
% 6.42/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 6.42/1.51    inference(definition_unfolding,[],[f38,f46])).
% 6.42/1.51  
% 6.42/1.51  fof(f55,plain,(
% 6.42/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 6.42/1.51    inference(definition_unfolding,[],[f42,f45,f47])).
% 6.42/1.51  
% 6.42/1.51  fof(f9,axiom,(
% 6.42/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 6.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.42/1.51  
% 6.42/1.51  fof(f36,plain,(
% 6.42/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 6.42/1.51    inference(cnf_transformation,[],[f9])).
% 6.42/1.51  
% 6.42/1.51  fof(f53,plain,(
% 6.42/1.51    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 6.42/1.51    inference(definition_unfolding,[],[f36,f47,f47])).
% 6.42/1.51  
% 6.42/1.51  fof(f7,axiom,(
% 6.42/1.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 6.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.42/1.51  
% 6.42/1.51  fof(f34,plain,(
% 6.42/1.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.42/1.51    inference(cnf_transformation,[],[f7])).
% 6.42/1.51  
% 6.42/1.51  fof(f52,plain,(
% 6.42/1.51    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 6.42/1.51    inference(definition_unfolding,[],[f34,f45])).
% 6.42/1.51  
% 6.42/1.51  fof(f4,axiom,(
% 6.42/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.42/1.51  
% 6.42/1.51  fof(f19,plain,(
% 6.42/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.42/1.51    inference(ennf_transformation,[],[f4])).
% 6.42/1.51  
% 6.42/1.51  fof(f31,plain,(
% 6.42/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 6.42/1.51    inference(cnf_transformation,[],[f19])).
% 6.42/1.51  
% 6.42/1.51  fof(f6,axiom,(
% 6.42/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 6.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.42/1.51  
% 6.42/1.51  fof(f33,plain,(
% 6.42/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 6.42/1.51    inference(cnf_transformation,[],[f6])).
% 6.42/1.51  
% 6.42/1.51  fof(f51,plain,(
% 6.42/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))) )),
% 6.42/1.51    inference(definition_unfolding,[],[f33,f29,f29,f45])).
% 6.42/1.51  
% 6.42/1.51  fof(f1,axiom,(
% 6.42/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.42/1.51  
% 6.42/1.51  fof(f22,plain,(
% 6.42/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.42/1.51    inference(nnf_transformation,[],[f1])).
% 6.42/1.51  
% 6.42/1.51  fof(f23,plain,(
% 6.42/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.42/1.51    inference(flattening,[],[f22])).
% 6.42/1.51  
% 6.42/1.51  fof(f26,plain,(
% 6.42/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.42/1.51    inference(cnf_transformation,[],[f23])).
% 6.42/1.51  
% 6.42/1.51  fof(f58,plain,(
% 6.42/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.42/1.51    inference(equality_resolution,[],[f26])).
% 6.42/1.51  
% 6.42/1.51  fof(f14,axiom,(
% 6.42/1.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 6.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.42/1.51  
% 6.42/1.51  fof(f18,plain,(
% 6.42/1.51    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 6.42/1.51    inference(unused_predicate_definition_removal,[],[f14])).
% 6.42/1.51  
% 6.42/1.51  fof(f20,plain,(
% 6.42/1.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 6.42/1.51    inference(ennf_transformation,[],[f18])).
% 6.42/1.51  
% 6.42/1.51  fof(f41,plain,(
% 6.42/1.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 6.42/1.51    inference(cnf_transformation,[],[f20])).
% 6.42/1.51  
% 6.42/1.51  fof(f10,axiom,(
% 6.42/1.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.42/1.51  
% 6.42/1.51  fof(f37,plain,(
% 6.42/1.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.42/1.51    inference(cnf_transformation,[],[f10])).
% 6.42/1.51  
% 6.42/1.51  fof(f48,plain,(
% 6.42/1.51    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 6.42/1.51    inference(definition_unfolding,[],[f37,f47])).
% 6.42/1.51  
% 6.42/1.51  fof(f54,plain,(
% 6.42/1.51    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 6.42/1.51    inference(definition_unfolding,[],[f41,f48])).
% 6.42/1.51  
% 6.42/1.51  fof(f16,conjecture,(
% 6.42/1.51    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 6.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.42/1.51  
% 6.42/1.51  fof(f17,negated_conjecture,(
% 6.42/1.51    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 6.42/1.51    inference(negated_conjecture,[],[f16])).
% 6.42/1.51  
% 6.42/1.51  fof(f21,plain,(
% 6.42/1.51    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 6.42/1.51    inference(ennf_transformation,[],[f17])).
% 6.42/1.51  
% 6.42/1.51  fof(f24,plain,(
% 6.42/1.51    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK0),sK1) != sK1 & r2_hidden(sK0,sK1))),
% 6.42/1.51    introduced(choice_axiom,[])).
% 6.42/1.51  
% 6.42/1.51  fof(f25,plain,(
% 6.42/1.51    k2_xboole_0(k1_tarski(sK0),sK1) != sK1 & r2_hidden(sK0,sK1)),
% 6.42/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).
% 6.42/1.51  
% 6.42/1.51  fof(f43,plain,(
% 6.42/1.51    r2_hidden(sK0,sK1)),
% 6.42/1.51    inference(cnf_transformation,[],[f25])).
% 6.42/1.51  
% 6.42/1.51  fof(f3,axiom,(
% 6.42/1.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 6.42/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.42/1.51  
% 6.42/1.51  fof(f30,plain,(
% 6.42/1.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.42/1.51    inference(cnf_transformation,[],[f3])).
% 6.42/1.51  
% 6.42/1.51  fof(f49,plain,(
% 6.42/1.51    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 6.42/1.51    inference(definition_unfolding,[],[f30,f45])).
% 6.42/1.51  
% 6.42/1.51  fof(f44,plain,(
% 6.42/1.51    k2_xboole_0(k1_tarski(sK0),sK1) != sK1),
% 6.42/1.51    inference(cnf_transformation,[],[f25])).
% 6.42/1.51  
% 6.42/1.51  fof(f56,plain,(
% 6.42/1.51    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1),
% 6.42/1.51    inference(definition_unfolding,[],[f44,f45,f48])).
% 6.42/1.51  
% 6.42/1.51  cnf(c_10,plain,
% 6.42/1.51      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 6.42/1.51      inference(cnf_transformation,[],[f55]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_8,plain,
% 6.42/1.51      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 6.42/1.51      inference(cnf_transformation,[],[f53]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_7,plain,
% 6.42/1.51      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 6.42/1.51      inference(cnf_transformation,[],[f52]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_239,plain,
% 6.42/1.51      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
% 6.42/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_4,plain,
% 6.42/1.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 6.42/1.51      inference(cnf_transformation,[],[f31]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_240,plain,
% 6.42/1.51      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 6.42/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_354,plain,
% 6.42/1.51      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_239,c_240]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_1260,plain,
% 6.42/1.51      ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_10,c_354]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_2292,plain,
% 6.42/1.51      ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = X0 ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_8,c_1260]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_2469,plain,
% 6.42/1.51      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_10,c_2292]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_6,plain,
% 6.42/1.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 6.42/1.51      inference(cnf_transformation,[],[f51]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_780,plain,
% 6.42/1.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_6,c_6]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_10850,plain,
% 6.42/1.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(X0,X0) ),
% 6.42/1.51      inference(light_normalisation,[status(thm)],[c_780,c_2469]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_10907,plain,
% 6.42/1.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,X1)),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,X1)),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_2469,c_10850]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_629,plain,
% 6.42/1.51      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_8,c_10]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_3218,plain,
% 6.42/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_629,c_10]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_10973,plain,
% 6.42/1.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,X0)) ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_10850,c_3218]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_10980,plain,
% 6.42/1.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,X1)) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,X0)) ),
% 6.42/1.51      inference(demodulation,[status(thm)],[c_10973,c_10850]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_4418,plain,
% 6.42/1.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),X0))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,X0)) ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_2469,c_3218]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_4458,plain,
% 6.42/1.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 6.42/1.51      inference(demodulation,[status(thm)],[c_4418,c_6]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_10982,plain,
% 6.42/1.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 6.42/1.51      inference(light_normalisation,[status(thm)],[c_10980,c_4458]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_10926,plain,
% 6.42/1.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_6,c_10850]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_10966,plain,
% 6.42/1.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,X0)))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_10850,c_10850]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_11002,plain,
% 6.42/1.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,X0) ),
% 6.42/1.51      inference(demodulation,[status(thm)],[c_10966,c_10850,c_10982]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_11076,plain,
% 6.42/1.51      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(X0,X0) ),
% 6.42/1.51      inference(light_normalisation,[status(thm)],[c_10926,c_11002]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_2,plain,
% 6.42/1.51      ( r1_tarski(X0,X0) ),
% 6.42/1.51      inference(cnf_transformation,[],[f58]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_241,plain,
% 6.42/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 6.42/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_353,plain,
% 6.42/1.51      ( k3_xboole_0(X0,X0) = X0 ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_241,c_240]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_11078,plain,
% 6.42/1.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X1,X1) ),
% 6.42/1.51      inference(demodulation,[status(thm)],[c_11076,c_353,c_2469,c_4458]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_11157,plain,
% 6.42/1.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))))) = k5_xboole_0(X1,X1) ),
% 6.42/1.51      inference(light_normalisation,
% 6.42/1.51                [status(thm)],
% 6.42/1.51                [c_10907,c_10982,c_11078]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_11159,plain,
% 6.42/1.51      ( k5_xboole_0(X0,X0) = k5_xboole_0(X1,X1) ),
% 6.42/1.51      inference(light_normalisation,[status(thm)],[c_11157,c_6,c_10850]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_9,plain,
% 6.42/1.51      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 6.42/1.51      inference(cnf_transformation,[],[f54]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_12,negated_conjecture,
% 6.42/1.51      ( r2_hidden(sK0,sK1) ),
% 6.42/1.51      inference(cnf_transformation,[],[f43]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_91,plain,
% 6.42/1.51      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
% 6.42/1.51      | sK1 != X1
% 6.42/1.51      | sK0 != X0 ),
% 6.42/1.51      inference(resolution_lifted,[status(thm)],[c_9,c_12]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_92,plain,
% 6.42/1.51      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
% 6.42/1.51      inference(unflattening,[status(thm)],[c_91]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_238,plain,
% 6.42/1.51      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
% 6.42/1.51      inference(predicate_to_equality,[status(thm)],[c_92]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_355,plain,
% 6.42/1.51      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_238,c_240]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_633,plain,
% 6.42/1.51      ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_355,c_10]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_11376,plain,
% 6.42/1.51      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(X0,X0)) ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_11159,c_633]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_3,plain,
% 6.42/1.51      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 6.42/1.51      inference(cnf_transformation,[],[f49]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_634,plain,
% 6.42/1.51      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_10,c_3]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_1392,plain,
% 6.42/1.51      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_8,c_634]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_9133,plain,
% 6.42/1.51      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k5_xboole_0(X1,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_10,c_4458]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_9372,plain,
% 6.42/1.51      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(X0,k5_xboole_0(X0,X0)) ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_1392,c_9133]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_9380,plain,
% 6.42/1.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
% 6.42/1.51      inference(light_normalisation,[status(thm)],[c_9372,c_3]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_11379,plain,
% 6.42/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X1)) = X0 ),
% 6.42/1.51      inference(superposition,[status(thm)],[c_11159,c_9380]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_11457,plain,
% 6.42/1.51      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = sK1 ),
% 6.42/1.51      inference(demodulation,[status(thm)],[c_11376,c_11379]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_11,negated_conjecture,
% 6.42/1.51      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 6.42/1.51      inference(cnf_transformation,[],[f56]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(c_3191,plain,
% 6.42/1.51      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 6.42/1.51      inference(demodulation,[status(thm)],[c_629,c_11]) ).
% 6.42/1.51  
% 6.42/1.51  cnf(contradiction,plain,
% 6.42/1.51      ( $false ),
% 6.42/1.51      inference(minisat,[status(thm)],[c_11457,c_3191]) ).
% 6.42/1.51  
% 6.42/1.51  
% 6.42/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 6.42/1.51  
% 6.42/1.51  ------                               Statistics
% 6.42/1.51  
% 6.42/1.51  ------ General
% 6.42/1.51  
% 6.42/1.51  abstr_ref_over_cycles:                  0
% 6.42/1.51  abstr_ref_under_cycles:                 0
% 6.42/1.51  gc_basic_clause_elim:                   0
% 6.42/1.51  forced_gc_time:                         0
% 6.42/1.51  parsing_time:                           0.012
% 6.42/1.51  unif_index_cands_time:                  0.
% 6.42/1.51  unif_index_add_time:                    0.
% 6.42/1.51  orderings_time:                         0.
% 6.42/1.51  out_proof_time:                         0.007
% 6.42/1.51  total_time:                             0.575
% 6.42/1.51  num_of_symbols:                         40
% 6.42/1.51  num_of_terms:                           10445
% 6.42/1.51  
% 6.42/1.51  ------ Preprocessing
% 6.42/1.51  
% 6.42/1.51  num_of_splits:                          0
% 6.42/1.51  num_of_split_atoms:                     0
% 6.42/1.51  num_of_reused_defs:                     0
% 6.42/1.51  num_eq_ax_congr_red:                    0
% 6.42/1.51  num_of_sem_filtered_clauses:            1
% 6.42/1.51  num_of_subtypes:                        0
% 6.42/1.51  monotx_restored_types:                  0
% 6.42/1.51  sat_num_of_epr_types:                   0
% 6.42/1.51  sat_num_of_non_cyclic_types:            0
% 6.42/1.51  sat_guarded_non_collapsed_types:        0
% 6.42/1.51  num_pure_diseq_elim:                    0
% 6.42/1.51  simp_replaced_by:                       0
% 6.42/1.51  res_preprocessed:                       60
% 6.42/1.51  prep_upred:                             0
% 6.42/1.51  prep_unflattend:                        2
% 6.42/1.51  smt_new_axioms:                         0
% 6.42/1.51  pred_elim_cands:                        1
% 6.42/1.51  pred_elim:                              1
% 6.42/1.51  pred_elim_cl:                           1
% 6.42/1.51  pred_elim_cycles:                       3
% 6.42/1.51  merged_defs:                            0
% 6.42/1.51  merged_defs_ncl:                        0
% 6.42/1.51  bin_hyper_res:                          0
% 6.42/1.51  prep_cycles:                            4
% 6.42/1.51  pred_elim_time:                         0.
% 6.42/1.51  splitting_time:                         0.
% 6.42/1.51  sem_filter_time:                        0.
% 6.42/1.51  monotx_time:                            0.
% 6.42/1.51  subtype_inf_time:                       0.
% 6.42/1.51  
% 6.42/1.51  ------ Problem properties
% 6.42/1.51  
% 6.42/1.51  clauses:                                11
% 6.42/1.51  conjectures:                            1
% 6.42/1.51  epr:                                    2
% 6.42/1.51  horn:                                   11
% 6.42/1.51  ground:                                 2
% 6.42/1.51  unary:                                  9
% 6.42/1.51  binary:                                 1
% 6.42/1.51  lits:                                   14
% 6.42/1.51  lits_eq:                                8
% 6.42/1.51  fd_pure:                                0
% 6.42/1.51  fd_pseudo:                              0
% 6.42/1.51  fd_cond:                                0
% 6.42/1.51  fd_pseudo_cond:                         1
% 6.42/1.51  ac_symbols:                             0
% 6.42/1.51  
% 6.42/1.51  ------ Propositional Solver
% 6.42/1.51  
% 6.42/1.51  prop_solver_calls:                      33
% 6.42/1.51  prop_fast_solver_calls:                 330
% 6.42/1.51  smt_solver_calls:                       0
% 6.42/1.51  smt_fast_solver_calls:                  0
% 6.42/1.51  prop_num_of_clauses:                    4265
% 6.42/1.51  prop_preprocess_simplified:             7875
% 6.42/1.51  prop_fo_subsumed:                       0
% 6.42/1.51  prop_solver_time:                       0.
% 6.42/1.51  smt_solver_time:                        0.
% 6.42/1.51  smt_fast_solver_time:                   0.
% 6.42/1.51  prop_fast_solver_time:                  0.
% 6.42/1.51  prop_unsat_core_time:                   0.
% 6.42/1.51  
% 6.42/1.51  ------ QBF
% 6.42/1.51  
% 6.42/1.51  qbf_q_res:                              0
% 6.42/1.51  qbf_num_tautologies:                    0
% 6.42/1.51  qbf_prep_cycles:                        0
% 6.42/1.51  
% 6.42/1.51  ------ BMC1
% 6.42/1.51  
% 6.42/1.51  bmc1_current_bound:                     -1
% 6.42/1.51  bmc1_last_solved_bound:                 -1
% 6.42/1.51  bmc1_unsat_core_size:                   -1
% 6.42/1.51  bmc1_unsat_core_parents_size:           -1
% 6.42/1.51  bmc1_merge_next_fun:                    0
% 6.42/1.51  bmc1_unsat_core_clauses_time:           0.
% 6.42/1.51  
% 6.42/1.51  ------ Instantiation
% 6.42/1.51  
% 6.42/1.51  inst_num_of_clauses:                    1436
% 6.42/1.51  inst_num_in_passive:                    825
% 6.42/1.51  inst_num_in_active:                     542
% 6.42/1.51  inst_num_in_unprocessed:                69
% 6.42/1.51  inst_num_of_loops:                      550
% 6.42/1.51  inst_num_of_learning_restarts:          0
% 6.42/1.51  inst_num_moves_active_passive:          2
% 6.42/1.51  inst_lit_activity:                      0
% 6.42/1.51  inst_lit_activity_moves:                0
% 6.42/1.51  inst_num_tautologies:                   0
% 6.42/1.51  inst_num_prop_implied:                  0
% 6.42/1.51  inst_num_existing_simplified:           0
% 6.42/1.51  inst_num_eq_res_simplified:             0
% 6.42/1.51  inst_num_child_elim:                    0
% 6.42/1.51  inst_num_of_dismatching_blockings:      239
% 6.42/1.51  inst_num_of_non_proper_insts:           1386
% 6.42/1.51  inst_num_of_duplicates:                 0
% 6.42/1.51  inst_inst_num_from_inst_to_res:         0
% 6.42/1.51  inst_dismatching_checking_time:         0.
% 6.42/1.51  
% 6.42/1.51  ------ Resolution
% 6.42/1.51  
% 6.42/1.51  res_num_of_clauses:                     0
% 6.42/1.51  res_num_in_passive:                     0
% 6.42/1.51  res_num_in_active:                      0
% 6.42/1.51  res_num_of_loops:                       64
% 6.42/1.51  res_forward_subset_subsumed:            211
% 6.42/1.51  res_backward_subset_subsumed:           0
% 6.42/1.51  res_forward_subsumed:                   0
% 6.42/1.51  res_backward_subsumed:                  0
% 6.42/1.51  res_forward_subsumption_resolution:     0
% 6.42/1.51  res_backward_subsumption_resolution:    0
% 6.42/1.51  res_clause_to_clause_subsumption:       3642
% 6.42/1.51  res_orphan_elimination:                 0
% 6.42/1.51  res_tautology_del:                      102
% 6.42/1.51  res_num_eq_res_simplified:              0
% 6.42/1.51  res_num_sel_changes:                    0
% 6.42/1.51  res_moves_from_active_to_pass:          0
% 6.42/1.51  
% 6.42/1.51  ------ Superposition
% 6.42/1.51  
% 6.42/1.51  sup_time_total:                         0.
% 6.42/1.51  sup_time_generating:                    0.
% 6.42/1.51  sup_time_sim_full:                      0.
% 6.42/1.51  sup_time_sim_immed:                     0.
% 6.42/1.51  
% 6.42/1.51  sup_num_of_clauses:                     524
% 6.42/1.51  sup_num_in_active:                      86
% 6.42/1.51  sup_num_in_passive:                     438
% 6.42/1.51  sup_num_of_loops:                       109
% 6.42/1.51  sup_fw_superposition:                   858
% 6.42/1.51  sup_bw_superposition:                   756
% 6.42/1.51  sup_immediate_simplified:               590
% 6.42/1.51  sup_given_eliminated:                   4
% 6.42/1.51  comparisons_done:                       0
% 6.42/1.51  comparisons_avoided:                    0
% 6.42/1.51  
% 6.42/1.51  ------ Simplifications
% 6.42/1.51  
% 6.42/1.51  
% 6.42/1.51  sim_fw_subset_subsumed:                 7
% 6.42/1.51  sim_bw_subset_subsumed:                 7
% 6.42/1.51  sim_fw_subsumed:                        135
% 6.42/1.51  sim_bw_subsumed:                        13
% 6.42/1.51  sim_fw_subsumption_res:                 0
% 6.42/1.51  sim_bw_subsumption_res:                 0
% 6.42/1.51  sim_tautology_del:                      0
% 6.42/1.51  sim_eq_tautology_del:                   42
% 6.42/1.51  sim_eq_res_simp:                        0
% 6.42/1.51  sim_fw_demodulated:                     136
% 6.42/1.51  sim_bw_demodulated:                     109
% 6.42/1.51  sim_light_normalised:                   348
% 6.42/1.51  sim_joinable_taut:                      0
% 6.42/1.51  sim_joinable_simp:                      0
% 6.42/1.51  sim_ac_normalised:                      0
% 6.42/1.51  sim_smt_subsumption:                    0
% 6.42/1.51  
%------------------------------------------------------------------------------
