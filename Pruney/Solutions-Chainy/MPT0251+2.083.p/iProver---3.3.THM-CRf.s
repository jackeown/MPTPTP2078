%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:16 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  102 (1558 expanded)
%              Number of clauses        :   47 ( 264 expanded)
%              Number of leaves         :   17 ( 483 expanded)
%              Depth                    :   23
%              Number of atoms          :  135 (1761 expanded)
%              Number of equality atoms :   95 (1512 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) ),
    inference(definition_unfolding,[],[f34,f45,f45,f30])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f45,f47])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) ),
    inference(definition_unfolding,[],[f35,f30,f30,f45])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f45,f45])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(definition_unfolding,[],[f32,f45])).

fof(f44,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f56,plain,(
    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(definition_unfolding,[],[f44,f45,f48])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_12,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_82,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_12])).

cnf(c_83,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unflattening,[status(thm)],[c_82])).

cnf(c_206,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_83])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_207,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_374,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_206,c_207])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_649,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1))) = k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(superposition,[status(thm)],[c_374,c_7])).

cnf(c_10,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_616,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_374,c_10])).

cnf(c_651,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_649,c_374,c_616])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1135,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[status(thm)],[c_651,c_8])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_606,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_922,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_606,c_7])).

cnf(c_923,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_922,c_606])).

cnf(c_924,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_923,c_606])).

cnf(c_1136,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_924,c_8])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_208,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_373,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_208,c_207])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_921,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_606,c_5])).

cnf(c_1150,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1136,c_373,c_921,c_923])).

cnf(c_1151,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1150,c_924])).

cnf(c_1152,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_1135,c_1151])).

cnf(c_1153,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1152,c_923])).

cnf(c_1300,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k3_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) ),
    inference(superposition,[status(thm)],[c_1153,c_8])).

cnf(c_1308,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1300,c_921,c_924])).

cnf(c_1309,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0),k3_xboole_0(k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0),sK1)) = k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)) ),
    inference(superposition,[status(thm)],[c_1308,c_8])).

cnf(c_1006,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_924,c_4])).

cnf(c_1008,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_921,c_1006])).

cnf(c_617,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_1132,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X0)) = k5_xboole_0(X1,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_617,c_8])).

cnf(c_1322,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1309,c_374,c_1008,c_1132,c_1151])).

cnf(c_1323,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1322,c_374])).

cnf(c_1454,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1323,c_616])).

cnf(c_1455,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_1454,c_1008])).

cnf(c_11,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_604,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) != sK1 ),
    inference(demodulation,[status(thm)],[c_0,c_11])).

cnf(c_605,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(light_normalisation,[status(thm)],[c_604,c_374])).

cnf(c_655,plain,
    ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(light_normalisation,[status(thm)],[c_605,c_616])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1455,c_655])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 11:09:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.34/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.03  
% 3.34/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/1.03  
% 3.34/1.03  ------  iProver source info
% 3.34/1.03  
% 3.34/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.34/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/1.03  git: non_committed_changes: false
% 3.34/1.03  git: last_make_outside_of_git: false
% 3.34/1.03  
% 3.34/1.03  ------ 
% 3.34/1.03  
% 3.34/1.03  ------ Input Options
% 3.34/1.03  
% 3.34/1.03  --out_options                           all
% 3.34/1.03  --tptp_safe_out                         true
% 3.34/1.03  --problem_path                          ""
% 3.34/1.03  --include_path                          ""
% 3.34/1.03  --clausifier                            res/vclausify_rel
% 3.34/1.03  --clausifier_options                    ""
% 3.34/1.03  --stdin                                 false
% 3.34/1.03  --stats_out                             all
% 3.34/1.03  
% 3.34/1.03  ------ General Options
% 3.34/1.03  
% 3.34/1.03  --fof                                   false
% 3.34/1.03  --time_out_real                         305.
% 3.34/1.03  --time_out_virtual                      -1.
% 3.34/1.03  --symbol_type_check                     false
% 3.34/1.03  --clausify_out                          false
% 3.34/1.03  --sig_cnt_out                           false
% 3.34/1.03  --trig_cnt_out                          false
% 3.34/1.03  --trig_cnt_out_tolerance                1.
% 3.34/1.03  --trig_cnt_out_sk_spl                   false
% 3.34/1.03  --abstr_cl_out                          false
% 3.34/1.03  
% 3.34/1.03  ------ Global Options
% 3.34/1.03  
% 3.34/1.03  --schedule                              default
% 3.34/1.03  --add_important_lit                     false
% 3.34/1.03  --prop_solver_per_cl                    1000
% 3.34/1.03  --min_unsat_core                        false
% 3.34/1.03  --soft_assumptions                      false
% 3.34/1.03  --soft_lemma_size                       3
% 3.34/1.03  --prop_impl_unit_size                   0
% 3.34/1.03  --prop_impl_unit                        []
% 3.34/1.03  --share_sel_clauses                     true
% 3.34/1.03  --reset_solvers                         false
% 3.34/1.03  --bc_imp_inh                            [conj_cone]
% 3.34/1.03  --conj_cone_tolerance                   3.
% 3.34/1.03  --extra_neg_conj                        none
% 3.34/1.03  --large_theory_mode                     true
% 3.34/1.03  --prolific_symb_bound                   200
% 3.34/1.03  --lt_threshold                          2000
% 3.34/1.03  --clause_weak_htbl                      true
% 3.34/1.03  --gc_record_bc_elim                     false
% 3.34/1.03  
% 3.34/1.03  ------ Preprocessing Options
% 3.34/1.03  
% 3.34/1.03  --preprocessing_flag                    true
% 3.34/1.03  --time_out_prep_mult                    0.1
% 3.34/1.03  --splitting_mode                        input
% 3.34/1.03  --splitting_grd                         true
% 3.34/1.03  --splitting_cvd                         false
% 3.34/1.03  --splitting_cvd_svl                     false
% 3.34/1.03  --splitting_nvd                         32
% 3.34/1.03  --sub_typing                            true
% 3.34/1.03  --prep_gs_sim                           true
% 3.34/1.03  --prep_unflatten                        true
% 3.34/1.03  --prep_res_sim                          true
% 3.34/1.03  --prep_upred                            true
% 3.34/1.03  --prep_sem_filter                       exhaustive
% 3.34/1.03  --prep_sem_filter_out                   false
% 3.34/1.03  --pred_elim                             true
% 3.34/1.03  --res_sim_input                         true
% 3.34/1.03  --eq_ax_congr_red                       true
% 3.34/1.03  --pure_diseq_elim                       true
% 3.34/1.03  --brand_transform                       false
% 3.34/1.03  --non_eq_to_eq                          false
% 3.34/1.03  --prep_def_merge                        true
% 3.34/1.03  --prep_def_merge_prop_impl              false
% 3.34/1.03  --prep_def_merge_mbd                    true
% 3.34/1.03  --prep_def_merge_tr_red                 false
% 3.34/1.03  --prep_def_merge_tr_cl                  false
% 3.34/1.03  --smt_preprocessing                     true
% 3.34/1.03  --smt_ac_axioms                         fast
% 3.34/1.03  --preprocessed_out                      false
% 3.34/1.03  --preprocessed_stats                    false
% 3.34/1.03  
% 3.34/1.03  ------ Abstraction refinement Options
% 3.34/1.03  
% 3.34/1.03  --abstr_ref                             []
% 3.34/1.03  --abstr_ref_prep                        false
% 3.34/1.03  --abstr_ref_until_sat                   false
% 3.34/1.03  --abstr_ref_sig_restrict                funpre
% 3.34/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.03  --abstr_ref_under                       []
% 3.34/1.03  
% 3.34/1.03  ------ SAT Options
% 3.34/1.03  
% 3.34/1.03  --sat_mode                              false
% 3.34/1.03  --sat_fm_restart_options                ""
% 3.34/1.03  --sat_gr_def                            false
% 3.34/1.03  --sat_epr_types                         true
% 3.34/1.03  --sat_non_cyclic_types                  false
% 3.34/1.03  --sat_finite_models                     false
% 3.34/1.03  --sat_fm_lemmas                         false
% 3.34/1.03  --sat_fm_prep                           false
% 3.34/1.03  --sat_fm_uc_incr                        true
% 3.34/1.03  --sat_out_model                         small
% 3.34/1.03  --sat_out_clauses                       false
% 3.34/1.03  
% 3.34/1.03  ------ QBF Options
% 3.34/1.03  
% 3.34/1.03  --qbf_mode                              false
% 3.34/1.03  --qbf_elim_univ                         false
% 3.34/1.03  --qbf_dom_inst                          none
% 3.34/1.03  --qbf_dom_pre_inst                      false
% 3.34/1.03  --qbf_sk_in                             false
% 3.34/1.03  --qbf_pred_elim                         true
% 3.34/1.03  --qbf_split                             512
% 3.34/1.03  
% 3.34/1.03  ------ BMC1 Options
% 3.34/1.03  
% 3.34/1.03  --bmc1_incremental                      false
% 3.34/1.03  --bmc1_axioms                           reachable_all
% 3.34/1.03  --bmc1_min_bound                        0
% 3.34/1.03  --bmc1_max_bound                        -1
% 3.34/1.03  --bmc1_max_bound_default                -1
% 3.34/1.03  --bmc1_symbol_reachability              true
% 3.34/1.03  --bmc1_property_lemmas                  false
% 3.34/1.03  --bmc1_k_induction                      false
% 3.34/1.03  --bmc1_non_equiv_states                 false
% 3.34/1.03  --bmc1_deadlock                         false
% 3.34/1.03  --bmc1_ucm                              false
% 3.34/1.03  --bmc1_add_unsat_core                   none
% 3.34/1.03  --bmc1_unsat_core_children              false
% 3.34/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.03  --bmc1_out_stat                         full
% 3.34/1.03  --bmc1_ground_init                      false
% 3.34/1.03  --bmc1_pre_inst_next_state              false
% 3.34/1.03  --bmc1_pre_inst_state                   false
% 3.34/1.03  --bmc1_pre_inst_reach_state             false
% 3.34/1.03  --bmc1_out_unsat_core                   false
% 3.34/1.03  --bmc1_aig_witness_out                  false
% 3.34/1.03  --bmc1_verbose                          false
% 3.34/1.03  --bmc1_dump_clauses_tptp                false
% 3.34/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.03  --bmc1_dump_file                        -
% 3.34/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.03  --bmc1_ucm_extend_mode                  1
% 3.34/1.03  --bmc1_ucm_init_mode                    2
% 3.34/1.03  --bmc1_ucm_cone_mode                    none
% 3.34/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.03  --bmc1_ucm_relax_model                  4
% 3.34/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.03  --bmc1_ucm_layered_model                none
% 3.34/1.03  --bmc1_ucm_max_lemma_size               10
% 3.34/1.03  
% 3.34/1.03  ------ AIG Options
% 3.34/1.03  
% 3.34/1.03  --aig_mode                              false
% 3.34/1.03  
% 3.34/1.03  ------ Instantiation Options
% 3.34/1.03  
% 3.34/1.03  --instantiation_flag                    true
% 3.34/1.03  --inst_sos_flag                         true
% 3.34/1.03  --inst_sos_phase                        true
% 3.34/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.03  --inst_lit_sel_side                     num_symb
% 3.34/1.03  --inst_solver_per_active                1400
% 3.34/1.03  --inst_solver_calls_frac                1.
% 3.34/1.03  --inst_passive_queue_type               priority_queues
% 3.34/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.03  --inst_passive_queues_freq              [25;2]
% 3.34/1.03  --inst_dismatching                      true
% 3.34/1.03  --inst_eager_unprocessed_to_passive     true
% 3.34/1.03  --inst_prop_sim_given                   true
% 3.34/1.03  --inst_prop_sim_new                     false
% 3.34/1.03  --inst_subs_new                         false
% 3.34/1.03  --inst_eq_res_simp                      false
% 3.34/1.03  --inst_subs_given                       false
% 3.34/1.03  --inst_orphan_elimination               true
% 3.34/1.03  --inst_learning_loop_flag               true
% 3.34/1.03  --inst_learning_start                   3000
% 3.34/1.03  --inst_learning_factor                  2
% 3.34/1.03  --inst_start_prop_sim_after_learn       3
% 3.34/1.03  --inst_sel_renew                        solver
% 3.34/1.03  --inst_lit_activity_flag                true
% 3.34/1.03  --inst_restr_to_given                   false
% 3.34/1.03  --inst_activity_threshold               500
% 3.34/1.03  --inst_out_proof                        true
% 3.34/1.03  
% 3.34/1.03  ------ Resolution Options
% 3.34/1.03  
% 3.34/1.03  --resolution_flag                       true
% 3.34/1.03  --res_lit_sel                           adaptive
% 3.34/1.03  --res_lit_sel_side                      none
% 3.34/1.03  --res_ordering                          kbo
% 3.34/1.03  --res_to_prop_solver                    active
% 3.34/1.03  --res_prop_simpl_new                    false
% 3.34/1.03  --res_prop_simpl_given                  true
% 3.34/1.03  --res_passive_queue_type                priority_queues
% 3.34/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.03  --res_passive_queues_freq               [15;5]
% 3.34/1.03  --res_forward_subs                      full
% 3.34/1.03  --res_backward_subs                     full
% 3.34/1.03  --res_forward_subs_resolution           true
% 3.34/1.03  --res_backward_subs_resolution          true
% 3.34/1.03  --res_orphan_elimination                true
% 3.34/1.03  --res_time_limit                        2.
% 3.34/1.03  --res_out_proof                         true
% 3.34/1.03  
% 3.34/1.03  ------ Superposition Options
% 3.34/1.03  
% 3.34/1.03  --superposition_flag                    true
% 3.34/1.03  --sup_passive_queue_type                priority_queues
% 3.34/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.03  --demod_completeness_check              fast
% 3.34/1.03  --demod_use_ground                      true
% 3.34/1.03  --sup_to_prop_solver                    passive
% 3.34/1.03  --sup_prop_simpl_new                    true
% 3.34/1.03  --sup_prop_simpl_given                  true
% 3.34/1.03  --sup_fun_splitting                     true
% 3.34/1.03  --sup_smt_interval                      50000
% 3.34/1.03  
% 3.34/1.03  ------ Superposition Simplification Setup
% 3.34/1.03  
% 3.34/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.34/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.34/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.34/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.34/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.34/1.03  --sup_immed_triv                        [TrivRules]
% 3.34/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.03  --sup_immed_bw_main                     []
% 3.34/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.34/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.03  --sup_input_bw                          []
% 3.34/1.03  
% 3.34/1.03  ------ Combination Options
% 3.34/1.03  
% 3.34/1.03  --comb_res_mult                         3
% 3.34/1.03  --comb_sup_mult                         2
% 3.34/1.03  --comb_inst_mult                        10
% 3.34/1.03  
% 3.34/1.03  ------ Debug Options
% 3.34/1.03  
% 3.34/1.03  --dbg_backtrace                         false
% 3.34/1.03  --dbg_dump_prop_clauses                 false
% 3.34/1.03  --dbg_dump_prop_clauses_file            -
% 3.34/1.03  --dbg_out_stat                          false
% 3.34/1.03  ------ Parsing...
% 3.34/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/1.03  
% 3.34/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.34/1.03  
% 3.34/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/1.03  
% 3.34/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/1.03  ------ Proving...
% 3.34/1.03  ------ Problem Properties 
% 3.34/1.03  
% 3.34/1.03  
% 3.34/1.03  clauses                                 11
% 3.34/1.03  conjectures                             1
% 3.34/1.03  EPR                                     2
% 3.34/1.03  Horn                                    11
% 3.34/1.03  unary                                   9
% 3.34/1.03  binary                                  1
% 3.34/1.03  lits                                    14
% 3.34/1.03  lits eq                                 9
% 3.34/1.03  fd_pure                                 0
% 3.34/1.03  fd_pseudo                               0
% 3.34/1.03  fd_cond                                 0
% 3.34/1.03  fd_pseudo_cond                          1
% 3.34/1.03  AC symbols                              0
% 3.34/1.03  
% 3.34/1.03  ------ Schedule dynamic 5 is on 
% 3.34/1.03  
% 3.34/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/1.03  
% 3.34/1.03  
% 3.34/1.03  ------ 
% 3.34/1.03  Current options:
% 3.34/1.03  ------ 
% 3.34/1.03  
% 3.34/1.03  ------ Input Options
% 3.34/1.03  
% 3.34/1.03  --out_options                           all
% 3.34/1.03  --tptp_safe_out                         true
% 3.34/1.03  --problem_path                          ""
% 3.34/1.03  --include_path                          ""
% 3.34/1.03  --clausifier                            res/vclausify_rel
% 3.34/1.03  --clausifier_options                    ""
% 3.34/1.03  --stdin                                 false
% 3.34/1.03  --stats_out                             all
% 3.34/1.03  
% 3.34/1.03  ------ General Options
% 3.34/1.03  
% 3.34/1.03  --fof                                   false
% 3.34/1.03  --time_out_real                         305.
% 3.34/1.03  --time_out_virtual                      -1.
% 3.34/1.03  --symbol_type_check                     false
% 3.34/1.03  --clausify_out                          false
% 3.34/1.03  --sig_cnt_out                           false
% 3.34/1.03  --trig_cnt_out                          false
% 3.34/1.03  --trig_cnt_out_tolerance                1.
% 3.34/1.03  --trig_cnt_out_sk_spl                   false
% 3.34/1.03  --abstr_cl_out                          false
% 3.34/1.03  
% 3.34/1.03  ------ Global Options
% 3.34/1.03  
% 3.34/1.03  --schedule                              default
% 3.34/1.03  --add_important_lit                     false
% 3.34/1.03  --prop_solver_per_cl                    1000
% 3.34/1.03  --min_unsat_core                        false
% 3.34/1.03  --soft_assumptions                      false
% 3.34/1.03  --soft_lemma_size                       3
% 3.34/1.03  --prop_impl_unit_size                   0
% 3.34/1.03  --prop_impl_unit                        []
% 3.34/1.03  --share_sel_clauses                     true
% 3.34/1.03  --reset_solvers                         false
% 3.34/1.03  --bc_imp_inh                            [conj_cone]
% 3.34/1.03  --conj_cone_tolerance                   3.
% 3.34/1.03  --extra_neg_conj                        none
% 3.34/1.03  --large_theory_mode                     true
% 3.34/1.03  --prolific_symb_bound                   200
% 3.34/1.03  --lt_threshold                          2000
% 3.34/1.03  --clause_weak_htbl                      true
% 3.34/1.03  --gc_record_bc_elim                     false
% 3.34/1.03  
% 3.34/1.03  ------ Preprocessing Options
% 3.34/1.03  
% 3.34/1.03  --preprocessing_flag                    true
% 3.34/1.03  --time_out_prep_mult                    0.1
% 3.34/1.03  --splitting_mode                        input
% 3.34/1.03  --splitting_grd                         true
% 3.34/1.03  --splitting_cvd                         false
% 3.34/1.03  --splitting_cvd_svl                     false
% 3.34/1.03  --splitting_nvd                         32
% 3.34/1.03  --sub_typing                            true
% 3.34/1.03  --prep_gs_sim                           true
% 3.34/1.03  --prep_unflatten                        true
% 3.34/1.03  --prep_res_sim                          true
% 3.34/1.03  --prep_upred                            true
% 3.34/1.03  --prep_sem_filter                       exhaustive
% 3.34/1.03  --prep_sem_filter_out                   false
% 3.34/1.03  --pred_elim                             true
% 3.34/1.03  --res_sim_input                         true
% 3.34/1.03  --eq_ax_congr_red                       true
% 3.34/1.03  --pure_diseq_elim                       true
% 3.34/1.03  --brand_transform                       false
% 3.34/1.03  --non_eq_to_eq                          false
% 3.34/1.03  --prep_def_merge                        true
% 3.34/1.03  --prep_def_merge_prop_impl              false
% 3.34/1.03  --prep_def_merge_mbd                    true
% 3.34/1.03  --prep_def_merge_tr_red                 false
% 3.34/1.03  --prep_def_merge_tr_cl                  false
% 3.34/1.03  --smt_preprocessing                     true
% 3.34/1.03  --smt_ac_axioms                         fast
% 3.34/1.03  --preprocessed_out                      false
% 3.34/1.03  --preprocessed_stats                    false
% 3.34/1.03  
% 3.34/1.03  ------ Abstraction refinement Options
% 3.34/1.03  
% 3.34/1.03  --abstr_ref                             []
% 3.34/1.03  --abstr_ref_prep                        false
% 3.34/1.03  --abstr_ref_until_sat                   false
% 3.34/1.03  --abstr_ref_sig_restrict                funpre
% 3.34/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.03  --abstr_ref_under                       []
% 3.34/1.03  
% 3.34/1.03  ------ SAT Options
% 3.34/1.03  
% 3.34/1.03  --sat_mode                              false
% 3.34/1.03  --sat_fm_restart_options                ""
% 3.34/1.03  --sat_gr_def                            false
% 3.34/1.03  --sat_epr_types                         true
% 3.34/1.03  --sat_non_cyclic_types                  false
% 3.34/1.03  --sat_finite_models                     false
% 3.34/1.03  --sat_fm_lemmas                         false
% 3.34/1.03  --sat_fm_prep                           false
% 3.34/1.03  --sat_fm_uc_incr                        true
% 3.34/1.03  --sat_out_model                         small
% 3.34/1.03  --sat_out_clauses                       false
% 3.34/1.03  
% 3.34/1.03  ------ QBF Options
% 3.34/1.03  
% 3.34/1.03  --qbf_mode                              false
% 3.34/1.03  --qbf_elim_univ                         false
% 3.34/1.03  --qbf_dom_inst                          none
% 3.34/1.03  --qbf_dom_pre_inst                      false
% 3.34/1.03  --qbf_sk_in                             false
% 3.34/1.03  --qbf_pred_elim                         true
% 3.34/1.03  --qbf_split                             512
% 3.34/1.03  
% 3.34/1.03  ------ BMC1 Options
% 3.34/1.03  
% 3.34/1.03  --bmc1_incremental                      false
% 3.34/1.03  --bmc1_axioms                           reachable_all
% 3.34/1.03  --bmc1_min_bound                        0
% 3.34/1.03  --bmc1_max_bound                        -1
% 3.34/1.03  --bmc1_max_bound_default                -1
% 3.34/1.03  --bmc1_symbol_reachability              true
% 3.34/1.03  --bmc1_property_lemmas                  false
% 3.34/1.03  --bmc1_k_induction                      false
% 3.34/1.03  --bmc1_non_equiv_states                 false
% 3.34/1.03  --bmc1_deadlock                         false
% 3.34/1.03  --bmc1_ucm                              false
% 3.34/1.03  --bmc1_add_unsat_core                   none
% 3.34/1.03  --bmc1_unsat_core_children              false
% 3.34/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.03  --bmc1_out_stat                         full
% 3.34/1.03  --bmc1_ground_init                      false
% 3.34/1.03  --bmc1_pre_inst_next_state              false
% 3.34/1.03  --bmc1_pre_inst_state                   false
% 3.34/1.03  --bmc1_pre_inst_reach_state             false
% 3.34/1.03  --bmc1_out_unsat_core                   false
% 3.34/1.03  --bmc1_aig_witness_out                  false
% 3.34/1.03  --bmc1_verbose                          false
% 3.34/1.03  --bmc1_dump_clauses_tptp                false
% 3.34/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.03  --bmc1_dump_file                        -
% 3.34/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.03  --bmc1_ucm_extend_mode                  1
% 3.34/1.03  --bmc1_ucm_init_mode                    2
% 3.34/1.03  --bmc1_ucm_cone_mode                    none
% 3.34/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.03  --bmc1_ucm_relax_model                  4
% 3.34/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.03  --bmc1_ucm_layered_model                none
% 3.34/1.03  --bmc1_ucm_max_lemma_size               10
% 3.34/1.03  
% 3.34/1.03  ------ AIG Options
% 3.34/1.03  
% 3.34/1.03  --aig_mode                              false
% 3.34/1.03  
% 3.34/1.03  ------ Instantiation Options
% 3.34/1.03  
% 3.34/1.03  --instantiation_flag                    true
% 3.34/1.03  --inst_sos_flag                         true
% 3.34/1.03  --inst_sos_phase                        true
% 3.34/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.03  --inst_lit_sel_side                     none
% 3.34/1.03  --inst_solver_per_active                1400
% 3.34/1.03  --inst_solver_calls_frac                1.
% 3.34/1.03  --inst_passive_queue_type               priority_queues
% 3.34/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.03  --inst_passive_queues_freq              [25;2]
% 3.34/1.03  --inst_dismatching                      true
% 3.34/1.03  --inst_eager_unprocessed_to_passive     true
% 3.34/1.03  --inst_prop_sim_given                   true
% 3.34/1.03  --inst_prop_sim_new                     false
% 3.34/1.03  --inst_subs_new                         false
% 3.34/1.03  --inst_eq_res_simp                      false
% 3.34/1.03  --inst_subs_given                       false
% 3.34/1.03  --inst_orphan_elimination               true
% 3.34/1.03  --inst_learning_loop_flag               true
% 3.34/1.03  --inst_learning_start                   3000
% 3.34/1.03  --inst_learning_factor                  2
% 3.34/1.03  --inst_start_prop_sim_after_learn       3
% 3.34/1.03  --inst_sel_renew                        solver
% 3.34/1.03  --inst_lit_activity_flag                true
% 3.34/1.03  --inst_restr_to_given                   false
% 3.34/1.03  --inst_activity_threshold               500
% 3.34/1.03  --inst_out_proof                        true
% 3.34/1.03  
% 3.34/1.03  ------ Resolution Options
% 3.34/1.03  
% 3.34/1.03  --resolution_flag                       false
% 3.34/1.03  --res_lit_sel                           adaptive
% 3.34/1.03  --res_lit_sel_side                      none
% 3.34/1.03  --res_ordering                          kbo
% 3.34/1.03  --res_to_prop_solver                    active
% 3.34/1.03  --res_prop_simpl_new                    false
% 3.34/1.03  --res_prop_simpl_given                  true
% 3.34/1.03  --res_passive_queue_type                priority_queues
% 3.34/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.03  --res_passive_queues_freq               [15;5]
% 3.34/1.03  --res_forward_subs                      full
% 3.34/1.03  --res_backward_subs                     full
% 3.34/1.03  --res_forward_subs_resolution           true
% 3.34/1.03  --res_backward_subs_resolution          true
% 3.34/1.03  --res_orphan_elimination                true
% 3.34/1.03  --res_time_limit                        2.
% 3.34/1.03  --res_out_proof                         true
% 3.34/1.03  
% 3.34/1.03  ------ Superposition Options
% 3.34/1.03  
% 3.34/1.03  --superposition_flag                    true
% 3.34/1.03  --sup_passive_queue_type                priority_queues
% 3.34/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.03  --demod_completeness_check              fast
% 3.34/1.03  --demod_use_ground                      true
% 3.34/1.03  --sup_to_prop_solver                    passive
% 3.34/1.03  --sup_prop_simpl_new                    true
% 3.34/1.03  --sup_prop_simpl_given                  true
% 3.34/1.03  --sup_fun_splitting                     true
% 3.34/1.03  --sup_smt_interval                      50000
% 3.34/1.03  
% 3.34/1.03  ------ Superposition Simplification Setup
% 3.34/1.03  
% 3.34/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.34/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.34/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.34/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.34/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.34/1.03  --sup_immed_triv                        [TrivRules]
% 3.34/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.03  --sup_immed_bw_main                     []
% 3.34/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.34/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.03  --sup_input_bw                          []
% 3.34/1.03  
% 3.34/1.03  ------ Combination Options
% 3.34/1.03  
% 3.34/1.03  --comb_res_mult                         3
% 3.34/1.03  --comb_sup_mult                         2
% 3.34/1.03  --comb_inst_mult                        10
% 3.34/1.03  
% 3.34/1.03  ------ Debug Options
% 3.34/1.03  
% 3.34/1.03  --dbg_backtrace                         false
% 3.34/1.03  --dbg_dump_prop_clauses                 false
% 3.34/1.03  --dbg_dump_prop_clauses_file            -
% 3.34/1.03  --dbg_out_stat                          false
% 3.34/1.03  
% 3.34/1.03  
% 3.34/1.03  
% 3.34/1.03  
% 3.34/1.03  ------ Proving...
% 3.34/1.03  
% 3.34/1.03  
% 3.34/1.03  % SZS status Theorem for theBenchmark.p
% 3.34/1.03  
% 3.34/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/1.03  
% 3.34/1.03  fof(f14,axiom,(
% 3.34/1.03    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f18,plain,(
% 3.34/1.03    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 3.34/1.03    inference(unused_predicate_definition_removal,[],[f14])).
% 3.34/1.03  
% 3.34/1.03  fof(f20,plain,(
% 3.34/1.03    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 3.34/1.03    inference(ennf_transformation,[],[f18])).
% 3.34/1.03  
% 3.34/1.03  fof(f41,plain,(
% 3.34/1.03    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.34/1.03    inference(cnf_transformation,[],[f20])).
% 3.34/1.03  
% 3.34/1.03  fof(f10,axiom,(
% 3.34/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f37,plain,(
% 3.34/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.34/1.03    inference(cnf_transformation,[],[f10])).
% 3.34/1.03  
% 3.34/1.03  fof(f11,axiom,(
% 3.34/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f38,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.34/1.03    inference(cnf_transformation,[],[f11])).
% 3.34/1.03  
% 3.34/1.03  fof(f12,axiom,(
% 3.34/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f39,plain,(
% 3.34/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.34/1.03    inference(cnf_transformation,[],[f12])).
% 3.34/1.03  
% 3.34/1.03  fof(f13,axiom,(
% 3.34/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f40,plain,(
% 3.34/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.34/1.03    inference(cnf_transformation,[],[f13])).
% 3.34/1.03  
% 3.34/1.03  fof(f46,plain,(
% 3.34/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.34/1.03    inference(definition_unfolding,[],[f39,f40])).
% 3.34/1.03  
% 3.34/1.03  fof(f47,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.34/1.03    inference(definition_unfolding,[],[f38,f46])).
% 3.34/1.03  
% 3.34/1.03  fof(f48,plain,(
% 3.34/1.03    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.34/1.03    inference(definition_unfolding,[],[f37,f47])).
% 3.34/1.03  
% 3.34/1.03  fof(f54,plain,(
% 3.34/1.03    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.34/1.03    inference(definition_unfolding,[],[f41,f48])).
% 3.34/1.03  
% 3.34/1.03  fof(f16,conjecture,(
% 3.34/1.03    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f17,negated_conjecture,(
% 3.34/1.03    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.34/1.03    inference(negated_conjecture,[],[f16])).
% 3.34/1.03  
% 3.34/1.03  fof(f21,plain,(
% 3.34/1.03    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 3.34/1.03    inference(ennf_transformation,[],[f17])).
% 3.34/1.03  
% 3.34/1.03  fof(f24,plain,(
% 3.34/1.03    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK0),sK1) != sK1 & r2_hidden(sK0,sK1))),
% 3.34/1.03    introduced(choice_axiom,[])).
% 3.34/1.03  
% 3.34/1.03  fof(f25,plain,(
% 3.34/1.03    k2_xboole_0(k1_tarski(sK0),sK1) != sK1 & r2_hidden(sK0,sK1)),
% 3.34/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f24])).
% 3.34/1.03  
% 3.34/1.03  fof(f43,plain,(
% 3.34/1.03    r2_hidden(sK0,sK1)),
% 3.34/1.03    inference(cnf_transformation,[],[f25])).
% 3.34/1.03  
% 3.34/1.03  fof(f6,axiom,(
% 3.34/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f19,plain,(
% 3.34/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.34/1.03    inference(ennf_transformation,[],[f6])).
% 3.34/1.03  
% 3.34/1.03  fof(f33,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.34/1.03    inference(cnf_transformation,[],[f19])).
% 3.34/1.03  
% 3.34/1.03  fof(f7,axiom,(
% 3.34/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f34,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.34/1.03    inference(cnf_transformation,[],[f7])).
% 3.34/1.03  
% 3.34/1.03  fof(f9,axiom,(
% 3.34/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f36,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.34/1.03    inference(cnf_transformation,[],[f9])).
% 3.34/1.03  
% 3.34/1.03  fof(f45,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.34/1.03    inference(definition_unfolding,[],[f36,f30])).
% 3.34/1.03  
% 3.34/1.03  fof(f3,axiom,(
% 3.34/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f30,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.34/1.03    inference(cnf_transformation,[],[f3])).
% 3.34/1.03  
% 3.34/1.03  fof(f52,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) )),
% 3.34/1.03    inference(definition_unfolding,[],[f34,f45,f45,f30])).
% 3.34/1.03  
% 3.34/1.03  fof(f15,axiom,(
% 3.34/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f42,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.34/1.03    inference(cnf_transformation,[],[f15])).
% 3.34/1.03  
% 3.34/1.03  fof(f55,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.34/1.03    inference(definition_unfolding,[],[f42,f45,f47])).
% 3.34/1.03  
% 3.34/1.03  fof(f8,axiom,(
% 3.34/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f35,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.34/1.03    inference(cnf_transformation,[],[f8])).
% 3.34/1.03  
% 3.34/1.03  fof(f53,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))) )),
% 3.34/1.03    inference(definition_unfolding,[],[f35,f30,f30,f45])).
% 3.34/1.03  
% 3.34/1.03  fof(f4,axiom,(
% 3.34/1.03    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f31,plain,(
% 3.34/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.34/1.03    inference(cnf_transformation,[],[f4])).
% 3.34/1.03  
% 3.34/1.03  fof(f50,plain,(
% 3.34/1.03    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 3.34/1.03    inference(definition_unfolding,[],[f31,f45])).
% 3.34/1.03  
% 3.34/1.03  fof(f1,axiom,(
% 3.34/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f26,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.34/1.03    inference(cnf_transformation,[],[f1])).
% 3.34/1.03  
% 3.34/1.03  fof(f49,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.34/1.03    inference(definition_unfolding,[],[f26,f45,f45])).
% 3.34/1.03  
% 3.34/1.03  fof(f2,axiom,(
% 3.34/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f22,plain,(
% 3.34/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/1.03    inference(nnf_transformation,[],[f2])).
% 3.34/1.03  
% 3.34/1.03  fof(f23,plain,(
% 3.34/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/1.03    inference(flattening,[],[f22])).
% 3.34/1.03  
% 3.34/1.03  fof(f27,plain,(
% 3.34/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.34/1.03    inference(cnf_transformation,[],[f23])).
% 3.34/1.03  
% 3.34/1.03  fof(f58,plain,(
% 3.34/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.34/1.03    inference(equality_resolution,[],[f27])).
% 3.34/1.03  
% 3.34/1.03  fof(f5,axiom,(
% 3.34/1.03    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.34/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.03  
% 3.34/1.03  fof(f32,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.34/1.03    inference(cnf_transformation,[],[f5])).
% 3.34/1.03  
% 3.34/1.03  fof(f51,plain,(
% 3.34/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0) )),
% 3.34/1.03    inference(definition_unfolding,[],[f32,f45])).
% 3.34/1.03  
% 3.34/1.03  fof(f44,plain,(
% 3.34/1.03    k2_xboole_0(k1_tarski(sK0),sK1) != sK1),
% 3.34/1.03    inference(cnf_transformation,[],[f25])).
% 3.34/1.03  
% 3.34/1.03  fof(f56,plain,(
% 3.34/1.03    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1),
% 3.34/1.03    inference(definition_unfolding,[],[f44,f45,f48])).
% 3.34/1.03  
% 3.34/1.03  cnf(c_9,plain,
% 3.34/1.03      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 3.34/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_12,negated_conjecture,
% 3.34/1.03      ( r2_hidden(sK0,sK1) ),
% 3.34/1.03      inference(cnf_transformation,[],[f43]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_82,plain,
% 3.34/1.03      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
% 3.34/1.03      | sK1 != X1
% 3.34/1.03      | sK0 != X0 ),
% 3.34/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_12]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_83,plain,
% 3.34/1.03      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
% 3.34/1.03      inference(unflattening,[status(thm)],[c_82]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_206,plain,
% 3.34/1.03      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
% 3.34/1.03      inference(predicate_to_equality,[status(thm)],[c_83]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_6,plain,
% 3.34/1.03      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.34/1.03      inference(cnf_transformation,[],[f33]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_207,plain,
% 3.34/1.03      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.34/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_374,plain,
% 3.34/1.03      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_206,c_207]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_7,plain,
% 3.34/1.03      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 3.34/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_649,plain,
% 3.34/1.03      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1))) = k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_374,c_7]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_10,plain,
% 3.34/1.03      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 3.34/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_616,plain,
% 3.34/1.03      ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_374,c_10]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_651,plain,
% 3.34/1.03      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1))) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 3.34/1.03      inference(light_normalisation,[status(thm)],[c_649,c_374,c_616]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_8,plain,
% 3.34/1.03      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 3.34/1.03      inference(cnf_transformation,[],[f53]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1135,plain,
% 3.34/1.03      ( k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_651,c_8]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_4,plain,
% 3.34/1.03      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 3.34/1.03      inference(cnf_transformation,[],[f50]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_0,plain,
% 3.34/1.03      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.34/1.03      inference(cnf_transformation,[],[f49]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_606,plain,
% 3.34/1.03      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_922,plain,
% 3.34/1.03      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_606,c_7]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_923,plain,
% 3.34/1.03      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.34/1.03      inference(demodulation,[status(thm)],[c_922,c_606]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_924,plain,
% 3.34/1.03      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.34/1.03      inference(demodulation,[status(thm)],[c_923,c_606]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1136,plain,
% 3.34/1.03      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_924,c_8]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_3,plain,
% 3.34/1.03      ( r1_tarski(X0,X0) ),
% 3.34/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_208,plain,
% 3.34/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 3.34/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_373,plain,
% 3.34/1.03      ( k3_xboole_0(X0,X0) = X0 ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_208,c_207]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_5,plain,
% 3.34/1.03      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
% 3.34/1.03      inference(cnf_transformation,[],[f51]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_921,plain,
% 3.34/1.03      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_606,c_5]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1150,plain,
% 3.34/1.03      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.34/1.03      inference(light_normalisation,
% 3.34/1.03                [status(thm)],
% 3.34/1.03                [c_1136,c_373,c_921,c_923]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1151,plain,
% 3.34/1.03      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.34/1.03      inference(demodulation,[status(thm)],[c_1150,c_924]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1152,plain,
% 3.34/1.03      ( k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)) ),
% 3.34/1.03      inference(demodulation,[status(thm)],[c_1135,c_1151]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1153,plain,
% 3.34/1.03      ( k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0)) = sK1 ),
% 3.34/1.03      inference(demodulation,[status(thm)],[c_1152,c_923]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1300,plain,
% 3.34/1.03      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k3_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_1153,c_8]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1308,plain,
% 3.34/1.03      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) = k1_xboole_0 ),
% 3.34/1.03      inference(demodulation,[status(thm)],[c_1300,c_921,c_924]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1309,plain,
% 3.34/1.03      ( k5_xboole_0(k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0),k3_xboole_0(k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k1_xboole_0),sK1)) = k5_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),sK1)) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_1308,c_8]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1006,plain,
% 3.34/1.03      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 3.34/1.03      inference(demodulation,[status(thm)],[c_924,c_4]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1008,plain,
% 3.34/1.03      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.34/1.03      inference(demodulation,[status(thm)],[c_921,c_1006]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_617,plain,
% 3.34/1.03      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1132,plain,
% 3.34/1.03      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X0)) = k5_xboole_0(X1,k3_xboole_0(X1,X0)) ),
% 3.34/1.03      inference(superposition,[status(thm)],[c_617,c_8]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1322,plain,
% 3.34/1.03      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k1_xboole_0 ),
% 3.34/1.03      inference(demodulation,
% 3.34/1.03                [status(thm)],
% 3.34/1.03                [c_1309,c_374,c_1008,c_1132,c_1151]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1323,plain,
% 3.34/1.03      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 3.34/1.03      inference(light_normalisation,[status(thm)],[c_1322,c_374]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1454,plain,
% 3.34/1.03      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k1_xboole_0) ),
% 3.34/1.03      inference(demodulation,[status(thm)],[c_1323,c_616]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_1455,plain,
% 3.34/1.03      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = sK1 ),
% 3.34/1.03      inference(demodulation,[status(thm)],[c_1454,c_1008]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_11,negated_conjecture,
% 3.34/1.03      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 3.34/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_604,plain,
% 3.34/1.03      ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) != sK1 ),
% 3.34/1.03      inference(demodulation,[status(thm)],[c_0,c_11]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_605,plain,
% 3.34/1.03      ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 3.34/1.03      inference(light_normalisation,[status(thm)],[c_604,c_374]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(c_655,plain,
% 3.34/1.03      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 3.34/1.03      inference(light_normalisation,[status(thm)],[c_605,c_616]) ).
% 3.34/1.03  
% 3.34/1.03  cnf(contradiction,plain,
% 3.34/1.03      ( $false ),
% 3.34/1.03      inference(minisat,[status(thm)],[c_1455,c_655]) ).
% 3.34/1.03  
% 3.34/1.03  
% 3.34/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/1.03  
% 3.34/1.03  ------                               Statistics
% 3.34/1.03  
% 3.34/1.03  ------ General
% 3.34/1.03  
% 3.34/1.03  abstr_ref_over_cycles:                  0
% 3.34/1.03  abstr_ref_under_cycles:                 0
% 3.34/1.03  gc_basic_clause_elim:                   0
% 3.34/1.03  forced_gc_time:                         0
% 3.34/1.03  parsing_time:                           0.006
% 3.34/1.03  unif_index_cands_time:                  0.
% 3.34/1.03  unif_index_add_time:                    0.
% 3.34/1.03  orderings_time:                         0.
% 3.34/1.03  out_proof_time:                         0.011
% 3.34/1.03  total_time:                             0.075
% 3.34/1.03  num_of_symbols:                         40
% 3.34/1.03  num_of_terms:                           1994
% 3.34/1.03  
% 3.34/1.03  ------ Preprocessing
% 3.34/1.03  
% 3.34/1.03  num_of_splits:                          0
% 3.34/1.03  num_of_split_atoms:                     0
% 3.34/1.03  num_of_reused_defs:                     0
% 3.34/1.03  num_eq_ax_congr_red:                    1
% 3.34/1.03  num_of_sem_filtered_clauses:            1
% 3.34/1.03  num_of_subtypes:                        0
% 3.34/1.03  monotx_restored_types:                  0
% 3.34/1.03  sat_num_of_epr_types:                   0
% 3.34/1.03  sat_num_of_non_cyclic_types:            0
% 3.34/1.03  sat_guarded_non_collapsed_types:        0
% 3.34/1.03  num_pure_diseq_elim:                    0
% 3.34/1.03  simp_replaced_by:                       0
% 3.34/1.03  res_preprocessed:                       60
% 3.34/1.03  prep_upred:                             0
% 3.34/1.03  prep_unflattend:                        2
% 3.34/1.03  smt_new_axioms:                         0
% 3.34/1.03  pred_elim_cands:                        1
% 3.34/1.03  pred_elim:                              1
% 3.34/1.03  pred_elim_cl:                           1
% 3.34/1.03  pred_elim_cycles:                       3
% 3.34/1.03  merged_defs:                            0
% 3.34/1.03  merged_defs_ncl:                        0
% 3.34/1.03  bin_hyper_res:                          0
% 3.34/1.03  prep_cycles:                            4
% 3.34/1.03  pred_elim_time:                         0.
% 3.34/1.03  splitting_time:                         0.
% 3.34/1.03  sem_filter_time:                        0.
% 3.34/1.03  monotx_time:                            0.
% 3.34/1.03  subtype_inf_time:                       0.
% 3.34/1.03  
% 3.34/1.03  ------ Problem properties
% 3.34/1.03  
% 3.34/1.03  clauses:                                11
% 3.34/1.03  conjectures:                            1
% 3.34/1.03  epr:                                    2
% 3.34/1.03  horn:                                   11
% 3.34/1.03  ground:                                 2
% 3.34/1.03  unary:                                  9
% 3.34/1.03  binary:                                 1
% 3.34/1.03  lits:                                   14
% 3.34/1.03  lits_eq:                                9
% 3.34/1.03  fd_pure:                                0
% 3.34/1.03  fd_pseudo:                              0
% 3.34/1.03  fd_cond:                                0
% 3.34/1.03  fd_pseudo_cond:                         1
% 3.34/1.03  ac_symbols:                             0
% 3.34/1.03  
% 3.34/1.03  ------ Propositional Solver
% 3.34/1.03  
% 3.34/1.03  prop_solver_calls:                      30
% 3.34/1.03  prop_fast_solver_calls:                 242
% 3.34/1.03  smt_solver_calls:                       0
% 3.34/1.03  smt_fast_solver_calls:                  0
% 3.34/1.03  prop_num_of_clauses:                    682
% 3.34/1.03  prop_preprocess_simplified:             1964
% 3.34/1.03  prop_fo_subsumed:                       0
% 3.34/1.03  prop_solver_time:                       0.
% 3.34/1.03  smt_solver_time:                        0.
% 3.34/1.03  smt_fast_solver_time:                   0.
% 3.34/1.03  prop_fast_solver_time:                  0.
% 3.34/1.03  prop_unsat_core_time:                   0.
% 3.34/1.03  
% 3.34/1.03  ------ QBF
% 3.34/1.03  
% 3.34/1.03  qbf_q_res:                              0
% 3.34/1.03  qbf_num_tautologies:                    0
% 3.34/1.03  qbf_prep_cycles:                        0
% 3.34/1.03  
% 3.34/1.03  ------ BMC1
% 3.34/1.03  
% 3.34/1.03  bmc1_current_bound:                     -1
% 3.34/1.03  bmc1_last_solved_bound:                 -1
% 3.34/1.03  bmc1_unsat_core_size:                   -1
% 3.34/1.03  bmc1_unsat_core_parents_size:           -1
% 3.34/1.03  bmc1_merge_next_fun:                    0
% 3.34/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.34/1.03  
% 3.34/1.03  ------ Instantiation
% 3.34/1.03  
% 3.34/1.03  inst_num_of_clauses:                    229
% 3.34/1.03  inst_num_in_passive:                    38
% 3.34/1.03  inst_num_in_active:                     122
% 3.34/1.03  inst_num_in_unprocessed:                69
% 3.34/1.03  inst_num_of_loops:                      150
% 3.34/1.03  inst_num_of_learning_restarts:          0
% 3.34/1.03  inst_num_moves_active_passive:          22
% 3.34/1.03  inst_lit_activity:                      0
% 3.34/1.03  inst_lit_activity_moves:                0
% 3.34/1.03  inst_num_tautologies:                   0
% 3.34/1.03  inst_num_prop_implied:                  0
% 3.34/1.03  inst_num_existing_simplified:           0
% 3.34/1.03  inst_num_eq_res_simplified:             0
% 3.34/1.03  inst_num_child_elim:                    0
% 3.34/1.03  inst_num_of_dismatching_blockings:      66
% 3.34/1.03  inst_num_of_non_proper_insts:           294
% 3.34/1.03  inst_num_of_duplicates:                 0
% 3.34/1.03  inst_inst_num_from_inst_to_res:         0
% 3.34/1.03  inst_dismatching_checking_time:         0.
% 3.34/1.03  
% 3.34/1.03  ------ Resolution
% 3.34/1.03  
% 3.34/1.03  res_num_of_clauses:                     0
% 3.34/1.03  res_num_in_passive:                     0
% 3.34/1.03  res_num_in_active:                      0
% 3.34/1.03  res_num_of_loops:                       64
% 3.34/1.03  res_forward_subset_subsumed:            52
% 3.34/1.03  res_backward_subset_subsumed:           0
% 3.34/1.03  res_forward_subsumed:                   0
% 3.34/1.03  res_backward_subsumed:                  0
% 3.34/1.03  res_forward_subsumption_resolution:     0
% 3.34/1.03  res_backward_subsumption_resolution:    0
% 3.34/1.03  res_clause_to_clause_subsumption:       139
% 3.34/1.03  res_orphan_elimination:                 0
% 3.34/1.03  res_tautology_del:                      19
% 3.34/1.03  res_num_eq_res_simplified:              0
% 3.34/1.03  res_num_sel_changes:                    0
% 3.34/1.03  res_moves_from_active_to_pass:          0
% 3.34/1.03  
% 3.34/1.03  ------ Superposition
% 3.34/1.03  
% 3.34/1.03  sup_time_total:                         0.
% 3.34/1.03  sup_time_generating:                    0.
% 3.34/1.03  sup_time_sim_full:                      0.
% 3.34/1.03  sup_time_sim_immed:                     0.
% 3.34/1.03  
% 3.34/1.03  sup_num_of_clauses:                     39
% 3.34/1.03  sup_num_in_active:                      21
% 3.34/1.03  sup_num_in_passive:                     18
% 3.34/1.03  sup_num_of_loops:                       28
% 3.34/1.03  sup_fw_superposition:                   65
% 3.34/1.03  sup_bw_superposition:                   60
% 3.34/1.03  sup_immediate_simplified:               52
% 3.34/1.03  sup_given_eliminated:                   1
% 3.34/1.03  comparisons_done:                       0
% 3.34/1.03  comparisons_avoided:                    0
% 3.34/1.03  
% 3.34/1.03  ------ Simplifications
% 3.34/1.03  
% 3.34/1.03  
% 3.34/1.03  sim_fw_subset_subsumed:                 0
% 3.34/1.03  sim_bw_subset_subsumed:                 0
% 3.34/1.03  sim_fw_subsumed:                        3
% 3.34/1.03  sim_bw_subsumed:                        3
% 3.34/1.03  sim_fw_subsumption_res:                 0
% 3.34/1.03  sim_bw_subsumption_res:                 0
% 3.34/1.03  sim_tautology_del:                      0
% 3.34/1.03  sim_eq_tautology_del:                   23
% 3.34/1.03  sim_eq_res_simp:                        0
% 3.34/1.03  sim_fw_demodulated:                     34
% 3.34/1.03  sim_bw_demodulated:                     7
% 3.34/1.03  sim_light_normalised:                   26
% 3.34/1.03  sim_joinable_taut:                      0
% 3.34/1.03  sim_joinable_simp:                      0
% 3.34/1.03  sim_ac_normalised:                      0
% 3.34/1.03  sim_smt_subsumption:                    0
% 3.34/1.03  
%------------------------------------------------------------------------------
