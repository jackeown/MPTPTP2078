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
% DateTime   : Thu Dec  3 11:35:26 EST 2020

% Result     : Theorem 31.86s
% Output     : CNFRefutation 31.86s
% Verified   : 
% Statistics : Number of formulae       :  169 (8072 expanded)
%              Number of clauses        :  116 (2058 expanded)
%              Number of leaves         :   17 (2404 expanded)
%              Depth                    :   27
%              Number of atoms          :  192 (8494 expanded)
%              Number of equality atoms :  157 (8117 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f40])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) ),
    inference(definition_unfolding,[],[f38,f52,f40,f55])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) ),
    inference(definition_unfolding,[],[f36,f52,f40,f40])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) )
   => ( ~ r2_hidden(sK0,sK2)
      & k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r2_hidden(sK0,sK2)
    & k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).

fof(f50,plain,(
    k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f35,f52])).

fof(f68,plain,(
    k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))) = k1_enumset1(sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f50,f53,f40,f40])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k1_enumset1(X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f31,f53])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f30,f52])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f32,f53])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X3,X3,X2),k1_enumset1(X3,X3,X2),k1_enumset1(X1,X1,X0))) ),
    inference(definition_unfolding,[],[f37,f54,f54])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f25])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k1_enumset1(X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f47,f40])).

fof(f51,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_464,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_6])).

cnf(c_0,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_8,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_598,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_14,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))) = k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_126,negated_conjecture,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)))) = k1_enumset1(sK0,sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_14,c_5,c_1])).

cnf(c_461,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))),X0)) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_126,c_5])).

cnf(c_1239,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2))),X0)) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0) ),
    inference(demodulation,[status(thm)],[c_598,c_461])).

cnf(c_1731,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2))),X0))) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_464,c_1239])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k1_enumset1(X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_128,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X0)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_3,c_5,c_1])).

cnf(c_2,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_245,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_128,c_2,c_6])).

cnf(c_460,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_405,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_245,c_1])).

cnf(c_468,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_460,c_405])).

cnf(c_252,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_1368,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_252])).

cnf(c_1408,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_1368,c_245])).

cnf(c_1748,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_1731,c_245,c_468,c_1408])).

cnf(c_1756,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0)) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0) ),
    inference(demodulation,[status(thm)],[c_1748,c_1239])).

cnf(c_5187,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_5,c_468])).

cnf(c_5672,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,X2),X0)) = X2 ),
    inference(superposition,[status(thm)],[c_1,c_5187])).

cnf(c_7147,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X2,X1),X0)) = X2 ),
    inference(superposition,[status(thm)],[c_1,c_5672])).

cnf(c_8951,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X1),X0))) = X2 ),
    inference(superposition,[status(thm)],[c_7147,c_5])).

cnf(c_9862,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0)) = k1_enumset1(sK0,sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1756,c_8951])).

cnf(c_666,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))),X0),X1)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1) ),
    inference(superposition,[status(thm)],[c_461,c_5])).

cnf(c_664,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_5,c_461])).

cnf(c_779,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))) = k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_6,c_664])).

cnf(c_782,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))) = k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_779,c_245])).

cnf(c_841,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0),X1)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_666,c_666,c_782])).

cnf(c_4,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_127,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k1_enumset1(X0,X0,X1)))),X0) ),
    inference(theory_normalisation,[status(thm)],[c_4,c_5,c_1])).

cnf(c_244,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k1_enumset1(X0,X0,X1)))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_127])).

cnf(c_3395,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0)))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_841,c_244])).

cnf(c_781,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0)),X1)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1) ),
    inference(superposition,[status(thm)],[c_664,c_5])).

cnf(c_4346,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0))),X1) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_xboole_0),X1)) ),
    inference(superposition,[status(thm)],[c_464,c_781])).

cnf(c_1197,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0))) = k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_464,c_664])).

cnf(c_1207,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0))) = k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_1197,c_245])).

cnf(c_4408,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_xboole_0),X0)) = k5_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_4346,c_1207])).

cnf(c_4409,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0)) = k5_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0) ),
    inference(demodulation,[status(thm)],[c_4408,c_245])).

cnf(c_61631,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0))))),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3395,c_4409])).

cnf(c_254,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_1240,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2)))) = k1_enumset1(sK0,sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_598,c_126])).

cnf(c_1575,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2))))) = k5_xboole_0(X0,k1_enumset1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1240,c_252])).

cnf(c_1758,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))) = k5_xboole_0(X0,k1_enumset1(sK0,sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_1575,c_1575,c_1748])).

cnf(c_2391,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(sK2,X0))) = k5_xboole_0(X0,k1_enumset1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_254,c_1758])).

cnf(c_5227,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_468,c_254])).

cnf(c_5284,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_5227,c_5])).

cnf(c_6132,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_5284])).

cnf(c_6097,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X3,X2) ),
    inference(superposition,[status(thm)],[c_5,c_5284])).

cnf(c_22309,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X3,X1),X2) ),
    inference(superposition,[status(thm)],[c_6132,c_6097])).

cnf(c_22321,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X2,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_22309,c_6])).

cnf(c_22749,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(sK2,X0)),X1),sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(X0,k1_enumset1(sK0,sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_2391,c_22321])).

cnf(c_6093,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_6,c_5284])).

cnf(c_6926,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5,c_6093])).

cnf(c_16341,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_6926])).

cnf(c_22807,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X3,X1)))) ),
    inference(superposition,[status(thm)],[c_22321,c_16341])).

cnf(c_22820,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_22321,c_254])).

cnf(c_253,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_16430,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)) = k5_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_6926,c_253])).

cnf(c_22910,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
    inference(light_normalisation,[status(thm)],[c_22820,c_16430])).

cnf(c_22939,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k1_xboole_0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X3,X1),X0),X2) ),
    inference(demodulation,[status(thm)],[c_22807,c_22321,c_22910])).

cnf(c_22228,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X4,X0)) = k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X1,X2))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6132,c_6926])).

cnf(c_9900,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X1,X0)) = X2 ),
    inference(superposition,[status(thm)],[c_7147,c_8951])).

cnf(c_10389,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X0)) = X2 ),
    inference(light_normalisation,[status(thm)],[c_9900,c_5])).

cnf(c_22231,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X4,X0)) = k5_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X3,X1))) ),
    inference(superposition,[status(thm)],[c_6132,c_10389])).

cnf(c_22396,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_22228,c_22231])).

cnf(c_22940,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),X3) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X3))) ),
    inference(light_normalisation,[status(thm)],[c_22939,c_22396])).

cnf(c_23072,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(sK2,X0)),X1),sK2) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X1),X0) ),
    inference(demodulation,[status(thm)],[c_22749,c_22321,c_22940])).

cnf(c_6141,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X1),X2))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X1),X2),sK2) ),
    inference(superposition,[status(thm)],[c_841,c_5284])).

cnf(c_6290,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0),X1),sK2) = k5_xboole_0(X1,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0)) ),
    inference(demodulation,[status(thm)],[c_6141,c_5284])).

cnf(c_5722,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0)),X1) = k5_xboole_0(k5_xboole_0(X2,sK2),k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1))) ),
    inference(superposition,[status(thm)],[c_781,c_5187])).

cnf(c_1573,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2))),k1_enumset1(sK0,sK0,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1240,c_464])).

cnf(c_2257,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2))),k1_enumset1(sK0,sK0,sK1)),k5_xboole_0(sK2,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1573,c_253])).

cnf(c_1766,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_1758])).

cnf(c_1786,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),k1_enumset1(sK0,sK0,sK1)) = sK2 ),
    inference(demodulation,[status(thm)],[c_1766,c_245])).

cnf(c_2298,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2257,c_245,c_1748,c_1786])).

cnf(c_4669,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2298,c_5])).

cnf(c_5745,plain,
    ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(sK2,X1),X2) ),
    inference(superposition,[status(thm)],[c_4669,c_5187])).

cnf(c_5831,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0)),X1) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0)),X1) ),
    inference(demodulation,[status(thm)],[c_5722,c_5745])).

cnf(c_4652,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0)),X1) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1)) ),
    inference(superposition,[status(thm)],[c_781,c_2298])).

cnf(c_5832,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1)) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_5831,c_4652])).

cnf(c_6291,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1)),sK2) = k5_xboole_0(X1,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0)) ),
    inference(light_normalisation,[status(thm)],[c_6290,c_4409,c_5832])).

cnf(c_9996,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))))),X2) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X1),X2)) ),
    inference(superposition,[status(thm)],[c_8951,c_781])).

cnf(c_663,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)))) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_461])).

cnf(c_668,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)))) = sK2 ),
    inference(demodulation,[status(thm)],[c_663,c_245,c_468])).

cnf(c_870,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_668,c_668,c_782])).

cnf(c_1185,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0)),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_664,c_464])).

cnf(c_3251,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)))),sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_870,c_1185])).

cnf(c_1373,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)))) = k5_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_870,c_252])).

cnf(c_2369,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2))),k1_enumset1(sK0,sK0,sK1)),k5_xboole_0(X0,sK2)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1573,c_254])).

cnf(c_2416,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,sK2)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2369,c_245,c_1748,c_1786])).

cnf(c_3289,plain,
    ( k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3251,c_781,c_1373,c_2416])).

cnf(c_6529,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3289,c_2416])).

cnf(c_6535,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_6529,c_245])).

cnf(c_8963,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),sK2)) = k5_xboole_0(sK2,X1) ),
    inference(superposition,[status(thm)],[c_7147,c_4669])).

cnf(c_10300,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(sK2,X0)),X1) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_9996,c_6535,c_8963])).

cnf(c_23073,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X1)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_23072,c_6291,c_10300])).

cnf(c_61632,plain,
    ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0)))))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_61631,c_23073])).

cnf(c_61660,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_9862,c_61632])).

cnf(c_7,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X3,X3,X2),k1_enumset1(X3,X3,X2),k1_enumset1(X1,X1,X0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_657,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X2,X1,X0) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_14445,plain,
    ( k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(superposition,[status(thm)],[c_657,c_8])).

cnf(c_14772,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))) = sK2 ),
    inference(demodulation,[status(thm)],[c_14445,c_1748])).

cnf(c_61721,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_61660,c_14772])).

cnf(c_61722,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_61721,c_2416])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_enumset1(X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_241,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k1_enumset1(X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_101194,plain,
    ( r2_hidden(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_61722,c_241])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_15,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_101194,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:46:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 31.86/4.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.86/4.49  
% 31.86/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.86/4.49  
% 31.86/4.49  ------  iProver source info
% 31.86/4.49  
% 31.86/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.86/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.86/4.49  git: non_committed_changes: false
% 31.86/4.49  git: last_make_outside_of_git: false
% 31.86/4.49  
% 31.86/4.49  ------ 
% 31.86/4.49  
% 31.86/4.49  ------ Input Options
% 31.86/4.49  
% 31.86/4.49  --out_options                           all
% 31.86/4.49  --tptp_safe_out                         true
% 31.86/4.49  --problem_path                          ""
% 31.86/4.49  --include_path                          ""
% 31.86/4.49  --clausifier                            res/vclausify_rel
% 31.86/4.49  --clausifier_options                    ""
% 31.86/4.49  --stdin                                 false
% 31.86/4.49  --stats_out                             all
% 31.86/4.49  
% 31.86/4.49  ------ General Options
% 31.86/4.49  
% 31.86/4.49  --fof                                   false
% 31.86/4.49  --time_out_real                         305.
% 31.86/4.49  --time_out_virtual                      -1.
% 31.86/4.49  --symbol_type_check                     false
% 31.86/4.49  --clausify_out                          false
% 31.86/4.49  --sig_cnt_out                           false
% 31.86/4.49  --trig_cnt_out                          false
% 31.86/4.49  --trig_cnt_out_tolerance                1.
% 31.86/4.49  --trig_cnt_out_sk_spl                   false
% 31.86/4.49  --abstr_cl_out                          false
% 31.86/4.49  
% 31.86/4.49  ------ Global Options
% 31.86/4.49  
% 31.86/4.49  --schedule                              default
% 31.86/4.49  --add_important_lit                     false
% 31.86/4.49  --prop_solver_per_cl                    1000
% 31.86/4.49  --min_unsat_core                        false
% 31.86/4.49  --soft_assumptions                      false
% 31.86/4.49  --soft_lemma_size                       3
% 31.86/4.49  --prop_impl_unit_size                   0
% 31.86/4.49  --prop_impl_unit                        []
% 31.86/4.49  --share_sel_clauses                     true
% 31.86/4.49  --reset_solvers                         false
% 31.86/4.49  --bc_imp_inh                            [conj_cone]
% 31.86/4.49  --conj_cone_tolerance                   3.
% 31.86/4.49  --extra_neg_conj                        none
% 31.86/4.49  --large_theory_mode                     true
% 31.86/4.49  --prolific_symb_bound                   200
% 31.86/4.49  --lt_threshold                          2000
% 31.86/4.49  --clause_weak_htbl                      true
% 31.86/4.49  --gc_record_bc_elim                     false
% 31.86/4.49  
% 31.86/4.49  ------ Preprocessing Options
% 31.86/4.49  
% 31.86/4.49  --preprocessing_flag                    true
% 31.86/4.49  --time_out_prep_mult                    0.1
% 31.86/4.49  --splitting_mode                        input
% 31.86/4.49  --splitting_grd                         true
% 31.86/4.49  --splitting_cvd                         false
% 31.86/4.49  --splitting_cvd_svl                     false
% 31.86/4.49  --splitting_nvd                         32
% 31.86/4.49  --sub_typing                            true
% 31.86/4.49  --prep_gs_sim                           true
% 31.86/4.49  --prep_unflatten                        true
% 31.86/4.49  --prep_res_sim                          true
% 31.86/4.49  --prep_upred                            true
% 31.86/4.49  --prep_sem_filter                       exhaustive
% 31.86/4.49  --prep_sem_filter_out                   false
% 31.86/4.49  --pred_elim                             true
% 31.86/4.49  --res_sim_input                         true
% 31.86/4.49  --eq_ax_congr_red                       true
% 31.86/4.49  --pure_diseq_elim                       true
% 31.86/4.49  --brand_transform                       false
% 31.86/4.49  --non_eq_to_eq                          false
% 31.86/4.49  --prep_def_merge                        true
% 31.86/4.49  --prep_def_merge_prop_impl              false
% 31.86/4.49  --prep_def_merge_mbd                    true
% 31.86/4.49  --prep_def_merge_tr_red                 false
% 31.86/4.49  --prep_def_merge_tr_cl                  false
% 31.86/4.49  --smt_preprocessing                     true
% 31.86/4.49  --smt_ac_axioms                         fast
% 31.86/4.49  --preprocessed_out                      false
% 31.86/4.49  --preprocessed_stats                    false
% 31.86/4.49  
% 31.86/4.49  ------ Abstraction refinement Options
% 31.86/4.49  
% 31.86/4.49  --abstr_ref                             []
% 31.86/4.49  --abstr_ref_prep                        false
% 31.86/4.49  --abstr_ref_until_sat                   false
% 31.86/4.49  --abstr_ref_sig_restrict                funpre
% 31.86/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.86/4.49  --abstr_ref_under                       []
% 31.86/4.49  
% 31.86/4.49  ------ SAT Options
% 31.86/4.49  
% 31.86/4.49  --sat_mode                              false
% 31.86/4.49  --sat_fm_restart_options                ""
% 31.86/4.49  --sat_gr_def                            false
% 31.86/4.49  --sat_epr_types                         true
% 31.86/4.49  --sat_non_cyclic_types                  false
% 31.86/4.49  --sat_finite_models                     false
% 31.86/4.49  --sat_fm_lemmas                         false
% 31.86/4.49  --sat_fm_prep                           false
% 31.86/4.49  --sat_fm_uc_incr                        true
% 31.86/4.49  --sat_out_model                         small
% 31.86/4.49  --sat_out_clauses                       false
% 31.86/4.49  
% 31.86/4.49  ------ QBF Options
% 31.86/4.49  
% 31.86/4.49  --qbf_mode                              false
% 31.86/4.49  --qbf_elim_univ                         false
% 31.86/4.49  --qbf_dom_inst                          none
% 31.86/4.49  --qbf_dom_pre_inst                      false
% 31.86/4.49  --qbf_sk_in                             false
% 31.86/4.49  --qbf_pred_elim                         true
% 31.86/4.49  --qbf_split                             512
% 31.86/4.49  
% 31.86/4.49  ------ BMC1 Options
% 31.86/4.49  
% 31.86/4.49  --bmc1_incremental                      false
% 31.86/4.49  --bmc1_axioms                           reachable_all
% 31.86/4.49  --bmc1_min_bound                        0
% 31.86/4.49  --bmc1_max_bound                        -1
% 31.86/4.49  --bmc1_max_bound_default                -1
% 31.86/4.49  --bmc1_symbol_reachability              true
% 31.86/4.49  --bmc1_property_lemmas                  false
% 31.86/4.49  --bmc1_k_induction                      false
% 31.86/4.49  --bmc1_non_equiv_states                 false
% 31.86/4.49  --bmc1_deadlock                         false
% 31.86/4.49  --bmc1_ucm                              false
% 31.86/4.49  --bmc1_add_unsat_core                   none
% 31.86/4.49  --bmc1_unsat_core_children              false
% 31.86/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.86/4.49  --bmc1_out_stat                         full
% 31.86/4.49  --bmc1_ground_init                      false
% 31.86/4.49  --bmc1_pre_inst_next_state              false
% 31.86/4.49  --bmc1_pre_inst_state                   false
% 31.86/4.49  --bmc1_pre_inst_reach_state             false
% 31.86/4.49  --bmc1_out_unsat_core                   false
% 31.86/4.49  --bmc1_aig_witness_out                  false
% 31.86/4.49  --bmc1_verbose                          false
% 31.86/4.49  --bmc1_dump_clauses_tptp                false
% 31.86/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.86/4.49  --bmc1_dump_file                        -
% 31.86/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.86/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.86/4.49  --bmc1_ucm_extend_mode                  1
% 31.86/4.49  --bmc1_ucm_init_mode                    2
% 31.86/4.49  --bmc1_ucm_cone_mode                    none
% 31.86/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.86/4.49  --bmc1_ucm_relax_model                  4
% 31.86/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.86/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.86/4.49  --bmc1_ucm_layered_model                none
% 31.86/4.49  --bmc1_ucm_max_lemma_size               10
% 31.86/4.49  
% 31.86/4.49  ------ AIG Options
% 31.86/4.49  
% 31.86/4.49  --aig_mode                              false
% 31.86/4.49  
% 31.86/4.49  ------ Instantiation Options
% 31.86/4.49  
% 31.86/4.49  --instantiation_flag                    true
% 31.86/4.49  --inst_sos_flag                         true
% 31.86/4.49  --inst_sos_phase                        true
% 31.86/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.86/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.86/4.49  --inst_lit_sel_side                     num_symb
% 31.86/4.49  --inst_solver_per_active                1400
% 31.86/4.49  --inst_solver_calls_frac                1.
% 31.86/4.49  --inst_passive_queue_type               priority_queues
% 31.86/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.86/4.49  --inst_passive_queues_freq              [25;2]
% 31.86/4.49  --inst_dismatching                      true
% 31.86/4.49  --inst_eager_unprocessed_to_passive     true
% 31.86/4.49  --inst_prop_sim_given                   true
% 31.86/4.49  --inst_prop_sim_new                     false
% 31.86/4.49  --inst_subs_new                         false
% 31.86/4.49  --inst_eq_res_simp                      false
% 31.86/4.49  --inst_subs_given                       false
% 31.86/4.49  --inst_orphan_elimination               true
% 31.86/4.49  --inst_learning_loop_flag               true
% 31.86/4.49  --inst_learning_start                   3000
% 31.86/4.49  --inst_learning_factor                  2
% 31.86/4.49  --inst_start_prop_sim_after_learn       3
% 31.86/4.49  --inst_sel_renew                        solver
% 31.86/4.49  --inst_lit_activity_flag                true
% 31.86/4.49  --inst_restr_to_given                   false
% 31.86/4.49  --inst_activity_threshold               500
% 31.86/4.49  --inst_out_proof                        true
% 31.86/4.49  
% 31.86/4.49  ------ Resolution Options
% 31.86/4.49  
% 31.86/4.49  --resolution_flag                       true
% 31.86/4.49  --res_lit_sel                           adaptive
% 31.86/4.49  --res_lit_sel_side                      none
% 31.86/4.49  --res_ordering                          kbo
% 31.86/4.49  --res_to_prop_solver                    active
% 31.86/4.49  --res_prop_simpl_new                    false
% 31.86/4.49  --res_prop_simpl_given                  true
% 31.86/4.49  --res_passive_queue_type                priority_queues
% 31.86/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.86/4.49  --res_passive_queues_freq               [15;5]
% 31.86/4.49  --res_forward_subs                      full
% 31.86/4.49  --res_backward_subs                     full
% 31.86/4.49  --res_forward_subs_resolution           true
% 31.86/4.49  --res_backward_subs_resolution          true
% 31.86/4.49  --res_orphan_elimination                true
% 31.86/4.49  --res_time_limit                        2.
% 31.86/4.49  --res_out_proof                         true
% 31.86/4.49  
% 31.86/4.49  ------ Superposition Options
% 31.86/4.49  
% 31.86/4.49  --superposition_flag                    true
% 31.86/4.49  --sup_passive_queue_type                priority_queues
% 31.86/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.86/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.86/4.49  --demod_completeness_check              fast
% 31.86/4.49  --demod_use_ground                      true
% 31.86/4.49  --sup_to_prop_solver                    passive
% 31.86/4.49  --sup_prop_simpl_new                    true
% 31.86/4.49  --sup_prop_simpl_given                  true
% 31.86/4.49  --sup_fun_splitting                     true
% 31.86/4.49  --sup_smt_interval                      50000
% 31.86/4.49  
% 31.86/4.49  ------ Superposition Simplification Setup
% 31.86/4.49  
% 31.86/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.86/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.86/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.86/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.86/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.86/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.86/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.86/4.49  --sup_immed_triv                        [TrivRules]
% 31.86/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.86/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.86/4.49  --sup_immed_bw_main                     []
% 31.86/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.86/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.86/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.86/4.49  --sup_input_bw                          []
% 31.86/4.49  
% 31.86/4.49  ------ Combination Options
% 31.86/4.49  
% 31.86/4.49  --comb_res_mult                         3
% 31.86/4.49  --comb_sup_mult                         2
% 31.86/4.49  --comb_inst_mult                        10
% 31.86/4.49  
% 31.86/4.49  ------ Debug Options
% 31.86/4.49  
% 31.86/4.49  --dbg_backtrace                         false
% 31.86/4.49  --dbg_dump_prop_clauses                 false
% 31.86/4.49  --dbg_dump_prop_clauses_file            -
% 31.86/4.49  --dbg_out_stat                          false
% 31.86/4.49  ------ Parsing...
% 31.86/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.86/4.49  
% 31.86/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 31.86/4.49  
% 31.86/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.86/4.49  
% 31.86/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.86/4.49  ------ Proving...
% 31.86/4.49  ------ Problem Properties 
% 31.86/4.49  
% 31.86/4.49  
% 31.86/4.49  clauses                                 15
% 31.86/4.49  conjectures                             2
% 31.86/4.49  EPR                                     1
% 31.86/4.49  Horn                                    15
% 31.86/4.49  unary                                   12
% 31.86/4.49  binary                                  2
% 31.86/4.49  lits                                    19
% 31.86/4.49  lits eq                                 10
% 31.86/4.49  fd_pure                                 0
% 31.86/4.49  fd_pseudo                               0
% 31.86/4.49  fd_cond                                 0
% 31.86/4.49  fd_pseudo_cond                          0
% 31.86/4.49  AC symbols                              1
% 31.86/4.49  
% 31.86/4.49  ------ Schedule dynamic 5 is on 
% 31.86/4.49  
% 31.86/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.86/4.49  
% 31.86/4.49  
% 31.86/4.49  ------ 
% 31.86/4.49  Current options:
% 31.86/4.49  ------ 
% 31.86/4.49  
% 31.86/4.49  ------ Input Options
% 31.86/4.49  
% 31.86/4.49  --out_options                           all
% 31.86/4.49  --tptp_safe_out                         true
% 31.86/4.49  --problem_path                          ""
% 31.86/4.49  --include_path                          ""
% 31.86/4.49  --clausifier                            res/vclausify_rel
% 31.86/4.49  --clausifier_options                    ""
% 31.86/4.49  --stdin                                 false
% 31.86/4.49  --stats_out                             all
% 31.86/4.49  
% 31.86/4.49  ------ General Options
% 31.86/4.49  
% 31.86/4.49  --fof                                   false
% 31.86/4.49  --time_out_real                         305.
% 31.86/4.49  --time_out_virtual                      -1.
% 31.86/4.49  --symbol_type_check                     false
% 31.86/4.49  --clausify_out                          false
% 31.86/4.49  --sig_cnt_out                           false
% 31.86/4.49  --trig_cnt_out                          false
% 31.86/4.49  --trig_cnt_out_tolerance                1.
% 31.86/4.49  --trig_cnt_out_sk_spl                   false
% 31.86/4.49  --abstr_cl_out                          false
% 31.86/4.49  
% 31.86/4.49  ------ Global Options
% 31.86/4.49  
% 31.86/4.49  --schedule                              default
% 31.86/4.49  --add_important_lit                     false
% 31.86/4.49  --prop_solver_per_cl                    1000
% 31.86/4.49  --min_unsat_core                        false
% 31.86/4.49  --soft_assumptions                      false
% 31.86/4.49  --soft_lemma_size                       3
% 31.86/4.49  --prop_impl_unit_size                   0
% 31.86/4.49  --prop_impl_unit                        []
% 31.86/4.49  --share_sel_clauses                     true
% 31.86/4.49  --reset_solvers                         false
% 31.86/4.49  --bc_imp_inh                            [conj_cone]
% 31.86/4.49  --conj_cone_tolerance                   3.
% 31.86/4.49  --extra_neg_conj                        none
% 31.86/4.49  --large_theory_mode                     true
% 31.86/4.49  --prolific_symb_bound                   200
% 31.86/4.49  --lt_threshold                          2000
% 31.86/4.49  --clause_weak_htbl                      true
% 31.86/4.49  --gc_record_bc_elim                     false
% 31.86/4.49  
% 31.86/4.49  ------ Preprocessing Options
% 31.86/4.49  
% 31.86/4.49  --preprocessing_flag                    true
% 31.86/4.49  --time_out_prep_mult                    0.1
% 31.86/4.49  --splitting_mode                        input
% 31.86/4.49  --splitting_grd                         true
% 31.86/4.49  --splitting_cvd                         false
% 31.86/4.49  --splitting_cvd_svl                     false
% 31.86/4.49  --splitting_nvd                         32
% 31.86/4.49  --sub_typing                            true
% 31.86/4.49  --prep_gs_sim                           true
% 31.86/4.49  --prep_unflatten                        true
% 31.86/4.49  --prep_res_sim                          true
% 31.86/4.49  --prep_upred                            true
% 31.86/4.49  --prep_sem_filter                       exhaustive
% 31.86/4.49  --prep_sem_filter_out                   false
% 31.86/4.49  --pred_elim                             true
% 31.86/4.49  --res_sim_input                         true
% 31.86/4.49  --eq_ax_congr_red                       true
% 31.86/4.49  --pure_diseq_elim                       true
% 31.86/4.49  --brand_transform                       false
% 31.86/4.49  --non_eq_to_eq                          false
% 31.86/4.49  --prep_def_merge                        true
% 31.86/4.49  --prep_def_merge_prop_impl              false
% 31.86/4.49  --prep_def_merge_mbd                    true
% 31.86/4.49  --prep_def_merge_tr_red                 false
% 31.86/4.49  --prep_def_merge_tr_cl                  false
% 31.86/4.49  --smt_preprocessing                     true
% 31.86/4.49  --smt_ac_axioms                         fast
% 31.86/4.49  --preprocessed_out                      false
% 31.86/4.49  --preprocessed_stats                    false
% 31.86/4.49  
% 31.86/4.49  ------ Abstraction refinement Options
% 31.86/4.49  
% 31.86/4.49  --abstr_ref                             []
% 31.86/4.49  --abstr_ref_prep                        false
% 31.86/4.49  --abstr_ref_until_sat                   false
% 31.86/4.49  --abstr_ref_sig_restrict                funpre
% 31.86/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.86/4.49  --abstr_ref_under                       []
% 31.86/4.49  
% 31.86/4.49  ------ SAT Options
% 31.86/4.49  
% 31.86/4.49  --sat_mode                              false
% 31.86/4.49  --sat_fm_restart_options                ""
% 31.86/4.49  --sat_gr_def                            false
% 31.86/4.49  --sat_epr_types                         true
% 31.86/4.49  --sat_non_cyclic_types                  false
% 31.86/4.49  --sat_finite_models                     false
% 31.86/4.49  --sat_fm_lemmas                         false
% 31.86/4.49  --sat_fm_prep                           false
% 31.86/4.49  --sat_fm_uc_incr                        true
% 31.86/4.49  --sat_out_model                         small
% 31.86/4.49  --sat_out_clauses                       false
% 31.86/4.49  
% 31.86/4.49  ------ QBF Options
% 31.86/4.49  
% 31.86/4.49  --qbf_mode                              false
% 31.86/4.49  --qbf_elim_univ                         false
% 31.86/4.49  --qbf_dom_inst                          none
% 31.86/4.49  --qbf_dom_pre_inst                      false
% 31.86/4.49  --qbf_sk_in                             false
% 31.86/4.49  --qbf_pred_elim                         true
% 31.86/4.49  --qbf_split                             512
% 31.86/4.49  
% 31.86/4.49  ------ BMC1 Options
% 31.86/4.49  
% 31.86/4.49  --bmc1_incremental                      false
% 31.86/4.49  --bmc1_axioms                           reachable_all
% 31.86/4.49  --bmc1_min_bound                        0
% 31.86/4.49  --bmc1_max_bound                        -1
% 31.86/4.49  --bmc1_max_bound_default                -1
% 31.86/4.49  --bmc1_symbol_reachability              true
% 31.86/4.49  --bmc1_property_lemmas                  false
% 31.86/4.49  --bmc1_k_induction                      false
% 31.86/4.49  --bmc1_non_equiv_states                 false
% 31.86/4.49  --bmc1_deadlock                         false
% 31.86/4.49  --bmc1_ucm                              false
% 31.86/4.49  --bmc1_add_unsat_core                   none
% 31.86/4.49  --bmc1_unsat_core_children              false
% 31.86/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.86/4.49  --bmc1_out_stat                         full
% 31.86/4.49  --bmc1_ground_init                      false
% 31.86/4.49  --bmc1_pre_inst_next_state              false
% 31.86/4.49  --bmc1_pre_inst_state                   false
% 31.86/4.49  --bmc1_pre_inst_reach_state             false
% 31.86/4.49  --bmc1_out_unsat_core                   false
% 31.86/4.49  --bmc1_aig_witness_out                  false
% 31.86/4.49  --bmc1_verbose                          false
% 31.86/4.49  --bmc1_dump_clauses_tptp                false
% 31.86/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.86/4.49  --bmc1_dump_file                        -
% 31.86/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.86/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.86/4.49  --bmc1_ucm_extend_mode                  1
% 31.86/4.49  --bmc1_ucm_init_mode                    2
% 31.86/4.49  --bmc1_ucm_cone_mode                    none
% 31.86/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.86/4.49  --bmc1_ucm_relax_model                  4
% 31.86/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.86/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.86/4.49  --bmc1_ucm_layered_model                none
% 31.86/4.49  --bmc1_ucm_max_lemma_size               10
% 31.86/4.49  
% 31.86/4.49  ------ AIG Options
% 31.86/4.49  
% 31.86/4.49  --aig_mode                              false
% 31.86/4.49  
% 31.86/4.49  ------ Instantiation Options
% 31.86/4.49  
% 31.86/4.49  --instantiation_flag                    true
% 31.86/4.49  --inst_sos_flag                         true
% 31.86/4.49  --inst_sos_phase                        true
% 31.86/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.86/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.86/4.49  --inst_lit_sel_side                     none
% 31.86/4.49  --inst_solver_per_active                1400
% 31.86/4.49  --inst_solver_calls_frac                1.
% 31.86/4.49  --inst_passive_queue_type               priority_queues
% 31.86/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.86/4.49  --inst_passive_queues_freq              [25;2]
% 31.86/4.49  --inst_dismatching                      true
% 31.86/4.49  --inst_eager_unprocessed_to_passive     true
% 31.86/4.49  --inst_prop_sim_given                   true
% 31.86/4.49  --inst_prop_sim_new                     false
% 31.86/4.49  --inst_subs_new                         false
% 31.86/4.49  --inst_eq_res_simp                      false
% 31.86/4.49  --inst_subs_given                       false
% 31.86/4.49  --inst_orphan_elimination               true
% 31.86/4.49  --inst_learning_loop_flag               true
% 31.86/4.49  --inst_learning_start                   3000
% 31.86/4.49  --inst_learning_factor                  2
% 31.86/4.49  --inst_start_prop_sim_after_learn       3
% 31.86/4.49  --inst_sel_renew                        solver
% 31.86/4.49  --inst_lit_activity_flag                true
% 31.86/4.49  --inst_restr_to_given                   false
% 31.86/4.49  --inst_activity_threshold               500
% 31.86/4.49  --inst_out_proof                        true
% 31.86/4.49  
% 31.86/4.49  ------ Resolution Options
% 31.86/4.49  
% 31.86/4.49  --resolution_flag                       false
% 31.86/4.49  --res_lit_sel                           adaptive
% 31.86/4.49  --res_lit_sel_side                      none
% 31.86/4.49  --res_ordering                          kbo
% 31.86/4.49  --res_to_prop_solver                    active
% 31.86/4.49  --res_prop_simpl_new                    false
% 31.86/4.49  --res_prop_simpl_given                  true
% 31.86/4.49  --res_passive_queue_type                priority_queues
% 31.86/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.86/4.49  --res_passive_queues_freq               [15;5]
% 31.86/4.49  --res_forward_subs                      full
% 31.86/4.49  --res_backward_subs                     full
% 31.86/4.49  --res_forward_subs_resolution           true
% 31.86/4.49  --res_backward_subs_resolution          true
% 31.86/4.49  --res_orphan_elimination                true
% 31.86/4.49  --res_time_limit                        2.
% 31.86/4.49  --res_out_proof                         true
% 31.86/4.49  
% 31.86/4.49  ------ Superposition Options
% 31.86/4.49  
% 31.86/4.49  --superposition_flag                    true
% 31.86/4.49  --sup_passive_queue_type                priority_queues
% 31.86/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.86/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.86/4.49  --demod_completeness_check              fast
% 31.86/4.49  --demod_use_ground                      true
% 31.86/4.49  --sup_to_prop_solver                    passive
% 31.86/4.49  --sup_prop_simpl_new                    true
% 31.86/4.49  --sup_prop_simpl_given                  true
% 31.86/4.49  --sup_fun_splitting                     true
% 31.86/4.49  --sup_smt_interval                      50000
% 31.86/4.49  
% 31.86/4.49  ------ Superposition Simplification Setup
% 31.86/4.49  
% 31.86/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.86/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.86/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.86/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.86/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.86/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.86/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.86/4.49  --sup_immed_triv                        [TrivRules]
% 31.86/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.86/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.86/4.49  --sup_immed_bw_main                     []
% 31.86/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.86/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.86/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.86/4.49  --sup_input_bw                          []
% 31.86/4.49  
% 31.86/4.49  ------ Combination Options
% 31.86/4.49  
% 31.86/4.49  --comb_res_mult                         3
% 31.86/4.49  --comb_sup_mult                         2
% 31.86/4.49  --comb_inst_mult                        10
% 31.86/4.49  
% 31.86/4.49  ------ Debug Options
% 31.86/4.49  
% 31.86/4.49  --dbg_backtrace                         false
% 31.86/4.49  --dbg_dump_prop_clauses                 false
% 31.86/4.49  --dbg_dump_prop_clauses_file            -
% 31.86/4.49  --dbg_out_stat                          false
% 31.86/4.49  
% 31.86/4.49  
% 31.86/4.49  
% 31.86/4.49  
% 31.86/4.49  ------ Proving...
% 31.86/4.49  
% 31.86/4.49  
% 31.86/4.49  % SZS status Theorem for theBenchmark.p
% 31.86/4.49  
% 31.86/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.86/4.49  
% 31.86/4.49  fof(f5,axiom,(
% 31.86/4.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f33,plain,(
% 31.86/4.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 31.86/4.49    inference(cnf_transformation,[],[f5])).
% 31.86/4.49  
% 31.86/4.49  fof(f6,axiom,(
% 31.86/4.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f34,plain,(
% 31.86/4.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 31.86/4.49    inference(cnf_transformation,[],[f6])).
% 31.86/4.49  
% 31.86/4.49  fof(f10,axiom,(
% 31.86/4.49    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f38,plain,(
% 31.86/4.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)) )),
% 31.86/4.49    inference(cnf_transformation,[],[f10])).
% 31.86/4.49  
% 31.86/4.49  fof(f18,axiom,(
% 31.86/4.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f46,plain,(
% 31.86/4.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 31.86/4.49    inference(cnf_transformation,[],[f18])).
% 31.86/4.49  
% 31.86/4.49  fof(f52,plain,(
% 31.86/4.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 31.86/4.49    inference(definition_unfolding,[],[f46,f40])).
% 31.86/4.49  
% 31.86/4.49  fof(f11,axiom,(
% 31.86/4.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f39,plain,(
% 31.86/4.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 31.86/4.49    inference(cnf_transformation,[],[f11])).
% 31.86/4.49  
% 31.86/4.49  fof(f12,axiom,(
% 31.86/4.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f40,plain,(
% 31.86/4.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 31.86/4.49    inference(cnf_transformation,[],[f12])).
% 31.86/4.49  
% 31.86/4.49  fof(f55,plain,(
% 31.86/4.49    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 31.86/4.49    inference(definition_unfolding,[],[f39,f40])).
% 31.86/4.49  
% 31.86/4.49  fof(f58,plain,(
% 31.86/4.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))) )),
% 31.86/4.49    inference(definition_unfolding,[],[f38,f52,f40,f55])).
% 31.86/4.49  
% 31.86/4.49  fof(f13,axiom,(
% 31.86/4.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f41,plain,(
% 31.86/4.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 31.86/4.49    inference(cnf_transformation,[],[f13])).
% 31.86/4.49  
% 31.86/4.49  fof(f8,axiom,(
% 31.86/4.49    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f36,plain,(
% 31.86/4.49    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 31.86/4.49    inference(cnf_transformation,[],[f8])).
% 31.86/4.49  
% 31.86/4.49  fof(f54,plain,(
% 31.86/4.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)))) )),
% 31.86/4.49    inference(definition_unfolding,[],[f36,f52,f40,f40])).
% 31.86/4.49  
% 31.86/4.49  fof(f63,plain,(
% 31.86/4.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)))) )),
% 31.86/4.49    inference(definition_unfolding,[],[f41,f54])).
% 31.86/4.49  
% 31.86/4.49  fof(f20,conjecture,(
% 31.86/4.49    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) => r2_hidden(X0,X2))),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f21,negated_conjecture,(
% 31.86/4.49    ~! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) => r2_hidden(X0,X2))),
% 31.86/4.49    inference(negated_conjecture,[],[f20])).
% 31.86/4.49  
% 31.86/4.49  fof(f24,plain,(
% 31.86/4.49    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1))),
% 31.86/4.49    inference(ennf_transformation,[],[f21])).
% 31.86/4.49  
% 31.86/4.49  fof(f27,plain,(
% 31.86/4.49    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)) => (~r2_hidden(sK0,sK2) & k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1))),
% 31.86/4.49    introduced(choice_axiom,[])).
% 31.86/4.49  
% 31.86/4.49  fof(f28,plain,(
% 31.86/4.49    ~r2_hidden(sK0,sK2) & k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1)),
% 31.86/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27])).
% 31.86/4.49  
% 31.86/4.49  fof(f50,plain,(
% 31.86/4.49    k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK1)),
% 31.86/4.49    inference(cnf_transformation,[],[f28])).
% 31.86/4.49  
% 31.86/4.49  fof(f7,axiom,(
% 31.86/4.49    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f35,plain,(
% 31.86/4.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 31.86/4.49    inference(cnf_transformation,[],[f7])).
% 31.86/4.49  
% 31.86/4.49  fof(f53,plain,(
% 31.86/4.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 31.86/4.49    inference(definition_unfolding,[],[f35,f52])).
% 31.86/4.49  
% 31.86/4.49  fof(f68,plain,(
% 31.86/4.49    k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))) = k1_enumset1(sK0,sK0,sK1)),
% 31.86/4.49    inference(definition_unfolding,[],[f50,f53,f40,f40])).
% 31.86/4.49  
% 31.86/4.49  fof(f1,axiom,(
% 31.86/4.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f29,plain,(
% 31.86/4.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 31.86/4.49    inference(cnf_transformation,[],[f1])).
% 31.86/4.49  
% 31.86/4.49  fof(f3,axiom,(
% 31.86/4.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f23,plain,(
% 31.86/4.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 31.86/4.49    inference(rectify,[],[f3])).
% 31.86/4.49  
% 31.86/4.49  fof(f31,plain,(
% 31.86/4.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 31.86/4.49    inference(cnf_transformation,[],[f23])).
% 31.86/4.49  
% 31.86/4.49  fof(f60,plain,(
% 31.86/4.49    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k1_enumset1(X0,X0,X0))) = X0) )),
% 31.86/4.49    inference(definition_unfolding,[],[f31,f53])).
% 31.86/4.49  
% 31.86/4.49  fof(f2,axiom,(
% 31.86/4.49    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f22,plain,(
% 31.86/4.49    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 31.86/4.49    inference(rectify,[],[f2])).
% 31.86/4.49  
% 31.86/4.49  fof(f30,plain,(
% 31.86/4.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 31.86/4.49    inference(cnf_transformation,[],[f22])).
% 31.86/4.49  
% 31.86/4.49  fof(f59,plain,(
% 31.86/4.49    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) )),
% 31.86/4.49    inference(definition_unfolding,[],[f30,f52])).
% 31.86/4.49  
% 31.86/4.49  fof(f4,axiom,(
% 31.86/4.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f32,plain,(
% 31.86/4.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 31.86/4.49    inference(cnf_transformation,[],[f4])).
% 31.86/4.49  
% 31.86/4.49  fof(f61,plain,(
% 31.86/4.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1))),X0)) )),
% 31.86/4.49    inference(definition_unfolding,[],[f32,f53])).
% 31.86/4.49  
% 31.86/4.49  fof(f9,axiom,(
% 31.86/4.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f37,plain,(
% 31.86/4.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 31.86/4.49    inference(cnf_transformation,[],[f9])).
% 31.86/4.49  
% 31.86/4.49  fof(f62,plain,(
% 31.86/4.49    ( ! [X2,X0,X3,X1] : (k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X3,X3,X2),k1_enumset1(X3,X3,X2),k1_enumset1(X1,X1,X0)))) )),
% 31.86/4.49    inference(definition_unfolding,[],[f37,f54,f54])).
% 31.86/4.49  
% 31.86/4.49  fof(f19,axiom,(
% 31.86/4.49    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 31.86/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.86/4.49  
% 31.86/4.49  fof(f25,plain,(
% 31.86/4.49    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 31.86/4.49    inference(nnf_transformation,[],[f19])).
% 31.86/4.49  
% 31.86/4.49  fof(f26,plain,(
% 31.86/4.49    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 31.86/4.49    inference(flattening,[],[f25])).
% 31.86/4.49  
% 31.86/4.49  fof(f47,plain,(
% 31.86/4.49    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 31.86/4.49    inference(cnf_transformation,[],[f26])).
% 31.86/4.49  
% 31.86/4.49  fof(f67,plain,(
% 31.86/4.49    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k1_enumset1(X0,X0,X1),X2)) )),
% 31.86/4.49    inference(definition_unfolding,[],[f47,f40])).
% 31.86/4.49  
% 31.86/4.49  fof(f51,plain,(
% 31.86/4.49    ~r2_hidden(sK0,sK2)),
% 31.86/4.49    inference(cnf_transformation,[],[f28])).
% 31.86/4.49  
% 31.86/4.49  cnf(c_5,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 31.86/4.49      inference(cnf_transformation,[],[f33]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_6,plain,
% 31.86/4.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 31.86/4.49      inference(cnf_transformation,[],[f34]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_464,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_5,c_6]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_0,plain,
% 31.86/4.49      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2) ),
% 31.86/4.49      inference(cnf_transformation,[],[f58]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_8,plain,
% 31.86/4.49      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
% 31.86/4.49      inference(cnf_transformation,[],[f63]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_598,plain,
% 31.86/4.49      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_14,negated_conjecture,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))) = k1_enumset1(sK0,sK0,sK1) ),
% 31.86/4.49      inference(cnf_transformation,[],[f68]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1,plain,
% 31.86/4.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 31.86/4.49      inference(cnf_transformation,[],[f29]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_126,negated_conjecture,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)))) = k1_enumset1(sK0,sK0,sK1) ),
% 31.86/4.49      inference(theory_normalisation,[status(thm)],[c_14,c_5,c_1]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_461,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))),X0)) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_126,c_5]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1239,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2))),X0)) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0) ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_598,c_461]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1731,plain,
% 31.86/4.49      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2))),X0))) = k5_xboole_0(sK2,k1_xboole_0) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_464,c_1239]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_3,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k1_enumset1(X0,X0,X0))) = X0 ),
% 31.86/4.49      inference(cnf_transformation,[],[f60]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_128,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X0)))) = X0 ),
% 31.86/4.49      inference(theory_normalisation,[status(thm)],[c_3,c_5,c_1]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_2,plain,
% 31.86/4.49      ( k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
% 31.86/4.49      inference(cnf_transformation,[],[f59]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_245,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 31.86/4.49      inference(light_normalisation,[status(thm)],[c_128,c_2,c_6]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_460,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_405,plain,
% 31.86/4.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_245,c_1]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_468,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_460,c_405]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_252,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1368,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_6,c_252]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1408,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_1368,c_245]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1748,plain,
% 31.86/4.49      ( k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2)) = sK2 ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_1731,c_245,c_468,c_1408]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1756,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),X0)) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0) ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_1748,c_1239]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_5187,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_5,c_468]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_5672,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,X2),X0)) = X2 ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_1,c_5187]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_7147,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X2,X1),X0)) = X2 ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_1,c_5672]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_8951,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X1),X0))) = X2 ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_7147,c_5]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_9862,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0)) = k1_enumset1(sK0,sK0,sK1) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_1756,c_8951]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_666,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))),X0),X1)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_461,c_5]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_664,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0))) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_5,c_461]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_779,plain,
% 31.86/4.49      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))) = k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_xboole_0)) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_6,c_664]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_782,plain,
% 31.86/4.49      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))) = k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)) ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_779,c_245]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_841,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0),X1)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1) ),
% 31.86/4.49      inference(light_normalisation,[status(thm)],[c_666,c_666,c_782]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_4,plain,
% 31.86/4.49      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1))),X0) ),
% 31.86/4.49      inference(cnf_transformation,[],[f61]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_127,plain,
% 31.86/4.49      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k1_enumset1(X0,X0,X1)))),X0) ),
% 31.86/4.49      inference(theory_normalisation,[status(thm)],[c_4,c_5,c_1]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_244,plain,
% 31.86/4.49      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k1_enumset1(X0,X0,X1)))),X0) = iProver_top ),
% 31.86/4.49      inference(predicate_to_equality,[status(thm)],[c_127]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_3395,plain,
% 31.86/4.49      ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0)))),sK2) = iProver_top ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_841,c_244]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_781,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0)),X1)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_664,c_5]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_4346,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0))),X1) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_xboole_0),X1)) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_464,c_781]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1197,plain,
% 31.86/4.49      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0))) = k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_xboole_0)) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_464,c_664]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1207,plain,
% 31.86/4.49      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0))) = k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)) ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_1197,c_245]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_4408,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_xboole_0),X0)) = k5_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0) ),
% 31.86/4.49      inference(light_normalisation,[status(thm)],[c_4346,c_1207]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_4409,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0)) = k5_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0) ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_4408,c_245]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_61631,plain,
% 31.86/4.49      ( r1_tarski(k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0))))),sK2) = iProver_top ),
% 31.86/4.49      inference(light_normalisation,[status(thm)],[c_3395,c_4409]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_254,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1240,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2)))) = k1_enumset1(sK0,sK0,sK1) ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_598,c_126]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1575,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2))))) = k5_xboole_0(X0,k1_enumset1(sK0,sK0,sK1)) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_1240,c_252]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1758,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))) = k5_xboole_0(X0,k1_enumset1(sK0,sK0,sK1)) ),
% 31.86/4.49      inference(light_normalisation,[status(thm)],[c_1575,c_1575,c_1748]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_2391,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(sK2,X0))) = k5_xboole_0(X0,k1_enumset1(sK0,sK0,sK1)) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_254,c_1758]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_5227,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,X1) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_468,c_254]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_5284,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
% 31.86/4.49      inference(light_normalisation,[status(thm)],[c_5227,c_5]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_6132,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X3,k5_xboole_0(X1,X2)) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_5,c_5284]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_6097,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X3,X2) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_5,c_5284]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_22309,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X1,k5_xboole_0(X2,X3))) = k5_xboole_0(k5_xboole_0(X3,X1),X2) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_6132,c_6097]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_22321,plain,
% 31.86/4.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X2,X0),X1) ),
% 31.86/4.49      inference(light_normalisation,[status(thm)],[c_22309,c_6]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_22749,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(sK2,X0)),X1),sK2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k5_xboole_0(X0,k1_enumset1(sK0,sK0,sK1)))) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_2391,c_22321]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_6093,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0) = k5_xboole_0(X1,X0) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_6,c_5284]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_6926,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_5,c_6093]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_16341,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_1,c_6926]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_22807,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X3,X1)))) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_22321,c_16341]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_22820,plain,
% 31.86/4.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X2,X0),X1)) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_22321,c_254]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_253,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_16430,plain,
% 31.86/4.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X3)) = k5_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(X0,X1))) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_6926,c_253]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_22910,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))) ),
% 31.86/4.49      inference(light_normalisation,[status(thm)],[c_22820,c_16430]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_22939,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k1_xboole_0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X3,X1),X0),X2) ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_22807,c_22321,c_22910]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_22228,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X4,X0)) = k5_xboole_0(k5_xboole_0(X4,k5_xboole_0(X3,k5_xboole_0(X1,X2))),k1_xboole_0) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_6132,c_6926]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_9900,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X1,X0)) = X2 ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_7147,c_8951]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_10389,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X0)) = X2 ),
% 31.86/4.49      inference(light_normalisation,[status(thm)],[c_9900,c_5]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_22231,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(X4,X0)) = k5_xboole_0(X4,k5_xboole_0(X2,k5_xboole_0(X3,X1))) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_6132,c_10389]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_22396,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(X3,k5_xboole_0(X1,X2))) ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_22228,c_22231]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_22940,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),X3) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X3))) ),
% 31.86/4.49      inference(light_normalisation,[status(thm)],[c_22939,c_22396]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_23072,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(sK2,X0)),X1),sK2) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X1),X0) ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_22749,c_22321,c_22940]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_6141,plain,
% 31.86/4.49      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X1),X2))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X1),X2),sK2) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_841,c_5284]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_6290,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)),X0),X1),sK2) = k5_xboole_0(X1,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0)) ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_6141,c_5284]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_5722,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0)),X1) = k5_xboole_0(k5_xboole_0(X2,sK2),k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1))) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_781,c_5187]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1573,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2))),k1_enumset1(sK0,sK0,sK1))) = k1_xboole_0 ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_1240,c_464]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_2257,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2))),k1_enumset1(sK0,sK0,sK1)),k5_xboole_0(sK2,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_1573,c_253]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1766,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),k1_enumset1(sK0,sK0,sK1)) = k5_xboole_0(sK2,k1_xboole_0) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_6,c_1758]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1786,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2),k1_enumset1(sK0,sK0,sK1)) = sK2 ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_1766,c_245]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_2298,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(sK2,X0)) = X0 ),
% 31.86/4.49      inference(light_normalisation,
% 31.86/4.49                [status(thm)],
% 31.86/4.49                [c_2257,c_245,c_1748,c_1786]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_4669,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,X0),X1)) = k5_xboole_0(X0,X1) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_2298,c_5]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_5745,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(X0,sK2),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(sK2,X1),X2) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_4669,c_5187]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_5831,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0)),X1) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0)),X1) ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_5722,c_5745]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_4652,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0)),X1) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1)) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_781,c_2298]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_5832,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1)) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0)),X1) ),
% 31.86/4.49      inference(light_normalisation,[status(thm)],[c_5831,c_4652]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_6291,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1)),sK2) = k5_xboole_0(X1,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0)) ),
% 31.86/4.49      inference(light_normalisation,[status(thm)],[c_6290,c_4409,c_5832]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_9996,plain,
% 31.86/4.49      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))))),X2) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X1),X2)) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_8951,c_781]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_663,plain,
% 31.86/4.49      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)))) = k5_xboole_0(sK2,k1_xboole_0) ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_6,c_461]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_668,plain,
% 31.86/4.49      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)))) = sK2 ),
% 31.86/4.49      inference(demodulation,[status(thm)],[c_663,c_245,c_468]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_870,plain,
% 31.86/4.49      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1))) = sK2 ),
% 31.86/4.49      inference(light_normalisation,[status(thm)],[c_668,c_668,c_782]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1185,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),X0)),k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0))) = k1_xboole_0 ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_664,c_464]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_3251,plain,
% 31.86/4.49      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)))),sK2)) = k1_xboole_0 ),
% 31.86/4.49      inference(superposition,[status(thm)],[c_870,c_1185]) ).
% 31.86/4.49  
% 31.86/4.49  cnf(c_1373,plain,
% 31.86/4.49      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(X0,k5_xboole_0(sK2,k1_enumset1(sK0,sK0,sK1)))) = k5_xboole_0(X0,sK2) ),
% 31.86/4.50      inference(superposition,[status(thm)],[c_870,c_252]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_2369,plain,
% 31.86/4.50      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),sK2,sK2))),k1_enumset1(sK0,sK0,sK1)),k5_xboole_0(X0,sK2)) = k5_xboole_0(X0,k1_xboole_0) ),
% 31.86/4.50      inference(superposition,[status(thm)],[c_1573,c_254]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_2416,plain,
% 31.86/4.50      ( k5_xboole_0(sK2,k5_xboole_0(X0,sK2)) = X0 ),
% 31.86/4.50      inference(light_normalisation,
% 31.86/4.50                [status(thm)],
% 31.86/4.50                [c_2369,c_245,c_1748,c_1786]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_3289,plain,
% 31.86/4.50      ( k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2) = k1_xboole_0 ),
% 31.86/4.50      inference(demodulation,[status(thm)],[c_3251,c_781,c_1373,c_2416]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_6529,plain,
% 31.86/4.50      ( k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)) = k5_xboole_0(sK2,k1_xboole_0) ),
% 31.86/4.50      inference(superposition,[status(thm)],[c_3289,c_2416]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_6535,plain,
% 31.86/4.50      ( k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)) = sK2 ),
% 31.86/4.50      inference(demodulation,[status(thm)],[c_6529,c_245]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_8963,plain,
% 31.86/4.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),sK2)) = k5_xboole_0(sK2,X1) ),
% 31.86/4.50      inference(superposition,[status(thm)],[c_7147,c_4669]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_10300,plain,
% 31.86/4.50      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(sK2,X0)),X1) = k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1)) ),
% 31.86/4.50      inference(light_normalisation,[status(thm)],[c_9996,c_6535,c_8963]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_23073,plain,
% 31.86/4.50      ( k5_xboole_0(X0,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X1)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0),X1) ),
% 31.86/4.50      inference(light_normalisation,
% 31.86/4.50                [status(thm)],
% 31.86/4.50                [c_23072,c_6291,c_10300]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_61632,plain,
% 31.86/4.50      ( r1_tarski(k5_xboole_0(X0,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),X0)))))),sK2) = iProver_top ),
% 31.86/4.50      inference(demodulation,[status(thm)],[c_61631,c_23073]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_61660,plain,
% 31.86/4.50      ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))))),sK2) = iProver_top ),
% 31.86/4.50      inference(superposition,[status(thm)],[c_9862,c_61632]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_7,plain,
% 31.86/4.50      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X3,X3,X2),k1_enumset1(X3,X3,X2),k1_enumset1(X1,X1,X0))) ),
% 31.86/4.50      inference(cnf_transformation,[],[f62]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_657,plain,
% 31.86/4.50      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X2,X1,X0) ),
% 31.86/4.50      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_14445,plain,
% 31.86/4.50      ( k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
% 31.86/4.50      inference(superposition,[status(thm)],[c_657,c_8]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_14772,plain,
% 31.86/4.50      ( k3_tarski(k1_enumset1(sK2,sK2,k1_enumset1(sK0,sK0,sK1))) = sK2 ),
% 31.86/4.50      inference(demodulation,[status(thm)],[c_14445,c_1748]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_61721,plain,
% 31.86/4.50      ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)),sK2) = iProver_top ),
% 31.86/4.50      inference(light_normalisation,[status(thm)],[c_61660,c_14772]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_61722,plain,
% 31.86/4.50      ( r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) = iProver_top ),
% 31.86/4.50      inference(demodulation,[status(thm)],[c_61721,c_2416]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_12,plain,
% 31.86/4.50      ( r2_hidden(X0,X1) | ~ r1_tarski(k1_enumset1(X0,X0,X2),X1) ),
% 31.86/4.50      inference(cnf_transformation,[],[f67]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_241,plain,
% 31.86/4.50      ( r2_hidden(X0,X1) = iProver_top
% 31.86/4.50      | r1_tarski(k1_enumset1(X0,X0,X2),X1) != iProver_top ),
% 31.86/4.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_101194,plain,
% 31.86/4.50      ( r2_hidden(sK0,sK2) = iProver_top ),
% 31.86/4.50      inference(superposition,[status(thm)],[c_61722,c_241]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_13,negated_conjecture,
% 31.86/4.50      ( ~ r2_hidden(sK0,sK2) ),
% 31.86/4.50      inference(cnf_transformation,[],[f51]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(c_15,plain,
% 31.86/4.50      ( r2_hidden(sK0,sK2) != iProver_top ),
% 31.86/4.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.86/4.50  
% 31.86/4.50  cnf(contradiction,plain,
% 31.86/4.50      ( $false ),
% 31.86/4.50      inference(minisat,[status(thm)],[c_101194,c_15]) ).
% 31.86/4.50  
% 31.86/4.50  
% 31.86/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.86/4.50  
% 31.86/4.50  ------                               Statistics
% 31.86/4.50  
% 31.86/4.50  ------ General
% 31.86/4.50  
% 31.86/4.50  abstr_ref_over_cycles:                  0
% 31.86/4.50  abstr_ref_under_cycles:                 0
% 31.86/4.50  gc_basic_clause_elim:                   0
% 31.86/4.50  forced_gc_time:                         0
% 31.86/4.50  parsing_time:                           0.007
% 31.86/4.50  unif_index_cands_time:                  0.
% 31.86/4.50  unif_index_add_time:                    0.
% 31.86/4.50  orderings_time:                         0.
% 31.86/4.50  out_proof_time:                         0.013
% 31.86/4.50  total_time:                             3.789
% 31.86/4.50  num_of_symbols:                         43
% 31.86/4.50  num_of_terms:                           283941
% 31.86/4.50  
% 31.86/4.50  ------ Preprocessing
% 31.86/4.50  
% 31.86/4.50  num_of_splits:                          0
% 31.86/4.50  num_of_split_atoms:                     2
% 31.86/4.50  num_of_reused_defs:                     0
% 31.86/4.50  num_eq_ax_congr_red:                    18
% 31.86/4.50  num_of_sem_filtered_clauses:            1
% 31.86/4.50  num_of_subtypes:                        0
% 31.86/4.50  monotx_restored_types:                  0
% 31.86/4.50  sat_num_of_epr_types:                   0
% 31.86/4.50  sat_num_of_non_cyclic_types:            0
% 31.86/4.50  sat_guarded_non_collapsed_types:        0
% 31.86/4.50  num_pure_diseq_elim:                    0
% 31.86/4.50  simp_replaced_by:                       0
% 31.86/4.50  res_preprocessed:                       60
% 31.86/4.50  prep_upred:                             0
% 31.86/4.50  prep_unflattend:                        3
% 31.86/4.50  smt_new_axioms:                         0
% 31.86/4.50  pred_elim_cands:                        2
% 31.86/4.50  pred_elim:                              0
% 31.86/4.50  pred_elim_cl:                           0
% 31.86/4.50  pred_elim_cycles:                       1
% 31.86/4.50  merged_defs:                            0
% 31.86/4.50  merged_defs_ncl:                        0
% 31.86/4.50  bin_hyper_res:                          0
% 31.86/4.50  prep_cycles:                            3
% 31.86/4.50  pred_elim_time:                         0.001
% 31.86/4.50  splitting_time:                         0.
% 31.86/4.50  sem_filter_time:                        0.
% 31.86/4.50  monotx_time:                            0.
% 31.86/4.50  subtype_inf_time:                       0.
% 31.86/4.50  
% 31.86/4.50  ------ Problem properties
% 31.86/4.50  
% 31.86/4.50  clauses:                                15
% 31.86/4.50  conjectures:                            2
% 31.86/4.50  epr:                                    1
% 31.86/4.50  horn:                                   15
% 31.86/4.50  ground:                                 2
% 31.86/4.50  unary:                                  12
% 31.86/4.50  binary:                                 2
% 31.86/4.50  lits:                                   19
% 31.86/4.50  lits_eq:                                10
% 31.86/4.50  fd_pure:                                0
% 31.86/4.50  fd_pseudo:                              0
% 31.86/4.50  fd_cond:                                0
% 31.86/4.50  fd_pseudo_cond:                         0
% 31.86/4.50  ac_symbols:                             1
% 31.86/4.50  
% 31.86/4.50  ------ Propositional Solver
% 31.86/4.50  
% 31.86/4.50  prop_solver_calls:                      30
% 31.86/4.50  prop_fast_solver_calls:                 753
% 31.86/4.50  smt_solver_calls:                       0
% 31.86/4.50  smt_fast_solver_calls:                  0
% 31.86/4.50  prop_num_of_clauses:                    15370
% 31.86/4.50  prop_preprocess_simplified:             15469
% 31.86/4.50  prop_fo_subsumed:                       0
% 31.86/4.50  prop_solver_time:                       0.
% 31.86/4.50  smt_solver_time:                        0.
% 31.86/4.50  smt_fast_solver_time:                   0.
% 31.86/4.50  prop_fast_solver_time:                  0.
% 31.86/4.50  prop_unsat_core_time:                   0.001
% 31.86/4.50  
% 31.86/4.50  ------ QBF
% 31.86/4.50  
% 31.86/4.50  qbf_q_res:                              0
% 31.86/4.50  qbf_num_tautologies:                    0
% 31.86/4.50  qbf_prep_cycles:                        0
% 31.86/4.50  
% 31.86/4.50  ------ BMC1
% 31.86/4.50  
% 31.86/4.50  bmc1_current_bound:                     -1
% 31.86/4.50  bmc1_last_solved_bound:                 -1
% 31.86/4.50  bmc1_unsat_core_size:                   -1
% 31.86/4.50  bmc1_unsat_core_parents_size:           -1
% 31.86/4.50  bmc1_merge_next_fun:                    0
% 31.86/4.50  bmc1_unsat_core_clauses_time:           0.
% 31.86/4.50  
% 31.86/4.50  ------ Instantiation
% 31.86/4.50  
% 31.86/4.50  inst_num_of_clauses:                    2824
% 31.86/4.50  inst_num_in_passive:                    1442
% 31.86/4.50  inst_num_in_active:                     973
% 31.86/4.50  inst_num_in_unprocessed:                410
% 31.86/4.50  inst_num_of_loops:                      1060
% 31.86/4.50  inst_num_of_learning_restarts:          0
% 31.86/4.50  inst_num_moves_active_passive:          80
% 31.86/4.50  inst_lit_activity:                      0
% 31.86/4.50  inst_lit_activity_moves:                0
% 31.86/4.50  inst_num_tautologies:                   0
% 31.86/4.50  inst_num_prop_implied:                  0
% 31.86/4.50  inst_num_existing_simplified:           0
% 31.86/4.50  inst_num_eq_res_simplified:             0
% 31.86/4.50  inst_num_child_elim:                    0
% 31.86/4.50  inst_num_of_dismatching_blockings:      2848
% 31.86/4.50  inst_num_of_non_proper_insts:           4076
% 31.86/4.50  inst_num_of_duplicates:                 0
% 31.86/4.50  inst_inst_num_from_inst_to_res:         0
% 31.86/4.50  inst_dismatching_checking_time:         0.
% 31.86/4.50  
% 31.86/4.50  ------ Resolution
% 31.86/4.50  
% 31.86/4.50  res_num_of_clauses:                     0
% 31.86/4.50  res_num_in_passive:                     0
% 31.86/4.50  res_num_in_active:                      0
% 31.86/4.50  res_num_of_loops:                       63
% 31.86/4.50  res_forward_subset_subsumed:            728
% 31.86/4.50  res_backward_subset_subsumed:           4
% 31.86/4.50  res_forward_subsumed:                   0
% 31.86/4.50  res_backward_subsumed:                  0
% 31.86/4.50  res_forward_subsumption_resolution:     0
% 31.86/4.50  res_backward_subsumption_resolution:    0
% 31.86/4.50  res_clause_to_clause_subsumption:       194265
% 31.86/4.50  res_orphan_elimination:                 0
% 31.86/4.50  res_tautology_del:                      531
% 31.86/4.50  res_num_eq_res_simplified:              0
% 31.86/4.50  res_num_sel_changes:                    0
% 31.86/4.50  res_moves_from_active_to_pass:          0
% 31.86/4.50  
% 31.86/4.50  ------ Superposition
% 31.86/4.50  
% 31.86/4.50  sup_time_total:                         0.
% 31.86/4.50  sup_time_generating:                    0.
% 31.86/4.50  sup_time_sim_full:                      0.
% 31.86/4.50  sup_time_sim_immed:                     0.
% 31.86/4.50  
% 31.86/4.50  sup_num_of_clauses:                     6163
% 31.86/4.50  sup_num_in_active:                      166
% 31.86/4.50  sup_num_in_passive:                     5997
% 31.86/4.50  sup_num_of_loops:                       211
% 31.86/4.50  sup_fw_superposition:                   19335
% 31.86/4.50  sup_bw_superposition:                   14707
% 31.86/4.50  sup_immediate_simplified:               27874
% 31.86/4.50  sup_given_eliminated:                   13
% 31.86/4.50  comparisons_done:                       0
% 31.86/4.50  comparisons_avoided:                    0
% 31.86/4.50  
% 31.86/4.50  ------ Simplifications
% 31.86/4.50  
% 31.86/4.50  
% 31.86/4.50  sim_fw_subset_subsumed:                 0
% 31.86/4.50  sim_bw_subset_subsumed:                 0
% 31.86/4.50  sim_fw_subsumed:                        1244
% 31.86/4.50  sim_bw_subsumed:                        107
% 31.86/4.50  sim_fw_subsumption_res:                 0
% 31.86/4.50  sim_bw_subsumption_res:                 0
% 31.86/4.50  sim_tautology_del:                      2
% 31.86/4.50  sim_eq_tautology_del:                   6085
% 31.86/4.50  sim_eq_res_simp:                        0
% 31.86/4.50  sim_fw_demodulated:                     36565
% 31.86/4.50  sim_bw_demodulated:                     1002
% 31.86/4.50  sim_light_normalised:                   10763
% 31.86/4.50  sim_joinable_taut:                      1465
% 31.86/4.50  sim_joinable_simp:                      0
% 31.86/4.50  sim_ac_normalised:                      0
% 31.86/4.50  sim_smt_subsumption:                    0
% 31.86/4.50  
%------------------------------------------------------------------------------
