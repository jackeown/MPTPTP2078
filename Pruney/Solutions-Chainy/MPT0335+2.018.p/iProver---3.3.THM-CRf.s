%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:27 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 250 expanded)
%              Number of clauses        :   34 (  52 expanded)
%              Number of leaves         :   15 (  70 expanded)
%              Depth                    :   16
%              Number of atoms          :  135 ( 448 expanded)
%              Number of equality atoms :   93 ( 303 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f39,f39])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
      & r2_hidden(sK3,sK0)
      & k3_xboole_0(sK1,sK2) = k1_tarski(sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
    & r2_hidden(sK3,sK0)
    & k3_xboole_0(sK1,sK2) = k1_tarski(sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f25])).

fof(f46,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f61,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f46,f39,f51])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f51])).

fof(f47,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f34,f39,f39,f39])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f31,f39,f39,f39,f39])).

fof(f45,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f48,plain,(
    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f48,f39,f51])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,negated_conjecture,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_113,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1
    | sK3 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_114,plain,
    ( k2_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) = sK0 ),
    inference(unflattening,[status(thm)],[c_113])).

cnf(c_300,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_15,c_114])).

cnf(c_584,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_0,c_300])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_279,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_277,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_571,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_279,c_277])).

cnf(c_7,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3758,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_571,c_7])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3778,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3758,c_6])).

cnf(c_7423,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_584,c_3778])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_7777,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_7423,c_4])).

cnf(c_8324,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_0,c_7777])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_275,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_573,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_275,c_277])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1095,plain,
    ( k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_573,c_11])).

cnf(c_1107,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_1095,c_573])).

cnf(c_8576,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_8324,c_1095,c_1107])).

cnf(c_13,negated_conjecture,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_304,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_13,c_15])).

cnf(c_583,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_0,c_304])).

cnf(c_8965,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(demodulation,[status(thm)],[c_8576,c_583])).

cnf(c_489,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8965,c_489])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : iproveropt_run.sh %d %s
% 0.10/0.30  % Computer   : n020.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 12:42:37 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  % Running in FOF mode
% 3.89/0.89  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.89/0.89  
% 3.89/0.89  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.89/0.89  
% 3.89/0.89  ------  iProver source info
% 3.89/0.89  
% 3.89/0.89  git: date: 2020-06-30 10:37:57 +0100
% 3.89/0.89  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.89/0.89  git: non_committed_changes: false
% 3.89/0.89  git: last_make_outside_of_git: false
% 3.89/0.89  
% 3.89/0.89  ------ 
% 3.89/0.89  
% 3.89/0.89  ------ Input Options
% 3.89/0.89  
% 3.89/0.89  --out_options                           all
% 3.89/0.89  --tptp_safe_out                         true
% 3.89/0.89  --problem_path                          ""
% 3.89/0.89  --include_path                          ""
% 3.89/0.89  --clausifier                            res/vclausify_rel
% 3.89/0.89  --clausifier_options                    --mode clausify
% 3.89/0.89  --stdin                                 false
% 3.89/0.89  --stats_out                             all
% 3.89/0.89  
% 3.89/0.89  ------ General Options
% 3.89/0.89  
% 3.89/0.89  --fof                                   false
% 3.89/0.89  --time_out_real                         305.
% 3.89/0.89  --time_out_virtual                      -1.
% 3.89/0.89  --symbol_type_check                     false
% 3.89/0.89  --clausify_out                          false
% 3.89/0.89  --sig_cnt_out                           false
% 3.89/0.89  --trig_cnt_out                          false
% 3.89/0.89  --trig_cnt_out_tolerance                1.
% 3.89/0.89  --trig_cnt_out_sk_spl                   false
% 3.89/0.89  --abstr_cl_out                          false
% 3.89/0.89  
% 3.89/0.89  ------ Global Options
% 3.89/0.89  
% 3.89/0.89  --schedule                              default
% 3.89/0.89  --add_important_lit                     false
% 3.89/0.89  --prop_solver_per_cl                    1000
% 3.89/0.89  --min_unsat_core                        false
% 3.89/0.89  --soft_assumptions                      false
% 3.89/0.89  --soft_lemma_size                       3
% 3.89/0.89  --prop_impl_unit_size                   0
% 3.89/0.89  --prop_impl_unit                        []
% 3.89/0.89  --share_sel_clauses                     true
% 3.89/0.89  --reset_solvers                         false
% 3.89/0.89  --bc_imp_inh                            [conj_cone]
% 3.89/0.89  --conj_cone_tolerance                   3.
% 3.89/0.89  --extra_neg_conj                        none
% 3.89/0.89  --large_theory_mode                     true
% 3.89/0.89  --prolific_symb_bound                   200
% 3.89/0.89  --lt_threshold                          2000
% 3.89/0.89  --clause_weak_htbl                      true
% 3.89/0.89  --gc_record_bc_elim                     false
% 3.89/0.89  
% 3.89/0.89  ------ Preprocessing Options
% 3.89/0.89  
% 3.89/0.89  --preprocessing_flag                    true
% 3.89/0.89  --time_out_prep_mult                    0.1
% 3.89/0.89  --splitting_mode                        input
% 3.89/0.89  --splitting_grd                         true
% 3.89/0.89  --splitting_cvd                         false
% 3.89/0.89  --splitting_cvd_svl                     false
% 3.89/0.89  --splitting_nvd                         32
% 3.89/0.89  --sub_typing                            true
% 3.89/0.89  --prep_gs_sim                           true
% 3.89/0.89  --prep_unflatten                        true
% 3.89/0.89  --prep_res_sim                          true
% 3.89/0.89  --prep_upred                            true
% 3.89/0.89  --prep_sem_filter                       exhaustive
% 3.89/0.89  --prep_sem_filter_out                   false
% 3.89/0.89  --pred_elim                             true
% 3.89/0.89  --res_sim_input                         true
% 3.89/0.89  --eq_ax_congr_red                       true
% 3.89/0.89  --pure_diseq_elim                       true
% 3.89/0.89  --brand_transform                       false
% 3.89/0.89  --non_eq_to_eq                          false
% 3.89/0.89  --prep_def_merge                        true
% 3.89/0.89  --prep_def_merge_prop_impl              false
% 3.89/0.89  --prep_def_merge_mbd                    true
% 3.89/0.89  --prep_def_merge_tr_red                 false
% 3.89/0.89  --prep_def_merge_tr_cl                  false
% 3.89/0.89  --smt_preprocessing                     true
% 3.89/0.89  --smt_ac_axioms                         fast
% 3.89/0.89  --preprocessed_out                      false
% 3.89/0.89  --preprocessed_stats                    false
% 3.89/0.89  
% 3.89/0.89  ------ Abstraction refinement Options
% 3.89/0.89  
% 3.89/0.89  --abstr_ref                             []
% 3.89/0.89  --abstr_ref_prep                        false
% 3.89/0.89  --abstr_ref_until_sat                   false
% 3.89/0.89  --abstr_ref_sig_restrict                funpre
% 3.89/0.89  --abstr_ref_af_restrict_to_split_sk     false
% 3.89/0.89  --abstr_ref_under                       []
% 3.89/0.89  
% 3.89/0.89  ------ SAT Options
% 3.89/0.89  
% 3.89/0.89  --sat_mode                              false
% 3.89/0.89  --sat_fm_restart_options                ""
% 3.89/0.89  --sat_gr_def                            false
% 3.89/0.89  --sat_epr_types                         true
% 3.89/0.89  --sat_non_cyclic_types                  false
% 3.89/0.89  --sat_finite_models                     false
% 3.89/0.89  --sat_fm_lemmas                         false
% 3.89/0.89  --sat_fm_prep                           false
% 3.89/0.89  --sat_fm_uc_incr                        true
% 3.89/0.89  --sat_out_model                         small
% 3.89/0.89  --sat_out_clauses                       false
% 3.89/0.89  
% 3.89/0.89  ------ QBF Options
% 3.89/0.89  
% 3.89/0.89  --qbf_mode                              false
% 3.89/0.89  --qbf_elim_univ                         false
% 3.89/0.89  --qbf_dom_inst                          none
% 3.89/0.89  --qbf_dom_pre_inst                      false
% 3.89/0.89  --qbf_sk_in                             false
% 3.89/0.89  --qbf_pred_elim                         true
% 3.89/0.89  --qbf_split                             512
% 3.89/0.89  
% 3.89/0.89  ------ BMC1 Options
% 3.89/0.89  
% 3.89/0.89  --bmc1_incremental                      false
% 3.89/0.89  --bmc1_axioms                           reachable_all
% 3.89/0.89  --bmc1_min_bound                        0
% 3.89/0.89  --bmc1_max_bound                        -1
% 3.89/0.89  --bmc1_max_bound_default                -1
% 3.89/0.89  --bmc1_symbol_reachability              true
% 3.89/0.89  --bmc1_property_lemmas                  false
% 3.89/0.89  --bmc1_k_induction                      false
% 3.89/0.89  --bmc1_non_equiv_states                 false
% 3.89/0.89  --bmc1_deadlock                         false
% 3.89/0.89  --bmc1_ucm                              false
% 3.89/0.89  --bmc1_add_unsat_core                   none
% 3.89/0.89  --bmc1_unsat_core_children              false
% 3.89/0.89  --bmc1_unsat_core_extrapolate_axioms    false
% 3.89/0.89  --bmc1_out_stat                         full
% 3.89/0.89  --bmc1_ground_init                      false
% 3.89/0.89  --bmc1_pre_inst_next_state              false
% 3.89/0.89  --bmc1_pre_inst_state                   false
% 3.89/0.89  --bmc1_pre_inst_reach_state             false
% 3.89/0.89  --bmc1_out_unsat_core                   false
% 3.89/0.89  --bmc1_aig_witness_out                  false
% 3.89/0.89  --bmc1_verbose                          false
% 3.89/0.89  --bmc1_dump_clauses_tptp                false
% 3.89/0.89  --bmc1_dump_unsat_core_tptp             false
% 3.89/0.89  --bmc1_dump_file                        -
% 3.89/0.89  --bmc1_ucm_expand_uc_limit              128
% 3.89/0.89  --bmc1_ucm_n_expand_iterations          6
% 3.89/0.89  --bmc1_ucm_extend_mode                  1
% 3.89/0.89  --bmc1_ucm_init_mode                    2
% 3.89/0.89  --bmc1_ucm_cone_mode                    none
% 3.89/0.89  --bmc1_ucm_reduced_relation_type        0
% 3.89/0.89  --bmc1_ucm_relax_model                  4
% 3.89/0.89  --bmc1_ucm_full_tr_after_sat            true
% 3.89/0.89  --bmc1_ucm_expand_neg_assumptions       false
% 3.89/0.89  --bmc1_ucm_layered_model                none
% 3.89/0.89  --bmc1_ucm_max_lemma_size               10
% 3.89/0.89  
% 3.89/0.89  ------ AIG Options
% 3.89/0.89  
% 3.89/0.89  --aig_mode                              false
% 3.89/0.89  
% 3.89/0.89  ------ Instantiation Options
% 3.89/0.89  
% 3.89/0.89  --instantiation_flag                    true
% 3.89/0.89  --inst_sos_flag                         false
% 3.89/0.89  --inst_sos_phase                        true
% 3.89/0.89  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.89/0.89  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.89/0.89  --inst_lit_sel_side                     num_symb
% 3.89/0.89  --inst_solver_per_active                1400
% 3.89/0.89  --inst_solver_calls_frac                1.
% 3.89/0.89  --inst_passive_queue_type               priority_queues
% 3.89/0.89  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.89/0.89  --inst_passive_queues_freq              [25;2]
% 3.89/0.89  --inst_dismatching                      true
% 3.89/0.89  --inst_eager_unprocessed_to_passive     true
% 3.89/0.89  --inst_prop_sim_given                   true
% 3.89/0.89  --inst_prop_sim_new                     false
% 3.89/0.89  --inst_subs_new                         false
% 3.89/0.89  --inst_eq_res_simp                      false
% 3.89/0.89  --inst_subs_given                       false
% 3.89/0.89  --inst_orphan_elimination               true
% 3.89/0.89  --inst_learning_loop_flag               true
% 3.89/0.89  --inst_learning_start                   3000
% 3.89/0.89  --inst_learning_factor                  2
% 3.89/0.89  --inst_start_prop_sim_after_learn       3
% 3.89/0.89  --inst_sel_renew                        solver
% 3.89/0.89  --inst_lit_activity_flag                true
% 3.89/0.89  --inst_restr_to_given                   false
% 3.89/0.89  --inst_activity_threshold               500
% 3.89/0.89  --inst_out_proof                        true
% 3.89/0.89  
% 3.89/0.89  ------ Resolution Options
% 3.89/0.89  
% 3.89/0.89  --resolution_flag                       true
% 3.89/0.89  --res_lit_sel                           adaptive
% 3.89/0.89  --res_lit_sel_side                      none
% 3.89/0.89  --res_ordering                          kbo
% 3.89/0.89  --res_to_prop_solver                    active
% 3.89/0.89  --res_prop_simpl_new                    false
% 3.89/0.89  --res_prop_simpl_given                  true
% 3.89/0.89  --res_passive_queue_type                priority_queues
% 3.89/0.89  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.89/0.89  --res_passive_queues_freq               [15;5]
% 3.89/0.89  --res_forward_subs                      full
% 3.89/0.89  --res_backward_subs                     full
% 3.89/0.89  --res_forward_subs_resolution           true
% 3.89/0.89  --res_backward_subs_resolution          true
% 3.89/0.89  --res_orphan_elimination                true
% 3.89/0.89  --res_time_limit                        2.
% 3.89/0.89  --res_out_proof                         true
% 3.89/0.89  
% 3.89/0.89  ------ Superposition Options
% 3.89/0.89  
% 3.89/0.89  --superposition_flag                    true
% 3.89/0.89  --sup_passive_queue_type                priority_queues
% 3.89/0.89  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.89/0.89  --sup_passive_queues_freq               [8;1;4]
% 3.89/0.89  --demod_completeness_check              fast
% 3.89/0.89  --demod_use_ground                      true
% 3.89/0.89  --sup_to_prop_solver                    passive
% 3.89/0.89  --sup_prop_simpl_new                    true
% 3.89/0.89  --sup_prop_simpl_given                  true
% 3.89/0.89  --sup_fun_splitting                     false
% 3.89/0.89  --sup_smt_interval                      50000
% 3.89/0.90  
% 3.89/0.90  ------ Superposition Simplification Setup
% 3.89/0.90  
% 3.89/0.90  --sup_indices_passive                   []
% 3.89/0.90  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.90  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.90  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.90  --sup_full_triv                         [TrivRules;PropSubs]
% 3.89/0.90  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.90  --sup_full_bw                           [BwDemod]
% 3.89/0.90  --sup_immed_triv                        [TrivRules]
% 3.89/0.90  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/0.90  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.90  --sup_immed_bw_main                     []
% 3.89/0.90  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.90  --sup_input_triv                        [Unflattening;TrivRules]
% 3.89/0.90  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.90  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.90  
% 3.89/0.90  ------ Combination Options
% 3.89/0.90  
% 3.89/0.90  --comb_res_mult                         3
% 3.89/0.90  --comb_sup_mult                         2
% 3.89/0.90  --comb_inst_mult                        10
% 3.89/0.90  
% 3.89/0.90  ------ Debug Options
% 3.89/0.90  
% 3.89/0.90  --dbg_backtrace                         false
% 3.89/0.90  --dbg_dump_prop_clauses                 false
% 3.89/0.90  --dbg_dump_prop_clauses_file            -
% 3.89/0.90  --dbg_out_stat                          false
% 3.89/0.90  ------ Parsing...
% 3.89/0.90  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.89/0.90  
% 3.89/0.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.89/0.90  
% 3.89/0.90  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.89/0.90  
% 3.89/0.90  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/0.90  ------ Proving...
% 3.89/0.90  ------ Problem Properties 
% 3.89/0.90  
% 3.89/0.90  
% 3.89/0.90  clauses                                 15
% 3.89/0.90  conjectures                             3
% 3.89/0.90  EPR                                     4
% 3.89/0.90  Horn                                    15
% 3.89/0.90  unary                                   13
% 3.89/0.90  binary                                  1
% 3.89/0.90  lits                                    18
% 3.89/0.90  lits eq                                 11
% 3.89/0.90  fd_pure                                 0
% 3.89/0.90  fd_pseudo                               0
% 3.89/0.90  fd_cond                                 0
% 3.89/0.90  fd_pseudo_cond                          1
% 3.89/0.90  AC symbols                              0
% 3.89/0.90  
% 3.89/0.90  ------ Schedule dynamic 5 is on 
% 3.89/0.90  
% 3.89/0.90  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.89/0.90  
% 3.89/0.90  
% 3.89/0.90  ------ 
% 3.89/0.90  Current options:
% 3.89/0.90  ------ 
% 3.89/0.90  
% 3.89/0.90  ------ Input Options
% 3.89/0.90  
% 3.89/0.90  --out_options                           all
% 3.89/0.90  --tptp_safe_out                         true
% 3.89/0.90  --problem_path                          ""
% 3.89/0.90  --include_path                          ""
% 3.89/0.90  --clausifier                            res/vclausify_rel
% 3.89/0.90  --clausifier_options                    --mode clausify
% 3.89/0.90  --stdin                                 false
% 3.89/0.90  --stats_out                             all
% 3.89/0.90  
% 3.89/0.90  ------ General Options
% 3.89/0.90  
% 3.89/0.90  --fof                                   false
% 3.89/0.90  --time_out_real                         305.
% 3.89/0.90  --time_out_virtual                      -1.
% 3.89/0.90  --symbol_type_check                     false
% 3.89/0.90  --clausify_out                          false
% 3.89/0.90  --sig_cnt_out                           false
% 3.89/0.90  --trig_cnt_out                          false
% 3.89/0.90  --trig_cnt_out_tolerance                1.
% 3.89/0.90  --trig_cnt_out_sk_spl                   false
% 3.89/0.90  --abstr_cl_out                          false
% 3.89/0.90  
% 3.89/0.90  ------ Global Options
% 3.89/0.90  
% 3.89/0.90  --schedule                              default
% 3.89/0.90  --add_important_lit                     false
% 3.89/0.90  --prop_solver_per_cl                    1000
% 3.89/0.90  --min_unsat_core                        false
% 3.89/0.90  --soft_assumptions                      false
% 3.89/0.90  --soft_lemma_size                       3
% 3.89/0.90  --prop_impl_unit_size                   0
% 3.89/0.90  --prop_impl_unit                        []
% 3.89/0.90  --share_sel_clauses                     true
% 3.89/0.90  --reset_solvers                         false
% 3.89/0.90  --bc_imp_inh                            [conj_cone]
% 3.89/0.90  --conj_cone_tolerance                   3.
% 3.89/0.90  --extra_neg_conj                        none
% 3.89/0.90  --large_theory_mode                     true
% 3.89/0.90  --prolific_symb_bound                   200
% 3.89/0.90  --lt_threshold                          2000
% 3.89/0.90  --clause_weak_htbl                      true
% 3.89/0.90  --gc_record_bc_elim                     false
% 3.89/0.90  
% 3.89/0.90  ------ Preprocessing Options
% 3.89/0.90  
% 3.89/0.90  --preprocessing_flag                    true
% 3.89/0.90  --time_out_prep_mult                    0.1
% 3.89/0.90  --splitting_mode                        input
% 3.89/0.90  --splitting_grd                         true
% 3.89/0.90  --splitting_cvd                         false
% 3.89/0.90  --splitting_cvd_svl                     false
% 3.89/0.90  --splitting_nvd                         32
% 3.89/0.90  --sub_typing                            true
% 3.89/0.90  --prep_gs_sim                           true
% 3.89/0.90  --prep_unflatten                        true
% 3.89/0.90  --prep_res_sim                          true
% 3.89/0.90  --prep_upred                            true
% 3.89/0.90  --prep_sem_filter                       exhaustive
% 3.89/0.90  --prep_sem_filter_out                   false
% 3.89/0.90  --pred_elim                             true
% 3.89/0.90  --res_sim_input                         true
% 3.89/0.90  --eq_ax_congr_red                       true
% 3.89/0.90  --pure_diseq_elim                       true
% 3.89/0.90  --brand_transform                       false
% 3.89/0.90  --non_eq_to_eq                          false
% 3.89/0.90  --prep_def_merge                        true
% 3.89/0.90  --prep_def_merge_prop_impl              false
% 3.89/0.90  --prep_def_merge_mbd                    true
% 3.89/0.90  --prep_def_merge_tr_red                 false
% 3.89/0.90  --prep_def_merge_tr_cl                  false
% 3.89/0.90  --smt_preprocessing                     true
% 3.89/0.90  --smt_ac_axioms                         fast
% 3.89/0.90  --preprocessed_out                      false
% 3.89/0.90  --preprocessed_stats                    false
% 3.89/0.90  
% 3.89/0.90  ------ Abstraction refinement Options
% 3.89/0.90  
% 3.89/0.90  --abstr_ref                             []
% 3.89/0.90  --abstr_ref_prep                        false
% 3.89/0.90  --abstr_ref_until_sat                   false
% 3.89/0.90  --abstr_ref_sig_restrict                funpre
% 3.89/0.90  --abstr_ref_af_restrict_to_split_sk     false
% 3.89/0.90  --abstr_ref_under                       []
% 3.89/0.90  
% 3.89/0.90  ------ SAT Options
% 3.89/0.90  
% 3.89/0.90  --sat_mode                              false
% 3.89/0.90  --sat_fm_restart_options                ""
% 3.89/0.90  --sat_gr_def                            false
% 3.89/0.90  --sat_epr_types                         true
% 3.89/0.90  --sat_non_cyclic_types                  false
% 3.89/0.90  --sat_finite_models                     false
% 3.89/0.90  --sat_fm_lemmas                         false
% 3.89/0.90  --sat_fm_prep                           false
% 3.89/0.90  --sat_fm_uc_incr                        true
% 3.89/0.90  --sat_out_model                         small
% 3.89/0.90  --sat_out_clauses                       false
% 3.89/0.90  
% 3.89/0.90  ------ QBF Options
% 3.89/0.90  
% 3.89/0.90  --qbf_mode                              false
% 3.89/0.90  --qbf_elim_univ                         false
% 3.89/0.90  --qbf_dom_inst                          none
% 3.89/0.90  --qbf_dom_pre_inst                      false
% 3.89/0.90  --qbf_sk_in                             false
% 3.89/0.90  --qbf_pred_elim                         true
% 3.89/0.90  --qbf_split                             512
% 3.89/0.90  
% 3.89/0.90  ------ BMC1 Options
% 3.89/0.90  
% 3.89/0.90  --bmc1_incremental                      false
% 3.89/0.90  --bmc1_axioms                           reachable_all
% 3.89/0.90  --bmc1_min_bound                        0
% 3.89/0.90  --bmc1_max_bound                        -1
% 3.89/0.90  --bmc1_max_bound_default                -1
% 3.89/0.90  --bmc1_symbol_reachability              true
% 3.89/0.90  --bmc1_property_lemmas                  false
% 3.89/0.90  --bmc1_k_induction                      false
% 3.89/0.90  --bmc1_non_equiv_states                 false
% 3.89/0.90  --bmc1_deadlock                         false
% 3.89/0.90  --bmc1_ucm                              false
% 3.89/0.90  --bmc1_add_unsat_core                   none
% 3.89/0.90  --bmc1_unsat_core_children              false
% 3.89/0.90  --bmc1_unsat_core_extrapolate_axioms    false
% 3.89/0.90  --bmc1_out_stat                         full
% 3.89/0.90  --bmc1_ground_init                      false
% 3.89/0.90  --bmc1_pre_inst_next_state              false
% 3.89/0.90  --bmc1_pre_inst_state                   false
% 3.89/0.90  --bmc1_pre_inst_reach_state             false
% 3.89/0.90  --bmc1_out_unsat_core                   false
% 3.89/0.90  --bmc1_aig_witness_out                  false
% 3.89/0.90  --bmc1_verbose                          false
% 3.89/0.90  --bmc1_dump_clauses_tptp                false
% 3.89/0.90  --bmc1_dump_unsat_core_tptp             false
% 3.89/0.90  --bmc1_dump_file                        -
% 3.89/0.90  --bmc1_ucm_expand_uc_limit              128
% 3.89/0.90  --bmc1_ucm_n_expand_iterations          6
% 3.89/0.90  --bmc1_ucm_extend_mode                  1
% 3.89/0.90  --bmc1_ucm_init_mode                    2
% 3.89/0.90  --bmc1_ucm_cone_mode                    none
% 3.89/0.90  --bmc1_ucm_reduced_relation_type        0
% 3.89/0.90  --bmc1_ucm_relax_model                  4
% 3.89/0.90  --bmc1_ucm_full_tr_after_sat            true
% 3.89/0.90  --bmc1_ucm_expand_neg_assumptions       false
% 3.89/0.90  --bmc1_ucm_layered_model                none
% 3.89/0.90  --bmc1_ucm_max_lemma_size               10
% 3.89/0.90  
% 3.89/0.90  ------ AIG Options
% 3.89/0.90  
% 3.89/0.90  --aig_mode                              false
% 3.89/0.90  
% 3.89/0.90  ------ Instantiation Options
% 3.89/0.90  
% 3.89/0.90  --instantiation_flag                    true
% 3.89/0.90  --inst_sos_flag                         false
% 3.89/0.90  --inst_sos_phase                        true
% 3.89/0.90  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.89/0.90  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.89/0.90  --inst_lit_sel_side                     none
% 3.89/0.90  --inst_solver_per_active                1400
% 3.89/0.90  --inst_solver_calls_frac                1.
% 3.89/0.90  --inst_passive_queue_type               priority_queues
% 3.89/0.90  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.89/0.90  --inst_passive_queues_freq              [25;2]
% 3.89/0.90  --inst_dismatching                      true
% 3.89/0.90  --inst_eager_unprocessed_to_passive     true
% 3.89/0.90  --inst_prop_sim_given                   true
% 3.89/0.90  --inst_prop_sim_new                     false
% 3.89/0.90  --inst_subs_new                         false
% 3.89/0.90  --inst_eq_res_simp                      false
% 3.89/0.90  --inst_subs_given                       false
% 3.89/0.90  --inst_orphan_elimination               true
% 3.89/0.90  --inst_learning_loop_flag               true
% 3.89/0.90  --inst_learning_start                   3000
% 3.89/0.90  --inst_learning_factor                  2
% 3.89/0.90  --inst_start_prop_sim_after_learn       3
% 3.89/0.90  --inst_sel_renew                        solver
% 3.89/0.90  --inst_lit_activity_flag                true
% 3.89/0.90  --inst_restr_to_given                   false
% 3.89/0.90  --inst_activity_threshold               500
% 3.89/0.90  --inst_out_proof                        true
% 3.89/0.90  
% 3.89/0.90  ------ Resolution Options
% 3.89/0.90  
% 3.89/0.90  --resolution_flag                       false
% 3.89/0.90  --res_lit_sel                           adaptive
% 3.89/0.90  --res_lit_sel_side                      none
% 3.89/0.90  --res_ordering                          kbo
% 3.89/0.90  --res_to_prop_solver                    active
% 3.89/0.90  --res_prop_simpl_new                    false
% 3.89/0.90  --res_prop_simpl_given                  true
% 3.89/0.90  --res_passive_queue_type                priority_queues
% 3.89/0.90  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.89/0.90  --res_passive_queues_freq               [15;5]
% 3.89/0.90  --res_forward_subs                      full
% 3.89/0.90  --res_backward_subs                     full
% 3.89/0.90  --res_forward_subs_resolution           true
% 3.89/0.90  --res_backward_subs_resolution          true
% 3.89/0.90  --res_orphan_elimination                true
% 3.89/0.90  --res_time_limit                        2.
% 3.89/0.90  --res_out_proof                         true
% 3.89/0.90  
% 3.89/0.90  ------ Superposition Options
% 3.89/0.90  
% 3.89/0.90  --superposition_flag                    true
% 3.89/0.90  --sup_passive_queue_type                priority_queues
% 3.89/0.90  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.89/0.90  --sup_passive_queues_freq               [8;1;4]
% 3.89/0.90  --demod_completeness_check              fast
% 3.89/0.90  --demod_use_ground                      true
% 3.89/0.90  --sup_to_prop_solver                    passive
% 3.89/0.90  --sup_prop_simpl_new                    true
% 3.89/0.90  --sup_prop_simpl_given                  true
% 3.89/0.90  --sup_fun_splitting                     false
% 3.89/0.90  --sup_smt_interval                      50000
% 3.89/0.90  
% 3.89/0.90  ------ Superposition Simplification Setup
% 3.89/0.90  
% 3.89/0.90  --sup_indices_passive                   []
% 3.89/0.90  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.90  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.90  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.89/0.90  --sup_full_triv                         [TrivRules;PropSubs]
% 3.89/0.90  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.90  --sup_full_bw                           [BwDemod]
% 3.89/0.90  --sup_immed_triv                        [TrivRules]
% 3.89/0.90  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.89/0.90  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.90  --sup_immed_bw_main                     []
% 3.89/0.90  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.90  --sup_input_triv                        [Unflattening;TrivRules]
% 3.89/0.90  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.89/0.90  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.89/0.90  
% 3.89/0.90  ------ Combination Options
% 3.89/0.90  
% 3.89/0.90  --comb_res_mult                         3
% 3.89/0.90  --comb_sup_mult                         2
% 3.89/0.90  --comb_inst_mult                        10
% 3.89/0.90  
% 3.89/0.90  ------ Debug Options
% 3.89/0.90  
% 3.89/0.90  --dbg_backtrace                         false
% 3.89/0.90  --dbg_dump_prop_clauses                 false
% 3.89/0.90  --dbg_dump_prop_clauses_file            -
% 3.89/0.90  --dbg_out_stat                          false
% 3.89/0.90  
% 3.89/0.90  
% 3.89/0.90  
% 3.89/0.90  
% 3.89/0.90  ------ Proving...
% 3.89/0.90  
% 3.89/0.90  
% 3.89/0.90  % SZS status Theorem for theBenchmark.p
% 3.89/0.90  
% 3.89/0.90  % SZS output start CNFRefutation for theBenchmark.p
% 3.89/0.90  
% 3.89/0.90  fof(f1,axiom,(
% 3.89/0.90    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.89/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.90  
% 3.89/0.90  fof(f27,plain,(
% 3.89/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.89/0.90    inference(cnf_transformation,[],[f1])).
% 3.89/0.90  
% 3.89/0.90  fof(f11,axiom,(
% 3.89/0.90    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.89/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.90  
% 3.89/0.90  fof(f39,plain,(
% 3.89/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.89/0.90    inference(cnf_transformation,[],[f11])).
% 3.89/0.90  
% 3.89/0.90  fof(f52,plain,(
% 3.89/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.89/0.90    inference(definition_unfolding,[],[f27,f39,f39])).
% 3.89/0.90  
% 3.89/0.90  fof(f17,conjecture,(
% 3.89/0.90    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 3.89/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.90  
% 3.89/0.90  fof(f18,negated_conjecture,(
% 3.89/0.90    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 3.89/0.90    inference(negated_conjecture,[],[f17])).
% 3.89/0.90  
% 3.89/0.90  fof(f21,plain,(
% 3.89/0.90    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 3.89/0.90    inference(ennf_transformation,[],[f18])).
% 3.89/0.90  
% 3.89/0.90  fof(f22,plain,(
% 3.89/0.90    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 3.89/0.90    inference(flattening,[],[f21])).
% 3.89/0.90  
% 3.89/0.90  fof(f25,plain,(
% 3.89/0.90    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k3_xboole_0(sK1,sK2) = k1_tarski(sK3) & r1_tarski(sK0,sK1))),
% 3.89/0.90    introduced(choice_axiom,[])).
% 3.89/0.90  
% 3.89/0.90  fof(f26,plain,(
% 3.89/0.90    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k3_xboole_0(sK1,sK2) = k1_tarski(sK3) & r1_tarski(sK0,sK1)),
% 3.89/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f25])).
% 3.89/0.90  
% 3.89/0.90  fof(f46,plain,(
% 3.89/0.90    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 3.89/0.90    inference(cnf_transformation,[],[f26])).
% 3.89/0.90  
% 3.89/0.90  fof(f12,axiom,(
% 3.89/0.90    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.89/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.90  
% 3.89/0.90  fof(f40,plain,(
% 3.89/0.90    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.89/0.90    inference(cnf_transformation,[],[f12])).
% 3.89/0.90  
% 3.89/0.90  fof(f13,axiom,(
% 3.89/0.90    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.89/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.90  
% 3.89/0.90  fof(f41,plain,(
% 3.89/0.90    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.89/0.90    inference(cnf_transformation,[],[f13])).
% 3.89/0.90  
% 3.89/0.90  fof(f14,axiom,(
% 3.89/0.90    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.89/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.90  
% 3.89/0.90  fof(f42,plain,(
% 3.89/0.90    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.89/0.90    inference(cnf_transformation,[],[f14])).
% 3.89/0.90  
% 3.89/0.90  fof(f15,axiom,(
% 3.89/0.90    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.89/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.90  
% 3.89/0.90  fof(f43,plain,(
% 3.89/0.90    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.89/0.90    inference(cnf_transformation,[],[f15])).
% 3.89/0.90  
% 3.89/0.90  fof(f49,plain,(
% 3.89/0.90    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.89/0.90    inference(definition_unfolding,[],[f42,f43])).
% 3.89/0.90  
% 3.89/0.90  fof(f50,plain,(
% 3.89/0.90    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.89/0.90    inference(definition_unfolding,[],[f41,f49])).
% 3.89/0.90  
% 3.89/0.90  fof(f51,plain,(
% 3.89/0.90    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.89/0.90    inference(definition_unfolding,[],[f40,f50])).
% 3.89/0.90  
% 3.89/0.90  fof(f61,plain,(
% 3.89/0.90    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 3.89/0.90    inference(definition_unfolding,[],[f46,f39,f51])).
% 3.89/0.90  
% 3.89/0.90  fof(f16,axiom,(
% 3.89/0.90    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.89/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.90  
% 3.89/0.90  fof(f20,plain,(
% 3.89/0.90    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 3.89/0.90    inference(ennf_transformation,[],[f16])).
% 3.89/0.90  
% 3.89/0.90  fof(f44,plain,(
% 3.89/0.90    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 3.89/0.90    inference(cnf_transformation,[],[f20])).
% 3.89/0.90  
% 3.89/0.90  fof(f59,plain,(
% 3.89/0.90    ( ! [X0,X1] : (k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 3.89/0.90    inference(definition_unfolding,[],[f44,f51])).
% 3.89/0.90  
% 3.89/0.90  fof(f47,plain,(
% 3.89/0.90    r2_hidden(sK3,sK0)),
% 3.89/0.90    inference(cnf_transformation,[],[f26])).
% 3.89/0.90  
% 3.89/0.90  fof(f2,axiom,(
% 3.89/0.90    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.89/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.90  
% 3.89/0.90  fof(f23,plain,(
% 3.89/0.90    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.89/0.90    inference(nnf_transformation,[],[f2])).
% 3.89/0.90  
% 3.89/0.90  fof(f24,plain,(
% 3.89/0.90    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.89/0.90    inference(flattening,[],[f23])).
% 3.89/0.90  
% 3.89/0.90  fof(f28,plain,(
% 3.89/0.90    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.89/0.90    inference(cnf_transformation,[],[f24])).
% 3.89/0.90  
% 3.89/0.90  fof(f63,plain,(
% 3.89/0.90    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.89/0.90    inference(equality_resolution,[],[f28])).
% 3.89/0.90  
% 3.89/0.90  fof(f7,axiom,(
% 3.89/0.90    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.89/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.90  
% 3.89/0.90  fof(f19,plain,(
% 3.89/0.90    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.89/0.90    inference(ennf_transformation,[],[f7])).
% 3.89/0.90  
% 3.89/0.90  fof(f35,plain,(
% 3.89/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.89/0.90    inference(cnf_transformation,[],[f19])).
% 3.89/0.90  
% 3.89/0.90  fof(f57,plain,(
% 3.89/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.89/0.90    inference(definition_unfolding,[],[f35,f39])).
% 3.89/0.90  
% 3.89/0.90  fof(f6,axiom,(
% 3.89/0.90    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 3.89/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.90  
% 3.89/0.90  fof(f34,plain,(
% 3.89/0.90    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 3.89/0.90    inference(cnf_transformation,[],[f6])).
% 3.89/0.90  
% 3.89/0.90  fof(f56,plain,(
% 3.89/0.90    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 3.89/0.90    inference(definition_unfolding,[],[f34,f39,f39,f39])).
% 3.89/0.90  
% 3.89/0.90  fof(f5,axiom,(
% 3.89/0.90    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.89/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.90  
% 3.89/0.90  fof(f33,plain,(
% 3.89/0.90    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.89/0.90    inference(cnf_transformation,[],[f5])).
% 3.89/0.90  
% 3.89/0.90  fof(f55,plain,(
% 3.89/0.90    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 3.89/0.90    inference(definition_unfolding,[],[f33,f39])).
% 3.89/0.90  
% 3.89/0.90  fof(f3,axiom,(
% 3.89/0.90    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.89/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.90  
% 3.89/0.90  fof(f31,plain,(
% 3.89/0.90    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.89/0.90    inference(cnf_transformation,[],[f3])).
% 3.89/0.90  
% 3.89/0.90  fof(f53,plain,(
% 3.89/0.90    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 3.89/0.90    inference(definition_unfolding,[],[f31,f39,f39,f39,f39])).
% 3.89/0.90  
% 3.89/0.90  fof(f45,plain,(
% 3.89/0.90    r1_tarski(sK0,sK1)),
% 3.89/0.90    inference(cnf_transformation,[],[f26])).
% 3.89/0.90  
% 3.89/0.90  fof(f10,axiom,(
% 3.89/0.90    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.89/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.89/0.90  
% 3.89/0.90  fof(f38,plain,(
% 3.89/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.89/0.90    inference(cnf_transformation,[],[f10])).
% 3.89/0.90  
% 3.89/0.90  fof(f58,plain,(
% 3.89/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.89/0.90    inference(definition_unfolding,[],[f38,f39])).
% 3.89/0.90  
% 3.89/0.90  fof(f48,plain,(
% 3.89/0.90    k3_xboole_0(sK0,sK2) != k1_tarski(sK3)),
% 3.89/0.90    inference(cnf_transformation,[],[f26])).
% 3.89/0.90  
% 3.89/0.90  fof(f60,plain,(
% 3.89/0.90    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3)),
% 3.89/0.90    inference(definition_unfolding,[],[f48,f39,f51])).
% 3.89/0.90  
% 3.89/0.90  cnf(c_0,plain,
% 3.89/0.90      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.89/0.90      inference(cnf_transformation,[],[f52]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_15,negated_conjecture,
% 3.89/0.90      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 3.89/0.90      inference(cnf_transformation,[],[f61]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_12,plain,
% 3.89/0.90      ( ~ r2_hidden(X0,X1)
% 3.89/0.90      | k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1 ),
% 3.89/0.90      inference(cnf_transformation,[],[f59]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_14,negated_conjecture,
% 3.89/0.90      ( r2_hidden(sK3,sK0) ),
% 3.89/0.90      inference(cnf_transformation,[],[f47]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_113,plain,
% 3.89/0.90      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = X1
% 3.89/0.90      | sK3 != X0
% 3.89/0.90      | sK0 != X1 ),
% 3.89/0.90      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_114,plain,
% 3.89/0.90      ( k2_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK0) = sK0 ),
% 3.89/0.90      inference(unflattening,[status(thm)],[c_113]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_300,plain,
% 3.89/0.90      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0) = sK0 ),
% 3.89/0.90      inference(demodulation,[status(thm)],[c_15,c_114]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_584,plain,
% 3.89/0.90      ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0) = sK0 ),
% 3.89/0.90      inference(demodulation,[status(thm)],[c_0,c_300]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_3,plain,
% 3.89/0.90      ( r1_tarski(X0,X0) ),
% 3.89/0.90      inference(cnf_transformation,[],[f63]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_279,plain,
% 3.89/0.90      ( r1_tarski(X0,X0) = iProver_top ),
% 3.89/0.90      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_8,plain,
% 3.89/0.90      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.89/0.90      inference(cnf_transformation,[],[f57]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_277,plain,
% 3.89/0.90      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.89/0.90      | r1_tarski(X0,X1) != iProver_top ),
% 3.89/0.90      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_571,plain,
% 3.89/0.90      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 3.89/0.90      inference(superposition,[status(thm)],[c_279,c_277]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_7,plain,
% 3.89/0.90      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 3.89/0.90      inference(cnf_transformation,[],[f56]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_3758,plain,
% 3.89/0.90      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
% 3.89/0.90      inference(superposition,[status(thm)],[c_571,c_7]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_6,plain,
% 3.89/0.90      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.89/0.90      inference(cnf_transformation,[],[f55]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_3778,plain,
% 3.89/0.90      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
% 3.89/0.90      inference(light_normalisation,[status(thm)],[c_3758,c_6]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_7423,plain,
% 3.89/0.90      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)),sK0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 3.89/0.90      inference(superposition,[status(thm)],[c_584,c_3778]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_4,plain,
% 3.89/0.90      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 3.89/0.90      inference(cnf_transformation,[],[f53]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_7777,plain,
% 3.89/0.90      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 3.89/0.90      inference(superposition,[status(thm)],[c_7423,c_4]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_8324,plain,
% 3.89/0.90      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
% 3.89/0.90      inference(superposition,[status(thm)],[c_0,c_7777]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_16,negated_conjecture,
% 3.89/0.90      ( r1_tarski(sK0,sK1) ),
% 3.89/0.90      inference(cnf_transformation,[],[f45]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_275,plain,
% 3.89/0.90      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.89/0.90      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_573,plain,
% 3.89/0.90      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = sK0 ),
% 3.89/0.90      inference(superposition,[status(thm)],[c_275,c_277]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_11,plain,
% 3.89/0.90      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.89/0.90      inference(cnf_transformation,[],[f58]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_1095,plain,
% 3.89/0.90      ( k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK1) ),
% 3.89/0.90      inference(superposition,[status(thm)],[c_573,c_11]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_1107,plain,
% 3.89/0.90      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) = sK0 ),
% 3.89/0.90      inference(demodulation,[status(thm)],[c_1095,c_573]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_8576,plain,
% 3.89/0.90      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
% 3.89/0.90      inference(light_normalisation,[status(thm)],[c_8324,c_1095,c_1107]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_13,negated_conjecture,
% 3.89/0.90      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k3_enumset1(sK3,sK3,sK3,sK3,sK3) ),
% 3.89/0.90      inference(cnf_transformation,[],[f60]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_304,plain,
% 3.89/0.90      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 3.89/0.90      inference(light_normalisation,[status(thm)],[c_13,c_15]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_583,plain,
% 3.89/0.90      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 3.89/0.90      inference(demodulation,[status(thm)],[c_0,c_304]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_8965,plain,
% 3.89/0.90      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 3.89/0.90      inference(demodulation,[status(thm)],[c_8576,c_583]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(c_489,plain,
% 3.89/0.90      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
% 3.89/0.90      inference(instantiation,[status(thm)],[c_0]) ).
% 3.89/0.90  
% 3.89/0.90  cnf(contradiction,plain,
% 3.89/0.90      ( $false ),
% 3.89/0.90      inference(minisat,[status(thm)],[c_8965,c_489]) ).
% 3.89/0.90  
% 3.89/0.90  
% 3.89/0.90  % SZS output end CNFRefutation for theBenchmark.p
% 3.89/0.90  
% 3.89/0.90  ------                               Statistics
% 3.89/0.90  
% 3.89/0.90  ------ General
% 3.89/0.90  
% 3.89/0.90  abstr_ref_over_cycles:                  0
% 3.89/0.90  abstr_ref_under_cycles:                 0
% 3.89/0.90  gc_basic_clause_elim:                   0
% 3.89/0.90  forced_gc_time:                         0
% 3.89/0.90  parsing_time:                           0.007
% 3.89/0.90  unif_index_cands_time:                  0.
% 3.89/0.90  unif_index_add_time:                    0.
% 3.89/0.90  orderings_time:                         0.
% 3.89/0.90  out_proof_time:                         0.008
% 3.89/0.90  total_time:                             0.379
% 3.89/0.90  num_of_symbols:                         41
% 3.89/0.90  num_of_terms:                           11228
% 3.89/0.90  
% 3.89/0.90  ------ Preprocessing
% 3.89/0.90  
% 3.89/0.90  num_of_splits:                          0
% 3.89/0.90  num_of_split_atoms:                     0
% 3.89/0.90  num_of_reused_defs:                     0
% 3.89/0.90  num_eq_ax_congr_red:                    0
% 3.89/0.90  num_of_sem_filtered_clauses:            1
% 3.89/0.90  num_of_subtypes:                        0
% 3.89/0.90  monotx_restored_types:                  0
% 3.89/0.90  sat_num_of_epr_types:                   0
% 3.89/0.90  sat_num_of_non_cyclic_types:            0
% 3.89/0.90  sat_guarded_non_collapsed_types:        0
% 3.89/0.90  num_pure_diseq_elim:                    0
% 3.89/0.90  simp_replaced_by:                       0
% 3.89/0.90  res_preprocessed:                       74
% 3.89/0.90  prep_upred:                             0
% 3.89/0.90  prep_unflattend:                        2
% 3.89/0.90  smt_new_axioms:                         0
% 3.89/0.90  pred_elim_cands:                        1
% 3.89/0.90  pred_elim:                              1
% 3.89/0.90  pred_elim_cl:                           1
% 3.89/0.90  pred_elim_cycles:                       3
% 3.89/0.90  merged_defs:                            0
% 3.89/0.90  merged_defs_ncl:                        0
% 3.89/0.90  bin_hyper_res:                          0
% 3.89/0.90  prep_cycles:                            4
% 3.89/0.90  pred_elim_time:                         0.
% 3.89/0.90  splitting_time:                         0.
% 3.89/0.90  sem_filter_time:                        0.
% 3.89/0.90  monotx_time:                            0.
% 3.89/0.90  subtype_inf_time:                       0.
% 3.89/0.90  
% 3.89/0.90  ------ Problem properties
% 3.89/0.90  
% 3.89/0.90  clauses:                                15
% 3.89/0.90  conjectures:                            3
% 3.89/0.90  epr:                                    4
% 3.89/0.90  horn:                                   15
% 3.89/0.90  ground:                                 4
% 3.89/0.90  unary:                                  13
% 3.89/0.90  binary:                                 1
% 3.89/0.90  lits:                                   18
% 3.89/0.90  lits_eq:                                11
% 3.89/0.90  fd_pure:                                0
% 3.89/0.90  fd_pseudo:                              0
% 3.89/0.90  fd_cond:                                0
% 3.89/0.90  fd_pseudo_cond:                         1
% 3.89/0.90  ac_symbols:                             0
% 3.89/0.90  
% 3.89/0.90  ------ Propositional Solver
% 3.89/0.90  
% 3.89/0.90  prop_solver_calls:                      31
% 3.89/0.90  prop_fast_solver_calls:                 328
% 3.89/0.90  smt_solver_calls:                       0
% 3.89/0.90  smt_fast_solver_calls:                  0
% 3.89/0.90  prop_num_of_clauses:                    3608
% 3.89/0.90  prop_preprocess_simplified:             6016
% 3.89/0.90  prop_fo_subsumed:                       0
% 3.89/0.90  prop_solver_time:                       0.
% 3.89/0.90  smt_solver_time:                        0.
% 3.89/0.90  smt_fast_solver_time:                   0.
% 3.89/0.90  prop_fast_solver_time:                  0.
% 3.89/0.90  prop_unsat_core_time:                   0.
% 3.89/0.90  
% 3.89/0.90  ------ QBF
% 3.89/0.90  
% 3.89/0.90  qbf_q_res:                              0
% 3.89/0.90  qbf_num_tautologies:                    0
% 3.89/0.90  qbf_prep_cycles:                        0
% 3.89/0.90  
% 3.89/0.90  ------ BMC1
% 3.89/0.90  
% 3.89/0.90  bmc1_current_bound:                     -1
% 3.89/0.90  bmc1_last_solved_bound:                 -1
% 3.89/0.90  bmc1_unsat_core_size:                   -1
% 3.89/0.90  bmc1_unsat_core_parents_size:           -1
% 3.89/0.90  bmc1_merge_next_fun:                    0
% 3.89/0.90  bmc1_unsat_core_clauses_time:           0.
% 3.89/0.90  
% 3.89/0.90  ------ Instantiation
% 3.89/0.90  
% 3.89/0.90  inst_num_of_clauses:                    1073
% 3.89/0.90  inst_num_in_passive:                    355
% 3.89/0.90  inst_num_in_active:                     416
% 3.89/0.90  inst_num_in_unprocessed:                302
% 3.89/0.90  inst_num_of_loops:                      420
% 3.89/0.90  inst_num_of_learning_restarts:          0
% 3.89/0.90  inst_num_moves_active_passive:          0
% 3.89/0.90  inst_lit_activity:                      0
% 3.89/0.90  inst_lit_activity_moves:                0
% 3.89/0.90  inst_num_tautologies:                   0
% 3.89/0.90  inst_num_prop_implied:                  0
% 3.89/0.90  inst_num_existing_simplified:           0
% 3.89/0.90  inst_num_eq_res_simplified:             0
% 3.89/0.90  inst_num_child_elim:                    0
% 3.89/0.90  inst_num_of_dismatching_blockings:      229
% 3.89/0.90  inst_num_of_non_proper_insts:           920
% 3.89/0.90  inst_num_of_duplicates:                 0
% 3.89/0.90  inst_inst_num_from_inst_to_res:         0
% 3.89/0.90  inst_dismatching_checking_time:         0.
% 3.89/0.90  
% 3.89/0.90  ------ Resolution
% 3.89/0.90  
% 3.89/0.90  res_num_of_clauses:                     0
% 3.89/0.90  res_num_in_passive:                     0
% 3.89/0.90  res_num_in_active:                      0
% 3.89/0.90  res_num_of_loops:                       78
% 3.89/0.90  res_forward_subset_subsumed:            126
% 3.89/0.90  res_backward_subset_subsumed:           0
% 3.89/0.90  res_forward_subsumed:                   0
% 3.89/0.90  res_backward_subsumed:                  0
% 3.89/0.90  res_forward_subsumption_resolution:     0
% 3.89/0.90  res_backward_subsumption_resolution:    0
% 3.89/0.90  res_clause_to_clause_subsumption:       3380
% 3.89/0.90  res_orphan_elimination:                 0
% 3.89/0.90  res_tautology_del:                      40
% 3.89/0.90  res_num_eq_res_simplified:              0
% 3.89/0.90  res_num_sel_changes:                    0
% 3.89/0.90  res_moves_from_active_to_pass:          0
% 3.89/0.90  
% 3.89/0.90  ------ Superposition
% 3.89/0.90  
% 3.89/0.90  sup_time_total:                         0.
% 3.89/0.90  sup_time_generating:                    0.
% 3.89/0.90  sup_time_sim_full:                      0.
% 3.89/0.90  sup_time_sim_immed:                     0.
% 3.89/0.90  
% 3.89/0.90  sup_num_of_clauses:                     442
% 3.89/0.90  sup_num_in_active:                      46
% 3.89/0.90  sup_num_in_passive:                     396
% 3.89/0.90  sup_num_of_loops:                       82
% 3.89/0.90  sup_fw_superposition:                   366
% 3.89/0.90  sup_bw_superposition:                   741
% 3.89/0.90  sup_immediate_simplified:               492
% 3.89/0.90  sup_given_eliminated:                   22
% 3.89/0.90  comparisons_done:                       0
% 3.89/0.90  comparisons_avoided:                    0
% 3.89/0.90  
% 3.89/0.90  ------ Simplifications
% 3.89/0.90  
% 3.89/0.90  
% 3.89/0.90  sim_fw_subset_subsumed:                 0
% 3.89/0.90  sim_bw_subset_subsumed:                 0
% 3.89/0.90  sim_fw_subsumed:                        75
% 3.89/0.90  sim_bw_subsumed:                        44
% 3.89/0.90  sim_fw_subsumption_res:                 0
% 3.89/0.90  sim_bw_subsumption_res:                 0
% 3.89/0.90  sim_tautology_del:                      0
% 3.89/0.90  sim_eq_tautology_del:                   93
% 3.89/0.90  sim_eq_res_simp:                        0
% 3.89/0.90  sim_fw_demodulated:                     243
% 3.89/0.90  sim_bw_demodulated:                     139
% 3.89/0.90  sim_light_normalised:                   222
% 3.89/0.90  sim_joinable_taut:                      0
% 3.89/0.90  sim_joinable_simp:                      0
% 3.89/0.90  sim_ac_normalised:                      0
% 3.89/0.90  sim_smt_subsumption:                    0
% 3.89/0.90  
%------------------------------------------------------------------------------
