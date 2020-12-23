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
% DateTime   : Thu Dec  3 11:23:49 EST 2020

% Result     : Theorem 47.61s
% Output     : CNFRefutation 47.61s
% Verified   : 
% Statistics : Number of formulae       :  734 (457109 expanded)
%              Number of clauses        :  679 (182713 expanded)
%              Number of leaves         :   22 (114881 expanded)
%              Depth                    :   50
%              Number of atoms          :  796 (695106 expanded)
%              Number of equality atoms :  734 (514167 expanded)
%              Maximal formula depth    :    9 (   1 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f24])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK3 != sK4
      & r1_xboole_0(sK5,sK3)
      & r1_xboole_0(sK4,sK2)
      & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( sK3 != sK4
    & r1_xboole_0(sK5,sK3)
    & r1_xboole_0(sK4,sK2)
    & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f30])).

fof(f49,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f44,f44])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f28])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
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
    inference(rectify,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f26])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f50,plain,(
    r1_xboole_0(sK4,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    r1_xboole_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_19,negated_conjecture,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_12,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_183,negated_conjecture,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK4,sK5) ),
    inference(theory_normalisation,[status(thm)],[c_19,c_12,c_0])).

cnf(c_14,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_622,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_183,c_14])).

cnf(c_626,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_622,c_183])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_15,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_107,plain,
    ( X0 != X1
    | k4_xboole_0(X1,X2) = k1_xboole_0
    | k2_xboole_0(X0,X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_108,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_107])).

cnf(c_547,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_108])).

cnf(c_1611,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_547])).

cnf(c_4103,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1611])).

cnf(c_11,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_9087,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_4103,c_11])).

cnf(c_551,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_108,c_8])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_555,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_551,c_6])).

cnf(c_1877,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_555])).

cnf(c_277,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_12,c_0])).

cnf(c_5480,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X0)),X2)) = k2_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_1877,c_277])).

cnf(c_3794,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_277,c_555])).

cnf(c_3795,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_277,c_14])).

cnf(c_5503,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_5480,c_3794,c_3795])).

cnf(c_9103,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(light_normalisation,[status(thm)],[c_9087,c_5503])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_270,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_9])).

cnf(c_1044,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_270,c_11])).

cnf(c_1068,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1044,c_108])).

cnf(c_9104,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9103,c_11,c_1068])).

cnf(c_22520,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_626,c_9104])).

cnf(c_13,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_184,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_13,c_12,c_0])).

cnf(c_1052,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_11,c_184])).

cnf(c_1055,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_11,c_8])).

cnf(c_1063,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1052,c_11,c_1055])).

cnf(c_30450,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK2,sK4),sK3)) = k4_xboole_0(k4_xboole_0(sK2,sK4),sK3) ),
    inference(superposition,[status(thm)],[c_22520,c_1063])).

cnf(c_23174,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK2,sK4)) = k2_xboole_0(k2_xboole_0(sK3,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_22520,c_8])).

cnf(c_1091,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_183,c_12])).

cnf(c_1228,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_1091,c_0])).

cnf(c_10,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_612,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_183,c_10])).

cnf(c_717,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,k4_xboole_0(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_612,c_8])).

cnf(c_718,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_717,c_8])).

cnf(c_1390,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,sK5)) = k2_xboole_0(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_1228,c_718])).

cnf(c_552,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_270,c_8])).

cnf(c_554,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_552,c_6])).

cnf(c_1232,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_1091,c_12])).

cnf(c_1400,plain,
    ( k2_xboole_0(sK5,sK4) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_1390,c_183,c_554,c_1232])).

cnf(c_1483,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_1400,c_12])).

cnf(c_23185,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK2,sK4)) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_23174,c_6,c_1400,c_1483])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1056,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_11,c_1])).

cnf(c_1062,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_1056,c_11])).

cnf(c_26777,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_1877,c_1055])).

cnf(c_27018,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_26777,c_1055])).

cnf(c_28600,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_1062,c_27018])).

cnf(c_28629,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_23185,c_28600])).

cnf(c_550,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_183,c_108])).

cnf(c_676,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),sK4) = k2_xboole_0(k2_xboole_0(sK3,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_550,c_8])).

cnf(c_677,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),sK4) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_676,c_6])).

cnf(c_609,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_10])).

cnf(c_2572,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_609,c_1])).

cnf(c_611,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_10])).

cnf(c_2576,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2572,c_9,c_108,c_611])).

cnf(c_2698,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_2576])).

cnf(c_7600,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = sK4 ),
    inference(superposition,[status(thm)],[c_677,c_2698])).

cnf(c_1054,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_11,c_1])).

cnf(c_24220,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) ),
    inference(superposition,[status(thm)],[c_677,c_1054])).

cnf(c_931,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_184,c_8])).

cnf(c_1747,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_931,c_0])).

cnf(c_1783,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1747,c_1232])).

cnf(c_1784,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1783,c_183])).

cnf(c_1945,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,X0)),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1784,c_547])).

cnf(c_3428,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1945,c_8])).

cnf(c_1224,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK5,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1091,c_12])).

cnf(c_1249,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) = k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1232,c_12])).

cnf(c_1268,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1224,c_1232,c_1249])).

cnf(c_3429,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_3428,c_6,c_1268,c_1400,c_1483])).

cnf(c_24280,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,X0)),k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,X0)),k4_xboole_0(X1,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(sK3,sK2)),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_3429,c_1054])).

cnf(c_7629,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,X0)),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK2,k4_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_1784,c_2698])).

cnf(c_24629,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,X0)),k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(sK3,sK2)),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_24280,c_7629])).

cnf(c_24631,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_24629])).

cnf(c_24677,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_24220,c_24631])).

cnf(c_24678,plain,
    ( k4_xboole_0(sK4,sK4) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_24677,c_7600])).

cnf(c_29062,plain,
    ( sP0_iProver_split = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_28629,c_547,c_7600,c_24678])).

cnf(c_30863,plain,
    ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(k4_xboole_0(sK2,sK4),sK3)) = k4_xboole_0(k4_xboole_0(sK2,sK4),sK3) ),
    inference(light_normalisation,[status(thm)],[c_30450,c_29062])).

cnf(c_30864,plain,
    ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK2,k2_xboole_0(sK4,sK3))) = k4_xboole_0(sK2,k2_xboole_0(sK4,sK3)) ),
    inference(demodulation,[status(thm)],[c_30863,c_11])).

cnf(c_613,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_8])).

cnf(c_616,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_613,c_8])).

cnf(c_276,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_12,c_0])).

cnf(c_2464,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_183,c_276])).

cnf(c_2992,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_2464,c_616])).

cnf(c_22672,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK4,sK2),X0),k2_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2992,c_9104])).

cnf(c_2461,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_6,c_276])).

cnf(c_7244,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
    inference(superposition,[status(thm)],[c_1232,c_2461])).

cnf(c_7281,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_2461,c_12])).

cnf(c_7329,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(light_normalisation,[status(thm)],[c_7281,c_5503])).

cnf(c_7330,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_7329,c_2461,c_5503])).

cnf(c_7381,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
    inference(demodulation,[status(thm)],[c_7244,c_7330])).

cnf(c_7382,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(demodulation,[status(thm)],[c_7381,c_183,c_5503])).

cnf(c_22751,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK4,sK2),X0),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_22672,c_7382])).

cnf(c_31642,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK4,sK2),X0),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_22751,c_22751,c_29062])).

cnf(c_31680,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK4,sK2),sK2),k2_xboole_0(sK2,sK3)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_616,c_31642])).

cnf(c_669,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_672,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_669,c_9,c_547])).

cnf(c_2711,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_2576,c_11])).

cnf(c_17587,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_672,c_2711])).

cnf(c_17687,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_17587,c_11])).

cnf(c_31824,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK2,sK3)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_31680,c_10,c_17687])).

cnf(c_32019,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_0,c_31824])).

cnf(c_1766,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_10,c_1747])).

cnf(c_16764,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1766])).

cnf(c_55295,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),sK4),sP0_iProver_split) = k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_32019,c_16764])).

cnf(c_55416,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_16764,c_276])).

cnf(c_2481,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_1747,c_276])).

cnf(c_1631,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_547,c_8])).

cnf(c_1634,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1631,c_6])).

cnf(c_4219,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1634])).

cnf(c_9376,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_276,c_4219])).

cnf(c_4225,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_12,c_1634])).

cnf(c_3767,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_277,c_555])).

cnf(c_4314,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_4225,c_12,c_3767])).

cnf(c_9561,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_9376,c_4314])).

cnf(c_55438,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(demodulation,[status(thm)],[c_55416,c_2481,c_9561])).

cnf(c_55812,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,sK3),k2_xboole_0(sP0_iProver_split,sK2)) = k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) ),
    inference(demodulation,[status(thm)],[c_55295,c_55438])).

cnf(c_3003,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2464,c_547])).

cnf(c_3616,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,sK3),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14,c_3003])).

cnf(c_8954,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_3616])).

cnf(c_26708,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK3,sK4),sK3)) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8954,c_1055])).

cnf(c_27106,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK4,sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_26708,c_6,c_609])).

cnf(c_1742,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_931,c_12])).

cnf(c_14682,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_0,c_1742])).

cnf(c_37727,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK4,sK3),X0),sK2) = k2_xboole_0(k4_xboole_0(sK4,sK3),sK2) ),
    inference(superposition,[status(thm)],[c_27106,c_14682])).

cnf(c_27477,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,sK3),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_27106,c_1877])).

cnf(c_27513,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,sK3),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_27477,c_27106])).

cnf(c_37949,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK4,sK3),X0),sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_37727,c_27513])).

cnf(c_37950,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK3,X0)),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_37949,c_11])).

cnf(c_42681,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK4,k2_xboole_0(sK3,X0))) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[status(thm)],[c_37950,c_2461])).

cnf(c_42705,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK4,k2_xboole_0(sK3,X0))) = k2_xboole_0(k4_xboole_0(sK2,X1),sK2) ),
    inference(superposition,[status(thm)],[c_37950,c_14682])).

cnf(c_42719,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK4,k2_xboole_0(sK3,X0))) = sK2 ),
    inference(demodulation,[status(thm)],[c_42705,c_931])).

cnf(c_42732,plain,
    ( k2_xboole_0(k1_xboole_0,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_42681,c_42719])).

cnf(c_42733,plain,
    ( k2_xboole_0(sP0_iProver_split,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_42732,c_29062])).

cnf(c_55813,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,sK3),sK2) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_55812,c_626,c_42733])).

cnf(c_58887,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,sK3)) = k4_xboole_0(sK2,k2_xboole_0(sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_55813,c_609])).

cnf(c_2999,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_2464,c_10])).

cnf(c_14057,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,sK3)) = k4_xboole_0(sK5,k2_xboole_0(sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_14,c_2999])).

cnf(c_2995,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK5) = k4_xboole_0(k2_xboole_0(sK4,X0),sK5) ),
    inference(superposition,[status(thm)],[c_2464,c_609])).

cnf(c_7130,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,sK3),sK5) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK5) ),
    inference(superposition,[status(thm)],[c_14,c_2995])).

cnf(c_7193,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,sK3),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_7130,c_612])).

cnf(c_7922,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK4),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_0,c_7193])).

cnf(c_922,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_10,c_184])).

cnf(c_936,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_922,c_672])).

cnf(c_19070,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK4),sK5) = k2_xboole_0(k4_xboole_0(sK4,sK5),sK5) ),
    inference(superposition,[status(thm)],[c_7922,c_936])).

cnf(c_19212,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK4),sK5) = k2_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_19070,c_936])).

cnf(c_19213,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK4),sK5) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_19212,c_183])).

cnf(c_19964,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19213,c_1611])).

cnf(c_21098,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)),k1_xboole_0)) = k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_19964,c_184])).

cnf(c_500,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_21125,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(k2_xboole_0(sK3,sK4),k1_xboole_0)) = k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_21098,c_11,c_500])).

cnf(c_7286,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2461,c_616])).

cnf(c_2761,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_616,c_616])).

cnf(c_2778,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2761,c_1877])).

cnf(c_7325,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_7286,c_2778])).

cnf(c_21126,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)) = k4_xboole_0(sK5,k2_xboole_0(sK4,sK3)) ),
    inference(demodulation,[status(thm)],[c_21125,c_7325])).

cnf(c_58941,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK4,sK3)) = k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_58887,c_14057,c_21126])).

cnf(c_917,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_184])).

cnf(c_1247,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_554,c_1232])).

cnf(c_1257,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1247,c_183])).

cnf(c_22542,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,sK3),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1257,c_9104])).

cnf(c_26718,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK5,sK3),sK3)) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_22542,c_1055])).

cnf(c_2546,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_8,c_609])).

cnf(c_2584,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2546,c_609])).

cnf(c_27092,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK5,sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_26718,c_6,c_2584])).

cnf(c_27420,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK3),X0)) = k2_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_27092,c_12])).

cnf(c_26732,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK5,k4_xboole_0(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_183,c_1055])).

cnf(c_1231,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_1091,c_8])).

cnf(c_3787,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_277,c_2464])).

cnf(c_10932,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1231,c_1231,c_1483,c_3787])).

cnf(c_27667,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_26732,c_10932])).

cnf(c_1098,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_12,c_10])).

cnf(c_42096,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k4_xboole_0(X0,sK4)) = k4_xboole_0(k2_xboole_0(sK4,sK5),k4_xboole_0(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_27667,c_1098])).

cnf(c_42440,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k4_xboole_0(X0,sK4)) = k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(X0,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_42096,c_183])).

cnf(c_69498,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),X0),sK4)) = k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),X0),sK4)) ),
    inference(superposition,[status(thm)],[c_27420,c_42440])).

cnf(c_27687,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK2,sK4),sK4)) = k2_xboole_0(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_22520,c_26732])).

cnf(c_27761,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sK2,sK4)) = sK5 ),
    inference(demodulation,[status(thm)],[c_27687,c_6,c_2584])).

cnf(c_29411,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK2,sK4),X0)) = k2_xboole_0(sK5,X0) ),
    inference(superposition,[status(thm)],[c_27761,c_12])).

cnf(c_74382,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) = k2_xboole_0(sK5,sK2) ),
    inference(superposition,[status(thm)],[c_917,c_29411])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_269,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,negated_conjecture,
    ( r1_xboole_0(sK4,sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_135,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK2 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_136,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) ),
    inference(unflattening,[status(thm)],[c_135])).

cnf(c_266,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_136])).

cnf(c_10469,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_269,c_266])).

cnf(c_69421,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) = k2_xboole_0(sK2,sK5) ),
    inference(superposition,[status(thm)],[c_917,c_27420])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(sK5,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_126,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK5 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_17])).

cnf(c_127,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) ),
    inference(unflattening,[status(thm)],[c_126])).

cnf(c_267,plain,
    ( r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_127])).

cnf(c_662,plain,
    ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1,c_267])).

cnf(c_10470,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_269,c_662])).

cnf(c_69591,plain,
    ( k2_xboole_0(sK2,sK5) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_69421,c_10470])).

cnf(c_69592,plain,
    ( k2_xboole_0(sK2,sK5) = sK2 ),
    inference(demodulation,[status(thm)],[c_69591,c_6])).

cnf(c_69687,plain,
    ( k2_xboole_0(sK5,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_69592,c_0])).

cnf(c_74572,plain,
    ( k2_xboole_0(sK5,k1_xboole_0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_74382,c_10469,c_69687])).

cnf(c_74573,plain,
    ( sK2 = sK5 ),
    inference(demodulation,[status(thm)],[c_74572,c_6])).

cnf(c_141321,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),X0),sK4)) = k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),X0),sK4)) ),
    inference(light_normalisation,[status(thm)],[c_69498,c_69498,c_74573])).

cnf(c_141393,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))),sK4)) = k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))),k4_xboole_0(sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_917,c_141321])).

cnf(c_141586,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),k1_xboole_0),sK4)) = k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,k1_xboole_0)),k4_xboole_0(sK5,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_141393,c_10470])).

cnf(c_1485,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) = k4_xboole_0(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_1400,c_10])).

cnf(c_2111,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,sK4)) = k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_1485,c_1])).

cnf(c_2115,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,sK4)) = k4_xboole_0(sK4,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2111,c_550])).

cnf(c_2116,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,sK4)) = sK4 ),
    inference(demodulation,[status(thm)],[c_2115,c_9])).

cnf(c_74820,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(sK5,sK4)) = sK4 ),
    inference(demodulation,[status(thm)],[c_74573,c_2116])).

cnf(c_275,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_12,c_0])).

cnf(c_1564,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_184,c_275])).

cnf(c_114624,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_1564,c_672])).

cnf(c_114629,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_1564,c_10])).

cnf(c_2902,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_672,c_11])).

cnf(c_110475,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_14682,c_2902])).

cnf(c_110385,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1747,c_2902])).

cnf(c_110945,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_110385,c_11])).

cnf(c_114773,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_114629,c_11,c_110475,c_110945])).

cnf(c_114776,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_114624,c_114773])).

cnf(c_7582,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_2698])).

cnf(c_1038,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_11])).

cnf(c_129530,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_7582,c_1038])).

cnf(c_2886,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_10,c_672])).

cnf(c_2920,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2886,c_1877])).

cnf(c_129547,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(light_normalisation,[status(thm)],[c_129530,c_2920,c_110475])).

cnf(c_141587,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) = sK4 ),
    inference(demodulation,[status(thm)],[c_141586,c_6,c_74820,c_114776,c_129547])).

cnf(c_1767,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_11,c_1747])).

cnf(c_141411,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),k4_xboole_0(sK5,k2_xboole_0(sK3,X0))),sK4)) = k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,X0)))),k4_xboole_0(k4_xboole_0(sK5,sK3),sK4)) ),
    inference(superposition,[status(thm)],[c_1767,c_141321])).

cnf(c_3000,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2464,c_108])).

cnf(c_26698,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3000,c_1055])).

cnf(c_27122,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,X0)) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_26698,c_6,c_1400,c_1483])).

cnf(c_28069,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,X0),k4_xboole_0(k4_xboole_0(sK5,X0),k4_xboole_0(X1,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(sK3,sK2)),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_27122,c_1054])).

cnf(c_7586,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_12,c_2698])).

cnf(c_22035,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,X0),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK5,X0) ),
    inference(superposition,[status(thm)],[c_3429,c_7586])).

cnf(c_28085,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(k4_xboole_0(sK5,X1),k4_xboole_0(sK5,X1)) ),
    inference(light_normalisation,[status(thm)],[c_28069,c_22035])).

cnf(c_28086,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,X0),k4_xboole_0(sK5,X0)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_28085,c_11,c_24631])).

cnf(c_21589,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) = X1 ),
    inference(superposition,[status(thm)],[c_1038,c_184])).

cnf(c_19100,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_936,c_0])).

cnf(c_21710,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2))) = X0 ),
    inference(demodulation,[status(thm)],[c_21589,c_11,c_19100])).

cnf(c_59436,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,X0),k4_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(sP0_iProver_split,X1))) = k4_xboole_0(sK5,X0) ),
    inference(superposition,[status(thm)],[c_28086,c_21710])).

cnf(c_31197,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(sP0_iProver_split,X1)) = k4_xboole_0(k4_xboole_0(sK5,X0),X1) ),
    inference(superposition,[status(thm)],[c_28086,c_2711])).

cnf(c_31214,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(sP0_iProver_split,X1)) = k4_xboole_0(sK5,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_31197,c_11])).

cnf(c_59668,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,X0),k4_xboole_0(sK5,k2_xboole_0(X0,X1))) = k4_xboole_0(sK5,X0) ),
    inference(light_normalisation,[status(thm)],[c_59436,c_31214])).

cnf(c_74834,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_74573,c_2464])).

cnf(c_2570,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_609,c_184])).

cnf(c_2577,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2570,c_8,c_611])).

cnf(c_7456,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X2,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_11,c_2577])).

cnf(c_128413,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK5,k2_xboole_0(sK4,X1))),k2_xboole_0(sK3,sK5)) = k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_74834,c_7456])).

cnf(c_4130,plain,
    ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK4,X0),sK5),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2464,c_1611])).

cnf(c_55331,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(k2_xboole_0(sK4,X0),sK5)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK4,X0),sK5),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_4130,c_16764])).

cnf(c_55677,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK4,X0),sK5),X0),k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK4,X0),sK5),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(demodulation,[status(thm)],[c_55331,c_55438])).

cnf(c_7152,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK4,X0),sK5),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_2995,c_931])).

cnf(c_27675,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sK4,sK4)) = k2_xboole_0(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_550,c_26732])).

cnf(c_27777,plain,
    ( k2_xboole_0(sK5,sP0_iProver_split) = k2_xboole_0(sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_27675,c_24678])).

cnf(c_27778,plain,
    ( k2_xboole_0(sK5,sP0_iProver_split) = sK5 ),
    inference(demodulation,[status(thm)],[c_27777,c_6])).

cnf(c_29275,plain,
    ( k2_xboole_0(sP0_iProver_split,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_27778,c_1228])).

cnf(c_29281,plain,
    ( k2_xboole_0(sP0_iProver_split,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_29275,c_183])).

cnf(c_55678,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK4,X0),sK5),X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_55677,c_7152,c_29062,c_29281])).

cnf(c_74814,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),sK5) = k4_xboole_0(k2_xboole_0(sK4,X0),sK5) ),
    inference(demodulation,[status(thm)],[c_74573,c_2995])).

cnf(c_2553,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_276,c_609])).

cnf(c_74863,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,X0),sK5) = k4_xboole_0(k2_xboole_0(sK4,X0),sK5) ),
    inference(demodulation,[status(thm)],[c_74814,c_2553])).

cnf(c_89714,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X0),sK5),X0),k2_xboole_0(sK3,sK5)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_55678,c_55678,c_74573,c_74863])).

cnf(c_128452,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X1),sK5),X1))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK5))),k2_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_89714,c_7456])).

cnf(c_128875,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X1),sK5),X1))) = k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_128452,c_7456])).

cnf(c_89815,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X1),sK5),X1))) = k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK5)))) ),
    inference(superposition,[status(thm)],[c_89714,c_1055])).

cnf(c_26730,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(superposition,[status(thm)],[c_12,c_1055])).

cnf(c_1101,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X1)))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_12,c_8])).

cnf(c_1105,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1101,c_12])).

cnf(c_1106,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_1105,c_1055])).

cnf(c_48560,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X0)))) = k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(superposition,[status(thm)],[c_11,c_1106])).

cnf(c_74848,plain,
    ( k2_xboole_0(sK3,sK5) = k2_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_74573,c_183])).

cnf(c_75232,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK5),X0) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_74848,c_12])).

cnf(c_74844,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
    inference(demodulation,[status(thm)],[c_74573,c_1232])).

cnf(c_75271,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK5),X0) ),
    inference(light_normalisation,[status(thm)],[c_75232,c_74844])).

cnf(c_89861,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X1),sK5),X1))) = k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_89815,c_26730,c_48560,c_75271])).

cnf(c_128876,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_128875,c_89861])).

cnf(c_128905,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK5,k2_xboole_0(sK4,X1))),k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_128413,c_128876])).

cnf(c_76004,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,sK5)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_74834,c_275])).

cnf(c_5429,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
    inference(superposition,[status(thm)],[c_1228,c_1877])).

cnf(c_5554,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_5429,c_5503])).

cnf(c_4239,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,X0)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_1228,c_1634])).

cnf(c_1590,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_275,c_1228])).

cnf(c_4304,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4239,c_1590])).

cnf(c_5555,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_5554,c_183,c_4304])).

cnf(c_74818,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_74573,c_5555])).

cnf(c_84698,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,sK5)),k2_xboole_0(sK3,sK5)),k2_xboole_0(sK5,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,sK5)),k2_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1055,c_74818])).

cnf(c_26855,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X3,X2)) = k2_xboole_0(X3,k2_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1055,c_277])).

cnf(c_5430,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
    inference(superposition,[status(thm)],[c_1232,c_1877])).

cnf(c_5552,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_5430,c_5503])).

cnf(c_4240,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(sK5,X0)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_1232,c_1634])).

cnf(c_4303,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(sK5,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4240,c_1590])).

cnf(c_5553,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_5552,c_183,c_4303])).

cnf(c_74819,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,X0)),k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_74573,c_5553])).

cnf(c_76050,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),X1) = k2_xboole_0(sK5,k2_xboole_0(k2_xboole_0(sK4,X0),X1)) ),
    inference(superposition,[status(thm)],[c_74834,c_12])).

cnf(c_2997,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(k2_xboole_0(sK4,X0),X1)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1) ),
    inference(superposition,[status(thm)],[c_2464,c_12])).

cnf(c_1392,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1) = k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) ),
    inference(superposition,[status(thm)],[c_1228,c_12])).

cnf(c_3015,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(k2_xboole_0(sK4,X0),X1)) = k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_2997,c_1392])).

cnf(c_76110,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),X1) = k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_76050,c_3015])).

cnf(c_1589,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK5,X1))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_275,c_1232])).

cnf(c_76111,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),X1) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_76110,c_1589,c_9561])).

cnf(c_76112,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),X1) = k2_xboole_0(sK3,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_76111,c_74573])).

cnf(c_84845,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_84698,c_26855,c_74819,c_76112])).

cnf(c_128906,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK5))))) = k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_128905,c_76004,c_84845])).

cnf(c_128907,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,X1)))) = k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_128906,c_26730])).

cnf(c_141558,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(sK5,X0))),k4_xboole_0(sK5,k2_xboole_0(sK4,sK3))) = k2_xboole_0(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) ),
    inference(demodulation,[status(thm)],[c_141411,c_59668,c_114776,c_128907,c_129547])).

cnf(c_141559,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(sK5,X0))),k4_xboole_0(sK5,k2_xboole_0(sK3,sK4))) = k2_xboole_0(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) ),
    inference(light_normalisation,[status(thm)],[c_141558,c_21126])).

cnf(c_74773,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK4),sK5) = k2_xboole_0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_74573,c_19213])).

cnf(c_75611,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK3,sK4)) = k2_xboole_0(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_74773,c_0])).

cnf(c_76475,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(sK5,k2_xboole_0(sK3,sK4))) = k2_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_75611,c_672])).

cnf(c_141560,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) = k2_xboole_0(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_141559,c_1747,c_76475])).

cnf(c_141588,plain,
    ( k2_xboole_0(sK3,sK4) = sK4 ),
    inference(demodulation,[status(thm)],[c_141587,c_141560])).

cnf(c_24206,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
    inference(superposition,[status(thm)],[c_183,c_1054])).

cnf(c_2113,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_1485,c_8])).

cnf(c_2114,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_2113,c_626])).

cnf(c_24268,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(X0,sK4))) = k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_2114,c_1054])).

cnf(c_24635,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(X0,sK4))))) = k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(demodulation,[status(thm)],[c_24268,c_11])).

cnf(c_19429,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_11,c_19100])).

cnf(c_24636,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) ),
    inference(demodulation,[status(thm)],[c_24635,c_11,c_19100,c_19429])).

cnf(c_24689,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
    inference(demodulation,[status(thm)],[c_24206,c_24636])).

cnf(c_64879,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK4),sK5),k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4))) = k4_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_24689,c_917])).

cnf(c_64914,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK4,sK5)),k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4))) = k4_xboole_0(X0,sK4) ),
    inference(demodulation,[status(thm)],[c_64879,c_11])).

cnf(c_64915,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4))) = k4_xboole_0(X0,sK4) ),
    inference(light_normalisation,[status(thm)],[c_64914,c_183])).

cnf(c_64997,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)),sK4))) = k4_xboole_0(k2_xboole_0(sK3,sK4),sK4) ),
    inference(superposition,[status(thm)],[c_8954,c_64915])).

cnf(c_65171,plain,
    ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)),sK4))) = k4_xboole_0(k2_xboole_0(sK3,sK4),sK4) ),
    inference(light_normalisation,[status(thm)],[c_64997,c_29062])).

cnf(c_19039,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_11,c_936])).

cnf(c_2482,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,X0)),k2_xboole_0(sK3,X1)) = k2_xboole_0(X1,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_1784,c_276])).

cnf(c_11747,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))),sK5) = k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK3,sK2)),sK5) ),
    inference(superposition,[status(thm)],[c_2482,c_2995])).

cnf(c_1626,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK5),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1257,c_547])).

cnf(c_2898,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,sK5),k2_xboole_0(sK3,sK2)),k1_xboole_0) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1626,c_672])).

cnf(c_2478,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK5),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_1257,c_276])).

cnf(c_2910,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_2898,c_9,c_2478])).

cnf(c_11763,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(light_normalisation,[status(thm)],[c_11747,c_612,c_2910])).

cnf(c_19075,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))),sK5) = k2_xboole_0(k4_xboole_0(sK4,sK5),sK5) ),
    inference(superposition,[status(thm)],[c_11763,c_936])).

cnf(c_19205,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))),sK5) = k2_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_19075,c_936])).

cnf(c_19206,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))),sK5) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_19205,c_183])).

cnf(c_22698,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19206,c_9104])).

cnf(c_30452,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK5,X0),X0)) = k4_xboole_0(k4_xboole_0(sK5,X0),X0) ),
    inference(superposition,[status(thm)],[c_22698,c_1063])).

cnf(c_30859,plain,
    ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(k4_xboole_0(sK5,X0),X0)) = k4_xboole_0(k4_xboole_0(sK5,X0),X0) ),
    inference(light_normalisation,[status(thm)],[c_30452,c_29062])).

cnf(c_30860,plain,
    ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK5,X0)) = k4_xboole_0(sK5,X0) ),
    inference(demodulation,[status(thm)],[c_30859,c_2584])).

cnf(c_65172,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK3),sK4)) = k4_xboole_0(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_65171,c_10,c_19039,c_30860])).

cnf(c_21502,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),X2) ),
    inference(superposition,[status(thm)],[c_609,c_1038])).

cnf(c_21833,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
    inference(light_normalisation,[status(thm)],[c_21502,c_9,c_108])).

cnf(c_150888,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),sK4),sK5),k2_xboole_0(k4_xboole_0(sK3,sK4),X0)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),sK4),X0) ),
    inference(superposition,[status(thm)],[c_65172,c_21833])).

cnf(c_2858,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,X1),X2)) = X2 ),
    inference(superposition,[status(thm)],[c_12,c_672])).

cnf(c_141729,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0)),k4_xboole_0(sK4,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_141587,c_2858])).

cnf(c_141745,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)))) = k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_141587,c_672])).

cnf(c_141750,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) ),
    inference(superposition,[status(thm)],[c_141587,c_10])).

cnf(c_2883,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_672])).

cnf(c_2922,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2883,c_1747])).

cnf(c_74847,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),sK5) = k4_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_74573,c_612])).

cnf(c_74849,plain,
    ( k4_xboole_0(sK4,sK5) = k4_xboole_0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_74847,c_10])).

cnf(c_141863,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_141750,c_2922,c_74849])).

cnf(c_141865,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)) ),
    inference(demodulation,[status(thm)],[c_141745,c_141863])).

cnf(c_142434,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK3,sK5)),X0)),k4_xboole_0(sK4,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_141729,c_141865])).

cnf(c_17632,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)),k4_xboole_0(X0,X2)) = k2_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_2711,c_672])).

cnf(c_3690,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_8,c_277])).

cnf(c_17668,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X2,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_17632,c_3690])).

cnf(c_1089,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_8,c_12])).

cnf(c_1115,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1089,c_12])).

cnf(c_1774,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_1747,c_12])).

cnf(c_61860,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),k2_xboole_0(X1,X3))) ),
    inference(superposition,[status(thm)],[c_1115,c_1774])).

cnf(c_2466,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_931,c_276])).

cnf(c_62041,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(X3,k2_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_61860,c_2466,c_9561])).

cnf(c_142435,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_142434,c_17668,c_62041])).

cnf(c_151215,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),sK4),sK5),X0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),sK4),X0) ),
    inference(light_normalisation,[status(thm)],[c_150888,c_142435])).

cnf(c_2463,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_14,c_276])).

cnf(c_99343,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_917,c_2463])).

cnf(c_11930,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_917,c_276])).

cnf(c_99663,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(X2,X0) ),
    inference(light_normalisation,[status(thm)],[c_99343,c_11930])).

cnf(c_151216,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),sK4),X0) = k4_xboole_0(k2_xboole_0(sK4,sK5),X0) ),
    inference(demodulation,[status(thm)],[c_151215,c_99663])).

cnf(c_151217,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),sK4),X0) = k4_xboole_0(k2_xboole_0(sK3,sK5),X0) ),
    inference(light_normalisation,[status(thm)],[c_151216,c_74848])).

cnf(c_65008,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) = k4_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_0,c_64915])).

cnf(c_96661,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) = k4_xboole_0(X0,sK4) ),
    inference(light_normalisation,[status(thm)],[c_65008,c_65008,c_74573])).

cnf(c_152730,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK3),sK4))))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),sK4),sK4) ),
    inference(superposition,[status(thm)],[c_151217,c_96661])).

cnf(c_19069,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,sK3),sK5) = k2_xboole_0(k4_xboole_0(sK4,sK5),sK5) ),
    inference(superposition,[status(thm)],[c_7193,c_936])).

cnf(c_19214,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,sK3),sK5) = k2_xboole_0(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_19069,c_936])).

cnf(c_19215,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,sK3),sK5) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_19214,c_183])).

cnf(c_20038,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_19215,c_12])).

cnf(c_20665,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),sK4) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) ),
    inference(superposition,[status(thm)],[c_20038,c_609])).

cnf(c_20730,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),sK4) = k4_xboole_0(sK5,sK4) ),
    inference(light_normalisation,[status(thm)],[c_20665,c_1485])).

cnf(c_29276,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sP0_iProver_split)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_27778,c_1232])).

cnf(c_29280,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,sP0_iProver_split)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_29276,c_183])).

cnf(c_5843,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5553,c_108])).

cnf(c_29605,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sP0_iProver_split,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_29280,c_5843])).

cnf(c_29614,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_29605,c_29062,c_29281])).

cnf(c_74736,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(sK3,sK5)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_74573,c_29614])).

cnf(c_1233,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(k2_xboole_0(sK3,sK2),X0))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_1091,c_14])).

cnf(c_11233,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(sK5,k2_xboole_0(sK4,X0)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1233,c_1233,c_1483,c_3787])).

cnf(c_4463,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK4,X1))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_277,c_3787])).

cnf(c_1568,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_626,c_275])).

cnf(c_4954,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_277,c_1568])).

cnf(c_11234,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_11233,c_1590,c_4463,c_4954])).

cnf(c_27680,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK2,sK5),sK4)) = k2_xboole_0(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1626,c_26732])).

cnf(c_26691,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_609,c_1055])).

cnf(c_27131,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_26691,c_1055])).

cnf(c_3793,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_277,c_609])).

cnf(c_27132,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_27131,c_3793,c_9561])).

cnf(c_27769,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK2,sK5),sK4)) = sK5 ),
    inference(demodulation,[status(thm)],[c_27680,c_6,c_27132])).

cnf(c_31053,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK5,sK2),sK4)) = sK5 ),
    inference(superposition,[status(thm)],[c_0,c_27769])).

cnf(c_35314,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK5,sK2),sK4),X0),k2_xboole_0(X0,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_31053,c_9104])).

cnf(c_35343,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK5,sK2),sK4),X0),k2_xboole_0(X0,sK5)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_35314,c_29062])).

cnf(c_17597,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_2698,c_2711])).

cnf(c_17684,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X3)) = k4_xboole_0(X0,k2_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(demodulation,[status(thm)],[c_17597,c_11,c_9561])).

cnf(c_35344,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(X0,k2_xboole_0(sK4,sK5))) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_35343,c_11,c_17684,c_17687])).

cnf(c_35345,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_35344,c_183])).

cnf(c_35612,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_11234,c_35345])).

cnf(c_36055,plain,
    ( k4_xboole_0(X0,sP0_iProver_split) = X0 ),
    inference(superposition,[status(thm)],[c_35612,c_7586])).

cnf(c_152722,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),sP0_iProver_split) = k2_xboole_0(k4_xboole_0(sK5,sK3),sK4) ),
    inference(superposition,[status(thm)],[c_151217,c_36055])).

cnf(c_74846,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_74573,c_626])).

cnf(c_75708,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(sK4,k2_xboole_0(sK3,sK5))) = k2_xboole_0(sK3,sK5) ),
    inference(superposition,[status(thm)],[c_74846,c_672])).

cnf(c_74730,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK5)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_74573,c_32019])).

cnf(c_75762,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),sP0_iProver_split) = k2_xboole_0(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_75708,c_74730])).

cnf(c_152833,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,sK3),sK4) = k2_xboole_0(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_152722,c_75762])).

cnf(c_153680,plain,
    ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(sK5,sK4) ),
    inference(light_normalisation,[status(thm)],[c_152730,c_20730,c_65172,c_74736,c_152833])).

cnf(c_37731,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK4),X0),sK5) = k2_xboole_0(k4_xboole_0(sK2,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_27761,c_14682])).

cnf(c_29407,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK4),sK5) = k2_xboole_0(sK5,k4_xboole_0(sK2,sK4)) ),
    inference(superposition,[status(thm)],[c_27761,c_1877])).

cnf(c_29455,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK4),sK5) = sK5 ),
    inference(demodulation,[status(thm)],[c_29407,c_27761])).

cnf(c_37941,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK4),X0),sK5) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_37731,c_29455])).

cnf(c_37942,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k2_xboole_0(sK4,X0)),sK5) = sK5 ),
    inference(demodulation,[status(thm)],[c_37941,c_11])).

cnf(c_1041,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_10,c_11])).

cnf(c_1072,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_1041,c_11])).

cnf(c_40005,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k2_xboole_0(sK4,X0)),k2_xboole_0(sK5,X1)) = k4_xboole_0(sK5,k2_xboole_0(sK5,X1)) ),
    inference(superposition,[status(thm)],[c_37942,c_1072])).

cnf(c_1099,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_108])).

cnf(c_29244,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK5,k2_xboole_0(sP0_iProver_split,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_27778,c_1099])).

cnf(c_29252,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sP0_iProver_split,X0)) = k2_xboole_0(sK5,X0) ),
    inference(superposition,[status(thm)],[c_27778,c_12])).

cnf(c_29302,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK5,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_29244,c_29252])).

cnf(c_29303,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK5,X0)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_29302,c_29062])).

cnf(c_40070,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k2_xboole_0(sK4,X0)),k2_xboole_0(sK5,X1)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_40005,c_11,c_29303])).

cnf(c_85107,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK4,X0)),k2_xboole_0(sK5,X1)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_40070,c_40070,c_74573])).

cnf(c_85199,plain,
    ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK5,k2_xboole_0(sK4,X0))) = k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_85107,c_931])).

cnf(c_2994,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(sK4,X0))) = k2_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_2464,c_672])).

cnf(c_13915,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_2994])).

cnf(c_13984,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(sK5,sK4)) = sK4 ),
    inference(demodulation,[status(thm)],[c_13915,c_6,c_2461])).

cnf(c_19078,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK4,k4_xboole_0(sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_13984,c_936])).

cnf(c_19201,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_19078,c_19100])).

cnf(c_14087,plain,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,sK2)),sK4) = k4_xboole_0(sK5,k2_xboole_0(sK4,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_6,c_2999])).

cnf(c_2558,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK4) = k4_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
    inference(superposition,[status(thm)],[c_1228,c_609])).

cnf(c_14164,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK3),sK4) = k4_xboole_0(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_14087,c_6,c_2461,c_2558])).

cnf(c_14258,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_14164,c_1747])).

cnf(c_19202,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_19201,c_1400,c_14258])).

cnf(c_21059,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,k4_xboole_0(sK5,sK4))) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_19202,c_12])).

cnf(c_56267,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(sK5,sK4)),sK2) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK2) ),
    inference(superposition,[status(thm)],[c_21059,c_609])).

cnf(c_56345,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(sK5,sK4)),sK2) = k4_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_56267,c_10])).

cnf(c_87423,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(sK5,sK4)),sK5) = k4_xboole_0(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_56345,c_56345,c_74573])).

cnf(c_150923,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,k2_xboole_0(sK3,k4_xboole_0(sK5,sK4))),k2_xboole_0(k4_xboole_0(sK3,sK5),X0)) = k4_xboole_0(sK5,X0) ),
    inference(superposition,[status(thm)],[c_87423,c_21833])).

cnf(c_74680,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK3,k4_xboole_0(sK5,sK4))) = k2_xboole_0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_74573,c_21059])).

cnf(c_74842,plain,
    ( k2_xboole_0(sK3,sK5) = k2_xboole_0(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_74573,c_1400])).

cnf(c_75318,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_74842,c_1072])).

cnf(c_145803,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK3,sK5)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_10469,c_10469,c_29062,c_74573,c_74849])).

cnf(c_14217,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(k4_xboole_0(sK5,sK4),X0)) = k4_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_13984,c_11])).

cnf(c_142046,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(k4_xboole_0(sK5,sK4),X0)) = k4_xboole_0(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_14217,c_14217,c_74573])).

cnf(c_142073,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) = k4_xboole_0(k2_xboole_0(sK5,sK3),sK5) ),
    inference(superposition,[status(thm)],[c_917,c_142046])).

cnf(c_142320,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,sK5))) = k4_xboole_0(k2_xboole_0(sK5,sK3),sK5) ),
    inference(light_normalisation,[status(thm)],[c_142073,c_74849])).

cnf(c_24213,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,sK5))) ),
    inference(superposition,[status(thm)],[c_1400,c_1054])).

cnf(c_1486,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1400,c_108])).

cnf(c_715,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_612,c_1])).

cnf(c_1491,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = k4_xboole_0(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1486,c_715])).

cnf(c_1492,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = sK5 ),
    inference(demodulation,[status(thm)],[c_1491,c_9])).

cnf(c_3971,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK2),sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_1492,c_184])).

cnf(c_3976,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sK4,sK5)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3971,c_612])).

cnf(c_24221,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(X0,sK5))) = k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_3976,c_1054])).

cnf(c_24670,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(X0,sK5))))) = k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(demodulation,[status(thm)],[c_24221,c_11])).

cnf(c_24671,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,X0),sK5)) ),
    inference(demodulation,[status(thm)],[c_24670,c_11,c_19100,c_19429])).

cnf(c_24685,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,X0),sK5)) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,sK5))) ),
    inference(demodulation,[status(thm)],[c_24213,c_24671])).

cnf(c_1763,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_1747])).

cnf(c_1388,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1228,c_12])).

cnf(c_92580,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK5))) = k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_1388,c_74573])).

cnf(c_92849,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK5))),k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(sK4,sK5),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_92580,c_1098])).

cnf(c_92886,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK5))),k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_92849,c_74848])).

cnf(c_112613,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k2_xboole_0(sK3,sK5))),X0) = k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_1763,c_92886])).

cnf(c_112961,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k2_xboole_0(sK3,sK5))),X0) = k4_xboole_0(k2_xboole_0(sK3,sK5),X0) ),
    inference(light_normalisation,[status(thm)],[c_112613,c_1763])).

cnf(c_5337,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_1763,c_12])).

cnf(c_42012,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X0) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(superposition,[status(thm)],[c_276,c_1098])).

cnf(c_112962,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK3),X0) = k4_xboole_0(k2_xboole_0(sK3,sK5),X0) ),
    inference(demodulation,[status(thm)],[c_112961,c_5337,c_42012])).

cnf(c_142321,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,sK5))) = k4_xboole_0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_142320,c_10,c_24685,c_112962])).

cnf(c_145804,plain,
    ( k4_xboole_0(sK4,sP0_iProver_split) = k4_xboole_0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_145803,c_142321])).

cnf(c_30435,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK4,X0),X0)) = k4_xboole_0(k2_xboole_0(sK4,X0),X0) ),
    inference(superposition,[status(thm)],[c_3003,c_1063])).

cnf(c_30885,plain,
    ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(k2_xboole_0(sK4,X0),X0)) = k4_xboole_0(k2_xboole_0(sK4,X0),X0) ),
    inference(light_normalisation,[status(thm)],[c_30435,c_29062])).

cnf(c_30886,plain,
    ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK4,X0)) = k4_xboole_0(sK4,X0) ),
    inference(demodulation,[status(thm)],[c_30885,c_10])).

cnf(c_34389,plain,
    ( k4_xboole_0(sK4,sP0_iProver_split) = k2_xboole_0(sP0_iProver_split,sK4) ),
    inference(superposition,[status(thm)],[c_30886,c_8])).

cnf(c_32038,plain,
    ( k2_xboole_0(sP0_iProver_split,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_31824,c_931])).

cnf(c_34414,plain,
    ( k4_xboole_0(sK4,sP0_iProver_split) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_34389,c_32038])).

cnf(c_145805,plain,
    ( k4_xboole_0(sK3,sK5) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_145804,c_34414])).

cnf(c_151166,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,X0) ),
    inference(light_normalisation,[status(thm)],[c_150923,c_74680,c_75318,c_145805])).

cnf(c_153681,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_153680,c_30860,c_85199,c_151166])).

cnf(c_29259,plain,
    ( k2_xboole_0(sP0_iProver_split,sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_27778,c_0])).

cnf(c_29356,plain,
    ( k4_xboole_0(sK5,k4_xboole_0(sP0_iProver_split,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_29259,c_672])).

cnf(c_29258,plain,
    ( k4_xboole_0(sP0_iProver_split,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_27778,c_547])).

cnf(c_29292,plain,
    ( k4_xboole_0(sP0_iProver_split,sK5) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_29258,c_29062])).

cnf(c_29388,plain,
    ( k4_xboole_0(sK5,sP0_iProver_split) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_29356,c_29292])).

cnf(c_141751,plain,
    ( k4_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_141587,c_108])).

cnf(c_142404,plain,
    ( k4_xboole_0(sK3,sK4) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_141751,c_29062])).

cnf(c_153682,plain,
    ( k4_xboole_0(sK5,sK4) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_153681,c_29388,c_142404])).

cnf(c_161568,plain,
    ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK5,k2_xboole_0(sK3,sK4))) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_30864,c_30864,c_58941,c_141588,c_153682])).

cnf(c_30451,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK5,sK3),sK3)) = k4_xboole_0(k4_xboole_0(sK5,sK3),sK3) ),
    inference(superposition,[status(thm)],[c_22542,c_1063])).

cnf(c_30861,plain,
    ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(k4_xboole_0(sK5,sK3),sK3)) = k4_xboole_0(k4_xboole_0(sK5,sK3),sK3) ),
    inference(light_normalisation,[status(thm)],[c_30451,c_29062])).

cnf(c_30862,plain,
    ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK5,sK3)) = k4_xboole_0(sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_30861,c_2584])).

cnf(c_37726,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK5,sK3),X0),sK2) = k2_xboole_0(k4_xboole_0(sK5,sK3),sK2) ),
    inference(superposition,[status(thm)],[c_27092,c_14682])).

cnf(c_27416,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,sK3),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK5,sK3)) ),
    inference(superposition,[status(thm)],[c_27092,c_1877])).

cnf(c_27459,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,sK3),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_27416,c_27092])).

cnf(c_37951,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK5,sK3),X0),sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_37726,c_27459])).

cnf(c_37952,plain,
    ( k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,X0)),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_37951,c_11])).

cnf(c_42818,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,X0)),k2_xboole_0(sK2,X1)) = k4_xboole_0(sK2,k2_xboole_0(sK2,X1)) ),
    inference(superposition,[status(thm)],[c_37952,c_1072])).

cnf(c_42679,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK3,X0)),k2_xboole_0(sK2,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_37950,c_1099])).

cnf(c_42686,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK3,X0)),k2_xboole_0(sK2,X1)) = k2_xboole_0(sK2,X1) ),
    inference(superposition,[status(thm)],[c_37950,c_12])).

cnf(c_42736,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_42679,c_42686])).

cnf(c_42737,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_42736,c_29062])).

cnf(c_42880,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,X0)),k2_xboole_0(sK2,X1)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_42818,c_11,c_42737])).

cnf(c_86104,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,X0)),k2_xboole_0(sK5,X1)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_42880,c_42880,c_74573])).

cnf(c_86192,plain,
    ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK5,k2_xboole_0(sK3,X0))) = k4_xboole_0(sK5,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_86104,c_931])).

cnf(c_27684,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK4),sK4)) = k2_xboole_0(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8954,c_26732])).

cnf(c_27765,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sK3,sK4)) = sK5 ),
    inference(demodulation,[status(thm)],[c_27684,c_6,c_10])).

cnf(c_48544,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,sK3)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_27765,c_1106])).

cnf(c_49106,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,sK3)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_48544,c_183])).

cnf(c_50607,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK3),sK4) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) ),
    inference(superposition,[status(thm)],[c_49106,c_609])).

cnf(c_50697,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK3),sK4) = k4_xboole_0(sK5,sK4) ),
    inference(light_normalisation,[status(thm)],[c_50607,c_1485])).

cnf(c_160029,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK3),sK4) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_50697,c_50697,c_153682])).

cnf(c_160073,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,X0) ),
    inference(superposition,[status(thm)],[c_160029,c_11])).

cnf(c_161209,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,k2_xboole_0(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_616,c_160073])).

cnf(c_161499,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(X0,sK4)) = k4_xboole_0(sK5,X0) ),
    inference(demodulation,[status(thm)],[c_161209,c_160073])).

cnf(c_161569,plain,
    ( k4_xboole_0(sK5,sK3) = sK5 ),
    inference(demodulation,[status(thm)],[c_161568,c_30862,c_86192,c_161499])).

cnf(c_65026,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK5),X1),k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X1),sK4))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK5),X1),sK4) ),
    inference(superposition,[status(thm)],[c_2711,c_64915])).

cnf(c_3735,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_277])).

cnf(c_42289,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),sK4)) = k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_1098,c_26732])).

cnf(c_42311,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),sK4)) = k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,X1),sK4)) ),
    inference(demodulation,[status(thm)],[c_42289,c_26732])).

cnf(c_65024,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(k1_xboole_0,sK4))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK4) ),
    inference(superposition,[status(thm)],[c_3000,c_64915])).

cnf(c_1379,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_0,c_1228])).

cnf(c_14330,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK4) = k4_xboole_0(k2_xboole_0(X0,sK5),sK4) ),
    inference(superposition,[status(thm)],[c_1379,c_609])).

cnf(c_65135,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,sK4)) = k4_xboole_0(k2_xboole_0(X0,sK5),sK4) ),
    inference(light_normalisation,[status(thm)],[c_65024,c_14330,c_29062,c_32038])).

cnf(c_65136,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,sK4)) = k4_xboole_0(k2_xboole_0(X0,sK5),sK4) ),
    inference(demodulation,[status(thm)],[c_65135,c_10])).

cnf(c_3126,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_3000])).

cnf(c_65027,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(k1_xboole_0,sK4))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),sK4) ),
    inference(superposition,[status(thm)],[c_3126,c_64915])).

cnf(c_65130,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,sK4)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),sK4) ),
    inference(light_normalisation,[status(thm)],[c_65027,c_29062,c_32038])).

cnf(c_65131,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,sK4)) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))),sK4) ),
    inference(demodulation,[status(thm)],[c_65130,c_2553])).

cnf(c_65137,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),sK4) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),sK5),sK4) ),
    inference(demodulation,[status(thm)],[c_65136,c_65131])).

cnf(c_65138,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),sK4) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK5)),sK4) ),
    inference(demodulation,[status(thm)],[c_65137,c_9561])).

cnf(c_102576,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK5)),sK4)) = k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,X1),sK4)) ),
    inference(light_normalisation,[status(thm)],[c_42311,c_42311,c_65138])).

cnf(c_74748,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k2_xboole_0(sK5,k4_xboole_0(X0,sK4)) ),
    inference(demodulation,[status(thm)],[c_74573,c_26732])).

cnf(c_77334,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(X0,sK3)) = k2_xboole_0(sK5,k4_xboole_0(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_74748,c_1055])).

cnf(c_102577,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK5)),sK4)) = k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,X1),sK3)) ),
    inference(demodulation,[status(thm)],[c_102576,c_77334])).

cnf(c_102658,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,X1),sK3)),sK5) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK5)),sK4),sK5) ),
    inference(superposition,[status(thm)],[c_102577,c_609])).

cnf(c_7642,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))),X0) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_2698,c_672])).

cnf(c_7660,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X0) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_7642,c_1055])).

cnf(c_102794,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK5)),k2_xboole_0(sK3,sK5)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_102658,c_11,c_7660,c_74848])).

cnf(c_116051,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK5),X1),k2_xboole_0(sK3,sK5)) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(sK5,X0)),k2_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_3735,c_102794])).

cnf(c_103027,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK5,X1)),k2_xboole_0(sK3,sK5)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK5)),k2_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1877,c_102794])).

cnf(c_103165,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK5,X1)),k2_xboole_0(sK3,sK5)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_103027,c_102794])).

cnf(c_116149,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK5),X1),k2_xboole_0(sK3,sK5)) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_116051,c_103165])).

cnf(c_138071,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK5),X0),sK4) ),
    inference(light_normalisation,[status(thm)],[c_65026,c_65026,c_74573,c_116149])).

cnf(c_96725,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0))),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) ),
    inference(superposition,[status(thm)],[c_96661,c_609])).

cnf(c_75245,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
    inference(superposition,[status(thm)],[c_74848,c_1054])).

cnf(c_75265,plain,
    ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) ),
    inference(light_normalisation,[status(thm)],[c_75245,c_24689])).

cnf(c_96801,plain,
    ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0))),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) ),
    inference(light_normalisation,[status(thm)],[c_96725,c_75265])).

cnf(c_22121,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1747,c_7586])).

cnf(c_96802,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) ),
    inference(demodulation,[status(thm)],[c_96801,c_22121])).

cnf(c_138072,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK5),X0),sK4) ),
    inference(demodulation,[status(thm)],[c_138071,c_96802])).

cnf(c_161637,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X0),k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(sK4,sK5))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK5),sK3),sK4) ),
    inference(superposition,[status(thm)],[c_161569,c_138072])).

cnf(c_74841,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK5)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_74573,c_1486])).

cnf(c_74850,plain,
    ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK5)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_74841,c_29062])).

cnf(c_1900,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_555,c_12])).

cnf(c_1914,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1900,c_12])).

cnf(c_50617,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,sK3)) = k4_xboole_0(k2_xboole_0(X0,sK4),k2_xboole_0(sK5,sK3)) ),
    inference(superposition,[status(thm)],[c_49106,c_1098])).

cnf(c_50623,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK4,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_49106,c_276])).

cnf(c_51565,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,sK3)) = k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK5,sK3)) ),
    inference(superposition,[status(thm)],[c_50623,c_609])).

cnf(c_74688,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK5,sK3)) = k2_xboole_0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_74573,c_49106])).

cnf(c_75416,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),k2_xboole_0(sK5,sK3)) = k4_xboole_0(k2_xboole_0(X0,sK4),k2_xboole_0(sK5,sK3)) ),
    inference(superposition,[status(thm)],[c_74688,c_1098])).

cnf(c_36470,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X2)) ),
    inference(superposition,[status(thm)],[c_1877,c_1072])).

cnf(c_36804,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_36470,c_1877])).

cnf(c_75456,plain,
    ( k4_xboole_0(k2_xboole_0(X0,sK4),k2_xboole_0(sK5,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK5,sK3)) ),
    inference(demodulation,[status(thm)],[c_75416,c_36804])).

cnf(c_76027,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_74834,c_2711])).

cnf(c_17558,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X0)))) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_276,c_2711])).

cnf(c_74824,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_74573,c_3787])).

cnf(c_76138,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) = k4_xboole_0(X0,k2_xboole_0(sK5,sK3)) ),
    inference(demodulation,[status(thm)],[c_76027,c_17558,c_74824])).

cnf(c_88803,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),k2_xboole_0(sK5,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_50617,c_51565,c_74573,c_75456,c_76138])).

cnf(c_97233,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK5)),k2_xboole_0(sK5,sK3)) = k4_xboole_0(k2_xboole_0(sK3,X0),k2_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1914,c_88803])).

cnf(c_88830,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,k2_xboole_0(sK4,X0)),k2_xboole_0(sK5,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_74834,c_88803])).

cnf(c_88949,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK5)),k2_xboole_0(sK5,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_88830,c_76004])).

cnf(c_97269,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,X0),k2_xboole_0(sK3,sK5)) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_97233,c_88949])).

cnf(c_96729,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) = k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) ),
    inference(superposition,[status(thm)],[c_96661,c_10])).

cnf(c_48690,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X0)))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X3,X0),k2_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_1106,c_2711])).

cnf(c_48860,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X0)))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_48690,c_2711])).

cnf(c_96797,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) = k4_xboole_0(X0,k2_xboole_0(sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_96729,c_11,c_27018,c_48860])).

cnf(c_96798,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_96797,c_74848])).

cnf(c_113299,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(X0,k2_xboole_0(sK3,sK5)))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_96798,c_184])).

cnf(c_3751,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(X1,sK5)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_2464,c_277])).

cnf(c_16444,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,sK5),k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK3,sK2))),sK5)) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_3751,c_5553])).

cnf(c_778,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = k2_xboole_0(k2_xboole_0(sK3,sK2),sK4) ),
    inference(superposition,[status(thm)],[c_677,c_14])).

cnf(c_782,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_778,c_677])).

cnf(c_3101,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK5) = k2_xboole_0(sK5,k2_xboole_0(sK4,sK2)) ),
    inference(superposition,[status(thm)],[c_2992,c_555])).

cnf(c_3118,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK5) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_3101,c_2992])).

cnf(c_12328,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK4),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2992,c_1099])).

cnf(c_12467,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12328,c_1400])).

cnf(c_12794,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK3)),k1_xboole_0) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_12467,c_672])).

cnf(c_2888,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),k1_xboole_0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_108,c_672])).

cnf(c_2470,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_554,c_276])).

cnf(c_2919,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2888,c_2470])).

cnf(c_3139,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_3000,c_672])).

cnf(c_2998,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_2464,c_14])).

cnf(c_1480,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_1400,c_718])).

cnf(c_2095,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_1480,c_275])).

cnf(c_2366,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK5,sK4),X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
    inference(superposition,[status(thm)],[c_2114,c_12])).

cnf(c_2375,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK5,sK4),X0)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(light_normalisation,[status(thm)],[c_2366,c_1483])).

cnf(c_2376,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_2375,c_1115,c_1590])).

cnf(c_3014,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2998,c_2095,c_2376])).

cnf(c_3151,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK2)),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_3139,c_3014])).

cnf(c_8776,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_2910,c_276])).

cnf(c_12816,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_12794,c_2919,c_3151,c_8776])).

cnf(c_16445,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_16444,c_183,c_782,c_2910,c_3118,c_12816])).

cnf(c_74779,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(sK5,sK3)) = k2_xboole_0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_74573,c_16445])).

cnf(c_75804,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK3),k4_xboole_0(k2_xboole_0(sK5,sK3),k4_xboole_0(X0,k2_xboole_0(sK3,sK5)))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) ),
    inference(superposition,[status(thm)],[c_74779,c_1054])).

cnf(c_50605,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,sK3)) = k2_xboole_0(sK4,k2_xboole_0(sK5,sK3)) ),
    inference(superposition,[status(thm)],[c_49106,c_1634])).

cnf(c_50698,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,sK3)) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_50605,c_49106])).

cnf(c_51193,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK3),k4_xboole_0(k2_xboole_0(sK5,sK3),k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_50698,c_1054])).

cnf(c_7636,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,X0),k4_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(sK5,X0) ),
    inference(superposition,[status(thm)],[c_5555,c_2698])).

cnf(c_46954,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK3),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK5,sK3) ),
    inference(superposition,[status(thm)],[c_14,c_7636])).

cnf(c_51231,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK5,sK3)) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_51193,c_24631,c_46954])).

cnf(c_17943,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_16445,c_2698])).

cnf(c_74778,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK3),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k2_xboole_0(sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_74573,c_17943])).

cnf(c_75849,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_75804,c_51231,c_74778])).

cnf(c_113324,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),sP0_iProver_split) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_113299,c_75849])).

cnf(c_161666,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK5),sK3),sK4) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(light_normalisation,[status(thm)],[c_161637,c_74848,c_74850,c_97269,c_113324])).

cnf(c_162090,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK5),sK3),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(X0,sK5),sK3))) ),
    inference(superposition,[status(thm)],[c_161666,c_1])).

cnf(c_2887,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_11,c_672])).

cnf(c_109769,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2),k4_xboole_0(X0,k2_xboole_0(X2,X1))) = X2 ),
    inference(superposition,[status(thm)],[c_1877,c_2887])).

cnf(c_109975,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X2,X1))) = X2 ),
    inference(light_normalisation,[status(thm)],[c_109769,c_19039])).

cnf(c_75250,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_74848,c_1742])).

cnf(c_75263,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK3,sK5) ),
    inference(demodulation,[status(thm)],[c_75250,c_74848])).

cnf(c_102621,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK3),sK3)) = k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK5),sK4)) ),
    inference(superposition,[status(thm)],[c_75263,c_102577])).

cnf(c_102841,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK3),sK3)) = k2_xboole_0(sK5,k4_xboole_0(sK5,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_102621,c_20730])).

cnf(c_102842,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK4,X0),sK3)) = sK5 ),
    inference(demodulation,[status(thm)],[c_102841,c_10,c_1747,c_77334])).

cnf(c_102843,plain,
    ( k2_xboole_0(sK5,k4_xboole_0(sK4,k2_xboole_0(X0,sK3))) = sK5 ),
    inference(demodulation,[status(thm)],[c_102842,c_11])).

cnf(c_156078,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK5),sK4) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_20730,c_20730,c_153682])).

cnf(c_156158,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,sK4)),sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_156078,c_2858])).

cnf(c_7247,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(k2_xboole_0(sK4,X0),sK5) ),
    inference(superposition,[status(thm)],[c_3787,c_2461])).

cnf(c_7378,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,X0),sK5) = k2_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_7247,c_7330])).

cnf(c_7383,plain,
    ( k2_xboole_0(k2_xboole_0(sK4,X0),sK5) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(demodulation,[status(thm)],[c_7382,c_7378])).

cnf(c_59527,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1)),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_21710,c_7383])).

cnf(c_1731,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_931])).

cnf(c_14710,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_1731,c_1742])).

cnf(c_14902,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = X1 ),
    inference(light_normalisation,[status(thm)],[c_14710,c_1731])).

cnf(c_14903,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_14902,c_11])).

cnf(c_50637,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(X0,sK4)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_49106,c_277])).

cnf(c_54799,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1)),k2_xboole_0(sK3,sK2)) = k2_xboole_0(k2_xboole_0(sK5,sK3),sK4) ),
    inference(superposition,[status(thm)],[c_14903,c_50637])).

cnf(c_50613,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK3,sK2)) = k2_xboole_0(k2_xboole_0(sK5,sK3),sK4) ),
    inference(superposition,[status(thm)],[c_49106,c_616])).

cnf(c_5849,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_5553,c_0])).

cnf(c_44043,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_616,c_5849])).

cnf(c_44195,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_44043,c_12816])).

cnf(c_50692,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,sK3),sK4) = k2_xboole_0(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_50613,c_44195])).

cnf(c_54830,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1)),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_54799,c_50692])).

cnf(c_59592,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1)),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
    inference(light_normalisation,[status(thm)],[c_59527,c_183,c_54830])).

cnf(c_59965,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1)))) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_59592,c_276])).

cnf(c_81476,plain,
    ( k2_xboole_0(sK5,k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1)))) = k2_xboole_0(sK3,sK5) ),
    inference(light_normalisation,[status(thm)],[c_59965,c_59965,c_74573])).

cnf(c_84715,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1))),k2_xboole_0(sK3,sK5)),k2_xboole_0(sK3,sK5)) = k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1))),k2_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_81476,c_74818])).

cnf(c_75970,plain,
    ( k2_xboole_0(k2_xboole_0(sK5,k2_xboole_0(sK4,X0)),k2_xboole_0(sK3,sK5)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_74834,c_1634])).

cnf(c_76176,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK5)),k2_xboole_0(sK3,sK5)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_75970,c_76004])).

cnf(c_81582,plain,
    ( k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1))),k2_xboole_0(X2,sK5)) = k2_xboole_0(X2,k2_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_81476,c_277])).

cnf(c_84822,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_84715,c_2470,c_76112,c_76176,c_81582])).

cnf(c_156172,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK3),sK5) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_156158,c_74842,c_84822])).

cnf(c_156301,plain,
    ( k4_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK5,X0)) = k4_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_156172,c_11])).

cnf(c_156528,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(X0,sK3))) = k4_xboole_0(k2_xboole_0(sK5,sK3),sK5) ),
    inference(superposition,[status(thm)],[c_102843,c_156301])).

cnf(c_156743,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(X0,sK3))) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_156528,c_156172])).

cnf(c_162146,plain,
    ( sK4 = sK3 ),
    inference(demodulation,[status(thm)],[c_162090,c_109975,c_156743])).

cnf(c_186,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1186,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_186])).

cnf(c_187,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_281,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_492,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_16,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f52])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_162146,c_1186,c_492,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:27:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 47.61/6.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.61/6.49  
% 47.61/6.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.61/6.49  
% 47.61/6.49  ------  iProver source info
% 47.61/6.49  
% 47.61/6.49  git: date: 2020-06-30 10:37:57 +0100
% 47.61/6.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.61/6.49  git: non_committed_changes: false
% 47.61/6.49  git: last_make_outside_of_git: false
% 47.61/6.49  
% 47.61/6.49  ------ 
% 47.61/6.49  
% 47.61/6.49  ------ Input Options
% 47.61/6.49  
% 47.61/6.49  --out_options                           all
% 47.61/6.49  --tptp_safe_out                         true
% 47.61/6.49  --problem_path                          ""
% 47.61/6.49  --include_path                          ""
% 47.61/6.49  --clausifier                            res/vclausify_rel
% 47.61/6.49  --clausifier_options                    ""
% 47.61/6.49  --stdin                                 false
% 47.61/6.49  --stats_out                             all
% 47.61/6.49  
% 47.61/6.49  ------ General Options
% 47.61/6.49  
% 47.61/6.49  --fof                                   false
% 47.61/6.49  --time_out_real                         305.
% 47.61/6.49  --time_out_virtual                      -1.
% 47.61/6.49  --symbol_type_check                     false
% 47.61/6.49  --clausify_out                          false
% 47.61/6.49  --sig_cnt_out                           false
% 47.61/6.49  --trig_cnt_out                          false
% 47.61/6.49  --trig_cnt_out_tolerance                1.
% 47.61/6.49  --trig_cnt_out_sk_spl                   false
% 47.61/6.49  --abstr_cl_out                          false
% 47.61/6.49  
% 47.61/6.49  ------ Global Options
% 47.61/6.49  
% 47.61/6.49  --schedule                              default
% 47.61/6.49  --add_important_lit                     false
% 47.61/6.49  --prop_solver_per_cl                    1000
% 47.61/6.49  --min_unsat_core                        false
% 47.61/6.49  --soft_assumptions                      false
% 47.61/6.49  --soft_lemma_size                       3
% 47.61/6.49  --prop_impl_unit_size                   0
% 47.61/6.49  --prop_impl_unit                        []
% 47.61/6.49  --share_sel_clauses                     true
% 47.61/6.49  --reset_solvers                         false
% 47.61/6.49  --bc_imp_inh                            [conj_cone]
% 47.61/6.49  --conj_cone_tolerance                   3.
% 47.61/6.49  --extra_neg_conj                        none
% 47.61/6.49  --large_theory_mode                     true
% 47.61/6.49  --prolific_symb_bound                   200
% 47.61/6.49  --lt_threshold                          2000
% 47.61/6.49  --clause_weak_htbl                      true
% 47.61/6.49  --gc_record_bc_elim                     false
% 47.61/6.49  
% 47.61/6.49  ------ Preprocessing Options
% 47.61/6.49  
% 47.61/6.49  --preprocessing_flag                    true
% 47.61/6.49  --time_out_prep_mult                    0.1
% 47.61/6.49  --splitting_mode                        input
% 47.61/6.49  --splitting_grd                         true
% 47.61/6.49  --splitting_cvd                         false
% 47.61/6.49  --splitting_cvd_svl                     false
% 47.61/6.49  --splitting_nvd                         32
% 47.61/6.49  --sub_typing                            true
% 47.61/6.49  --prep_gs_sim                           true
% 47.61/6.49  --prep_unflatten                        true
% 47.61/6.49  --prep_res_sim                          true
% 47.61/6.49  --prep_upred                            true
% 47.61/6.49  --prep_sem_filter                       exhaustive
% 47.61/6.49  --prep_sem_filter_out                   false
% 47.61/6.49  --pred_elim                             true
% 47.61/6.49  --res_sim_input                         true
% 47.61/6.49  --eq_ax_congr_red                       true
% 47.61/6.49  --pure_diseq_elim                       true
% 47.61/6.49  --brand_transform                       false
% 47.61/6.49  --non_eq_to_eq                          false
% 47.61/6.49  --prep_def_merge                        true
% 47.61/6.49  --prep_def_merge_prop_impl              false
% 47.61/6.49  --prep_def_merge_mbd                    true
% 47.61/6.49  --prep_def_merge_tr_red                 false
% 47.61/6.49  --prep_def_merge_tr_cl                  false
% 47.61/6.49  --smt_preprocessing                     true
% 47.61/6.49  --smt_ac_axioms                         fast
% 47.61/6.49  --preprocessed_out                      false
% 47.61/6.49  --preprocessed_stats                    false
% 47.61/6.49  
% 47.61/6.49  ------ Abstraction refinement Options
% 47.61/6.49  
% 47.61/6.49  --abstr_ref                             []
% 47.61/6.49  --abstr_ref_prep                        false
% 47.61/6.49  --abstr_ref_until_sat                   false
% 47.61/6.49  --abstr_ref_sig_restrict                funpre
% 47.61/6.49  --abstr_ref_af_restrict_to_split_sk     false
% 47.61/6.49  --abstr_ref_under                       []
% 47.61/6.49  
% 47.61/6.49  ------ SAT Options
% 47.61/6.49  
% 47.61/6.49  --sat_mode                              false
% 47.61/6.49  --sat_fm_restart_options                ""
% 47.61/6.49  --sat_gr_def                            false
% 47.61/6.49  --sat_epr_types                         true
% 47.61/6.49  --sat_non_cyclic_types                  false
% 47.61/6.49  --sat_finite_models                     false
% 47.61/6.49  --sat_fm_lemmas                         false
% 47.61/6.49  --sat_fm_prep                           false
% 47.61/6.49  --sat_fm_uc_incr                        true
% 47.61/6.49  --sat_out_model                         small
% 47.61/6.49  --sat_out_clauses                       false
% 47.61/6.49  
% 47.61/6.49  ------ QBF Options
% 47.61/6.49  
% 47.61/6.49  --qbf_mode                              false
% 47.61/6.49  --qbf_elim_univ                         false
% 47.61/6.49  --qbf_dom_inst                          none
% 47.61/6.49  --qbf_dom_pre_inst                      false
% 47.61/6.49  --qbf_sk_in                             false
% 47.61/6.49  --qbf_pred_elim                         true
% 47.61/6.49  --qbf_split                             512
% 47.61/6.49  
% 47.61/6.49  ------ BMC1 Options
% 47.61/6.49  
% 47.61/6.49  --bmc1_incremental                      false
% 47.61/6.49  --bmc1_axioms                           reachable_all
% 47.61/6.49  --bmc1_min_bound                        0
% 47.61/6.49  --bmc1_max_bound                        -1
% 47.61/6.49  --bmc1_max_bound_default                -1
% 47.61/6.49  --bmc1_symbol_reachability              true
% 47.61/6.49  --bmc1_property_lemmas                  false
% 47.61/6.49  --bmc1_k_induction                      false
% 47.61/6.49  --bmc1_non_equiv_states                 false
% 47.61/6.49  --bmc1_deadlock                         false
% 47.61/6.49  --bmc1_ucm                              false
% 47.61/6.49  --bmc1_add_unsat_core                   none
% 47.61/6.49  --bmc1_unsat_core_children              false
% 47.61/6.49  --bmc1_unsat_core_extrapolate_axioms    false
% 47.61/6.49  --bmc1_out_stat                         full
% 47.61/6.49  --bmc1_ground_init                      false
% 47.61/6.49  --bmc1_pre_inst_next_state              false
% 47.61/6.49  --bmc1_pre_inst_state                   false
% 47.61/6.49  --bmc1_pre_inst_reach_state             false
% 47.61/6.49  --bmc1_out_unsat_core                   false
% 47.61/6.49  --bmc1_aig_witness_out                  false
% 47.61/6.49  --bmc1_verbose                          false
% 47.61/6.49  --bmc1_dump_clauses_tptp                false
% 47.61/6.49  --bmc1_dump_unsat_core_tptp             false
% 47.61/6.49  --bmc1_dump_file                        -
% 47.61/6.49  --bmc1_ucm_expand_uc_limit              128
% 47.61/6.49  --bmc1_ucm_n_expand_iterations          6
% 47.61/6.49  --bmc1_ucm_extend_mode                  1
% 47.61/6.49  --bmc1_ucm_init_mode                    2
% 47.61/6.49  --bmc1_ucm_cone_mode                    none
% 47.61/6.49  --bmc1_ucm_reduced_relation_type        0
% 47.61/6.49  --bmc1_ucm_relax_model                  4
% 47.61/6.49  --bmc1_ucm_full_tr_after_sat            true
% 47.61/6.49  --bmc1_ucm_expand_neg_assumptions       false
% 47.61/6.49  --bmc1_ucm_layered_model                none
% 47.61/6.49  --bmc1_ucm_max_lemma_size               10
% 47.61/6.49  
% 47.61/6.49  ------ AIG Options
% 47.61/6.49  
% 47.61/6.49  --aig_mode                              false
% 47.61/6.49  
% 47.61/6.49  ------ Instantiation Options
% 47.61/6.49  
% 47.61/6.49  --instantiation_flag                    true
% 47.61/6.49  --inst_sos_flag                         true
% 47.61/6.49  --inst_sos_phase                        true
% 47.61/6.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.61/6.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.61/6.49  --inst_lit_sel_side                     num_symb
% 47.61/6.49  --inst_solver_per_active                1400
% 47.61/6.49  --inst_solver_calls_frac                1.
% 47.61/6.49  --inst_passive_queue_type               priority_queues
% 47.61/6.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.61/6.49  --inst_passive_queues_freq              [25;2]
% 47.61/6.49  --inst_dismatching                      true
% 47.61/6.49  --inst_eager_unprocessed_to_passive     true
% 47.61/6.49  --inst_prop_sim_given                   true
% 47.61/6.49  --inst_prop_sim_new                     false
% 47.61/6.49  --inst_subs_new                         false
% 47.61/6.49  --inst_eq_res_simp                      false
% 47.61/6.49  --inst_subs_given                       false
% 47.61/6.49  --inst_orphan_elimination               true
% 47.61/6.49  --inst_learning_loop_flag               true
% 47.61/6.49  --inst_learning_start                   3000
% 47.61/6.49  --inst_learning_factor                  2
% 47.61/6.49  --inst_start_prop_sim_after_learn       3
% 47.61/6.49  --inst_sel_renew                        solver
% 47.61/6.49  --inst_lit_activity_flag                true
% 47.61/6.49  --inst_restr_to_given                   false
% 47.61/6.49  --inst_activity_threshold               500
% 47.61/6.49  --inst_out_proof                        true
% 47.61/6.49  
% 47.61/6.49  ------ Resolution Options
% 47.61/6.49  
% 47.61/6.49  --resolution_flag                       true
% 47.61/6.49  --res_lit_sel                           adaptive
% 47.61/6.49  --res_lit_sel_side                      none
% 47.61/6.49  --res_ordering                          kbo
% 47.61/6.49  --res_to_prop_solver                    active
% 47.61/6.49  --res_prop_simpl_new                    false
% 47.61/6.49  --res_prop_simpl_given                  true
% 47.61/6.49  --res_passive_queue_type                priority_queues
% 47.61/6.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.61/6.49  --res_passive_queues_freq               [15;5]
% 47.61/6.49  --res_forward_subs                      full
% 47.61/6.49  --res_backward_subs                     full
% 47.61/6.49  --res_forward_subs_resolution           true
% 47.61/6.49  --res_backward_subs_resolution          true
% 47.61/6.49  --res_orphan_elimination                true
% 47.61/6.49  --res_time_limit                        2.
% 47.61/6.49  --res_out_proof                         true
% 47.61/6.49  
% 47.61/6.49  ------ Superposition Options
% 47.61/6.49  
% 47.61/6.49  --superposition_flag                    true
% 47.61/6.49  --sup_passive_queue_type                priority_queues
% 47.61/6.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.61/6.49  --sup_passive_queues_freq               [8;1;4]
% 47.61/6.49  --demod_completeness_check              fast
% 47.61/6.49  --demod_use_ground                      true
% 47.61/6.49  --sup_to_prop_solver                    passive
% 47.61/6.49  --sup_prop_simpl_new                    true
% 47.61/6.49  --sup_prop_simpl_given                  true
% 47.61/6.49  --sup_fun_splitting                     true
% 47.61/6.49  --sup_smt_interval                      50000
% 47.61/6.49  
% 47.61/6.49  ------ Superposition Simplification Setup
% 47.61/6.49  
% 47.61/6.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 47.61/6.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 47.61/6.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 47.61/6.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 47.61/6.49  --sup_full_triv                         [TrivRules;PropSubs]
% 47.61/6.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 47.61/6.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 47.61/6.49  --sup_immed_triv                        [TrivRules]
% 47.61/6.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.61/6.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.61/6.49  --sup_immed_bw_main                     []
% 47.61/6.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 47.61/6.49  --sup_input_triv                        [Unflattening;TrivRules]
% 47.61/6.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.61/6.49  --sup_input_bw                          []
% 47.61/6.49  
% 47.61/6.49  ------ Combination Options
% 47.61/6.49  
% 47.61/6.49  --comb_res_mult                         3
% 47.61/6.49  --comb_sup_mult                         2
% 47.61/6.49  --comb_inst_mult                        10
% 47.61/6.49  
% 47.61/6.49  ------ Debug Options
% 47.61/6.49  
% 47.61/6.49  --dbg_backtrace                         false
% 47.61/6.49  --dbg_dump_prop_clauses                 false
% 47.61/6.49  --dbg_dump_prop_clauses_file            -
% 47.61/6.49  --dbg_out_stat                          false
% 47.61/6.49  ------ Parsing...
% 47.61/6.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.61/6.49  
% 47.61/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 47.61/6.49  
% 47.61/6.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.61/6.49  
% 47.61/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.61/6.49  ------ Proving...
% 47.61/6.49  ------ Problem Properties 
% 47.61/6.49  
% 47.61/6.49  
% 47.61/6.49  clauses                                 18
% 47.61/6.49  conjectures                             2
% 47.61/6.49  EPR                                     1
% 47.61/6.49  Horn                                    17
% 47.61/6.49  unary                                   16
% 47.61/6.49  binary                                  2
% 47.61/6.49  lits                                    20
% 47.61/6.49  lits eq                                 15
% 47.61/6.49  fd_pure                                 0
% 47.61/6.49  fd_pseudo                               0
% 47.61/6.49  fd_cond                                 1
% 47.61/6.49  fd_pseudo_cond                          0
% 47.61/6.49  AC symbols                              1
% 47.61/6.49  
% 47.61/6.49  ------ Schedule dynamic 5 is on 
% 47.61/6.49  
% 47.61/6.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 47.61/6.49  
% 47.61/6.49  
% 47.61/6.49  ------ 
% 47.61/6.49  Current options:
% 47.61/6.49  ------ 
% 47.61/6.49  
% 47.61/6.49  ------ Input Options
% 47.61/6.49  
% 47.61/6.49  --out_options                           all
% 47.61/6.49  --tptp_safe_out                         true
% 47.61/6.49  --problem_path                          ""
% 47.61/6.49  --include_path                          ""
% 47.61/6.49  --clausifier                            res/vclausify_rel
% 47.61/6.49  --clausifier_options                    ""
% 47.61/6.49  --stdin                                 false
% 47.61/6.49  --stats_out                             all
% 47.61/6.49  
% 47.61/6.49  ------ General Options
% 47.61/6.49  
% 47.61/6.49  --fof                                   false
% 47.61/6.49  --time_out_real                         305.
% 47.61/6.49  --time_out_virtual                      -1.
% 47.61/6.49  --symbol_type_check                     false
% 47.61/6.49  --clausify_out                          false
% 47.61/6.49  --sig_cnt_out                           false
% 47.61/6.49  --trig_cnt_out                          false
% 47.61/6.49  --trig_cnt_out_tolerance                1.
% 47.61/6.49  --trig_cnt_out_sk_spl                   false
% 47.61/6.49  --abstr_cl_out                          false
% 47.61/6.49  
% 47.61/6.49  ------ Global Options
% 47.61/6.49  
% 47.61/6.49  --schedule                              default
% 47.61/6.49  --add_important_lit                     false
% 47.61/6.49  --prop_solver_per_cl                    1000
% 47.61/6.49  --min_unsat_core                        false
% 47.61/6.49  --soft_assumptions                      false
% 47.61/6.49  --soft_lemma_size                       3
% 47.61/6.49  --prop_impl_unit_size                   0
% 47.61/6.49  --prop_impl_unit                        []
% 47.61/6.49  --share_sel_clauses                     true
% 47.61/6.49  --reset_solvers                         false
% 47.61/6.49  --bc_imp_inh                            [conj_cone]
% 47.61/6.49  --conj_cone_tolerance                   3.
% 47.61/6.49  --extra_neg_conj                        none
% 47.61/6.49  --large_theory_mode                     true
% 47.61/6.49  --prolific_symb_bound                   200
% 47.61/6.49  --lt_threshold                          2000
% 47.61/6.49  --clause_weak_htbl                      true
% 47.61/6.49  --gc_record_bc_elim                     false
% 47.61/6.49  
% 47.61/6.49  ------ Preprocessing Options
% 47.61/6.49  
% 47.61/6.49  --preprocessing_flag                    true
% 47.61/6.49  --time_out_prep_mult                    0.1
% 47.61/6.49  --splitting_mode                        input
% 47.61/6.49  --splitting_grd                         true
% 47.61/6.49  --splitting_cvd                         false
% 47.61/6.49  --splitting_cvd_svl                     false
% 47.61/6.49  --splitting_nvd                         32
% 47.61/6.49  --sub_typing                            true
% 47.61/6.49  --prep_gs_sim                           true
% 47.61/6.49  --prep_unflatten                        true
% 47.61/6.49  --prep_res_sim                          true
% 47.61/6.49  --prep_upred                            true
% 47.61/6.49  --prep_sem_filter                       exhaustive
% 47.61/6.49  --prep_sem_filter_out                   false
% 47.61/6.49  --pred_elim                             true
% 47.61/6.49  --res_sim_input                         true
% 47.61/6.49  --eq_ax_congr_red                       true
% 47.61/6.49  --pure_diseq_elim                       true
% 47.61/6.49  --brand_transform                       false
% 47.61/6.49  --non_eq_to_eq                          false
% 47.61/6.49  --prep_def_merge                        true
% 47.61/6.49  --prep_def_merge_prop_impl              false
% 47.61/6.49  --prep_def_merge_mbd                    true
% 47.61/6.49  --prep_def_merge_tr_red                 false
% 47.61/6.49  --prep_def_merge_tr_cl                  false
% 47.61/6.49  --smt_preprocessing                     true
% 47.61/6.49  --smt_ac_axioms                         fast
% 47.61/6.49  --preprocessed_out                      false
% 47.61/6.49  --preprocessed_stats                    false
% 47.61/6.49  
% 47.61/6.49  ------ Abstraction refinement Options
% 47.61/6.49  
% 47.61/6.49  --abstr_ref                             []
% 47.61/6.49  --abstr_ref_prep                        false
% 47.61/6.49  --abstr_ref_until_sat                   false
% 47.61/6.49  --abstr_ref_sig_restrict                funpre
% 47.61/6.49  --abstr_ref_af_restrict_to_split_sk     false
% 47.61/6.49  --abstr_ref_under                       []
% 47.61/6.49  
% 47.61/6.49  ------ SAT Options
% 47.61/6.49  
% 47.61/6.49  --sat_mode                              false
% 47.61/6.49  --sat_fm_restart_options                ""
% 47.61/6.49  --sat_gr_def                            false
% 47.61/6.49  --sat_epr_types                         true
% 47.61/6.49  --sat_non_cyclic_types                  false
% 47.61/6.49  --sat_finite_models                     false
% 47.61/6.49  --sat_fm_lemmas                         false
% 47.61/6.49  --sat_fm_prep                           false
% 47.61/6.49  --sat_fm_uc_incr                        true
% 47.61/6.49  --sat_out_model                         small
% 47.61/6.49  --sat_out_clauses                       false
% 47.61/6.49  
% 47.61/6.49  ------ QBF Options
% 47.61/6.49  
% 47.61/6.49  --qbf_mode                              false
% 47.61/6.49  --qbf_elim_univ                         false
% 47.61/6.49  --qbf_dom_inst                          none
% 47.61/6.49  --qbf_dom_pre_inst                      false
% 47.61/6.49  --qbf_sk_in                             false
% 47.61/6.49  --qbf_pred_elim                         true
% 47.61/6.49  --qbf_split                             512
% 47.61/6.49  
% 47.61/6.49  ------ BMC1 Options
% 47.61/6.49  
% 47.61/6.49  --bmc1_incremental                      false
% 47.61/6.49  --bmc1_axioms                           reachable_all
% 47.61/6.49  --bmc1_min_bound                        0
% 47.61/6.49  --bmc1_max_bound                        -1
% 47.61/6.49  --bmc1_max_bound_default                -1
% 47.61/6.49  --bmc1_symbol_reachability              true
% 47.61/6.49  --bmc1_property_lemmas                  false
% 47.61/6.49  --bmc1_k_induction                      false
% 47.61/6.49  --bmc1_non_equiv_states                 false
% 47.61/6.49  --bmc1_deadlock                         false
% 47.61/6.49  --bmc1_ucm                              false
% 47.61/6.49  --bmc1_add_unsat_core                   none
% 47.61/6.49  --bmc1_unsat_core_children              false
% 47.61/6.49  --bmc1_unsat_core_extrapolate_axioms    false
% 47.61/6.49  --bmc1_out_stat                         full
% 47.61/6.49  --bmc1_ground_init                      false
% 47.61/6.49  --bmc1_pre_inst_next_state              false
% 47.61/6.49  --bmc1_pre_inst_state                   false
% 47.61/6.49  --bmc1_pre_inst_reach_state             false
% 47.61/6.49  --bmc1_out_unsat_core                   false
% 47.61/6.49  --bmc1_aig_witness_out                  false
% 47.61/6.49  --bmc1_verbose                          false
% 47.61/6.49  --bmc1_dump_clauses_tptp                false
% 47.61/6.49  --bmc1_dump_unsat_core_tptp             false
% 47.61/6.49  --bmc1_dump_file                        -
% 47.61/6.49  --bmc1_ucm_expand_uc_limit              128
% 47.61/6.49  --bmc1_ucm_n_expand_iterations          6
% 47.61/6.49  --bmc1_ucm_extend_mode                  1
% 47.61/6.49  --bmc1_ucm_init_mode                    2
% 47.61/6.49  --bmc1_ucm_cone_mode                    none
% 47.61/6.49  --bmc1_ucm_reduced_relation_type        0
% 47.61/6.49  --bmc1_ucm_relax_model                  4
% 47.61/6.49  --bmc1_ucm_full_tr_after_sat            true
% 47.61/6.49  --bmc1_ucm_expand_neg_assumptions       false
% 47.61/6.49  --bmc1_ucm_layered_model                none
% 47.61/6.49  --bmc1_ucm_max_lemma_size               10
% 47.61/6.49  
% 47.61/6.49  ------ AIG Options
% 47.61/6.49  
% 47.61/6.49  --aig_mode                              false
% 47.61/6.49  
% 47.61/6.49  ------ Instantiation Options
% 47.61/6.49  
% 47.61/6.49  --instantiation_flag                    true
% 47.61/6.49  --inst_sos_flag                         true
% 47.61/6.49  --inst_sos_phase                        true
% 47.61/6.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.61/6.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.61/6.49  --inst_lit_sel_side                     none
% 47.61/6.49  --inst_solver_per_active                1400
% 47.61/6.49  --inst_solver_calls_frac                1.
% 47.61/6.49  --inst_passive_queue_type               priority_queues
% 47.61/6.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.61/6.49  --inst_passive_queues_freq              [25;2]
% 47.61/6.49  --inst_dismatching                      true
% 47.61/6.49  --inst_eager_unprocessed_to_passive     true
% 47.61/6.49  --inst_prop_sim_given                   true
% 47.61/6.49  --inst_prop_sim_new                     false
% 47.61/6.49  --inst_subs_new                         false
% 47.61/6.49  --inst_eq_res_simp                      false
% 47.61/6.49  --inst_subs_given                       false
% 47.61/6.49  --inst_orphan_elimination               true
% 47.61/6.49  --inst_learning_loop_flag               true
% 47.61/6.49  --inst_learning_start                   3000
% 47.61/6.49  --inst_learning_factor                  2
% 47.61/6.49  --inst_start_prop_sim_after_learn       3
% 47.61/6.49  --inst_sel_renew                        solver
% 47.61/6.49  --inst_lit_activity_flag                true
% 47.61/6.49  --inst_restr_to_given                   false
% 47.61/6.49  --inst_activity_threshold               500
% 47.61/6.49  --inst_out_proof                        true
% 47.61/6.49  
% 47.61/6.49  ------ Resolution Options
% 47.61/6.49  
% 47.61/6.49  --resolution_flag                       false
% 47.61/6.49  --res_lit_sel                           adaptive
% 47.61/6.49  --res_lit_sel_side                      none
% 47.61/6.49  --res_ordering                          kbo
% 47.61/6.49  --res_to_prop_solver                    active
% 47.61/6.49  --res_prop_simpl_new                    false
% 47.61/6.49  --res_prop_simpl_given                  true
% 47.61/6.49  --res_passive_queue_type                priority_queues
% 47.61/6.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.61/6.49  --res_passive_queues_freq               [15;5]
% 47.61/6.49  --res_forward_subs                      full
% 47.61/6.49  --res_backward_subs                     full
% 47.61/6.49  --res_forward_subs_resolution           true
% 47.61/6.49  --res_backward_subs_resolution          true
% 47.61/6.49  --res_orphan_elimination                true
% 47.61/6.49  --res_time_limit                        2.
% 47.61/6.49  --res_out_proof                         true
% 47.61/6.49  
% 47.61/6.49  ------ Superposition Options
% 47.61/6.49  
% 47.61/6.49  --superposition_flag                    true
% 47.61/6.49  --sup_passive_queue_type                priority_queues
% 47.61/6.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.61/6.49  --sup_passive_queues_freq               [8;1;4]
% 47.61/6.49  --demod_completeness_check              fast
% 47.61/6.49  --demod_use_ground                      true
% 47.61/6.49  --sup_to_prop_solver                    passive
% 47.61/6.49  --sup_prop_simpl_new                    true
% 47.61/6.49  --sup_prop_simpl_given                  true
% 47.61/6.49  --sup_fun_splitting                     true
% 47.61/6.49  --sup_smt_interval                      50000
% 47.61/6.49  
% 47.61/6.49  ------ Superposition Simplification Setup
% 47.61/6.49  
% 47.61/6.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 47.61/6.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 47.61/6.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 47.61/6.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 47.61/6.49  --sup_full_triv                         [TrivRules;PropSubs]
% 47.61/6.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 47.61/6.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 47.61/6.49  --sup_immed_triv                        [TrivRules]
% 47.61/6.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.61/6.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.61/6.49  --sup_immed_bw_main                     []
% 47.61/6.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 47.61/6.49  --sup_input_triv                        [Unflattening;TrivRules]
% 47.61/6.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.61/6.49  --sup_input_bw                          []
% 47.61/6.49  
% 47.61/6.49  ------ Combination Options
% 47.61/6.49  
% 47.61/6.49  --comb_res_mult                         3
% 47.61/6.49  --comb_sup_mult                         2
% 47.61/6.49  --comb_inst_mult                        10
% 47.61/6.49  
% 47.61/6.49  ------ Debug Options
% 47.61/6.49  
% 47.61/6.49  --dbg_backtrace                         false
% 47.61/6.49  --dbg_dump_prop_clauses                 false
% 47.61/6.49  --dbg_dump_prop_clauses_file            -
% 47.61/6.49  --dbg_out_stat                          false
% 47.61/6.49  
% 47.61/6.49  
% 47.61/6.49  
% 47.61/6.49  
% 47.61/6.49  ------ Proving...
% 47.61/6.49  
% 47.61/6.49  
% 47.61/6.49  % SZS status Theorem for theBenchmark.p
% 47.61/6.49  
% 47.61/6.49  % SZS output start CNFRefutation for theBenchmark.p
% 47.61/6.49  
% 47.61/6.49  fof(f17,conjecture,(
% 47.61/6.49    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f18,negated_conjecture,(
% 47.61/6.49    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 47.61/6.49    inference(negated_conjecture,[],[f17])).
% 47.61/6.49  
% 47.61/6.49  fof(f24,plain,(
% 47.61/6.49    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 47.61/6.49    inference(ennf_transformation,[],[f18])).
% 47.61/6.49  
% 47.61/6.49  fof(f25,plain,(
% 47.61/6.49    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 47.61/6.49    inference(flattening,[],[f24])).
% 47.61/6.49  
% 47.61/6.49  fof(f30,plain,(
% 47.61/6.49    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK3 != sK4 & r1_xboole_0(sK5,sK3) & r1_xboole_0(sK4,sK2) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5))),
% 47.61/6.49    introduced(choice_axiom,[])).
% 47.61/6.49  
% 47.61/6.49  fof(f31,plain,(
% 47.61/6.49    sK3 != sK4 & r1_xboole_0(sK5,sK3) & r1_xboole_0(sK4,sK2) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5)),
% 47.61/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f30])).
% 47.61/6.49  
% 47.61/6.49  fof(f49,plain,(
% 47.61/6.49    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5)),
% 47.61/6.49    inference(cnf_transformation,[],[f31])).
% 47.61/6.49  
% 47.61/6.49  fof(f13,axiom,(
% 47.61/6.49    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f45,plain,(
% 47.61/6.49    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 47.61/6.49    inference(cnf_transformation,[],[f13])).
% 47.61/6.49  
% 47.61/6.49  fof(f1,axiom,(
% 47.61/6.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f32,plain,(
% 47.61/6.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 47.61/6.49    inference(cnf_transformation,[],[f1])).
% 47.61/6.49  
% 47.61/6.49  fof(f15,axiom,(
% 47.61/6.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f47,plain,(
% 47.61/6.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 47.61/6.49    inference(cnf_transformation,[],[f15])).
% 47.61/6.49  
% 47.61/6.49  fof(f8,axiom,(
% 47.61/6.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f40,plain,(
% 47.61/6.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 47.61/6.49    inference(cnf_transformation,[],[f8])).
% 47.61/6.49  
% 47.61/6.49  fof(f5,axiom,(
% 47.61/6.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f20,plain,(
% 47.61/6.49    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 47.61/6.49    inference(unused_predicate_definition_removal,[],[f5])).
% 47.61/6.49  
% 47.61/6.49  fof(f23,plain,(
% 47.61/6.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 47.61/6.49    inference(ennf_transformation,[],[f20])).
% 47.61/6.49  
% 47.61/6.49  fof(f37,plain,(
% 47.61/6.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 47.61/6.49    inference(cnf_transformation,[],[f23])).
% 47.61/6.49  
% 47.61/6.49  fof(f16,axiom,(
% 47.61/6.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f48,plain,(
% 47.61/6.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 47.61/6.49    inference(cnf_transformation,[],[f16])).
% 47.61/6.49  
% 47.61/6.49  fof(f11,axiom,(
% 47.61/6.49    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f43,plain,(
% 47.61/6.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 47.61/6.49    inference(cnf_transformation,[],[f11])).
% 47.61/6.49  
% 47.61/6.49  fof(f6,axiom,(
% 47.61/6.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f38,plain,(
% 47.61/6.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 47.61/6.49    inference(cnf_transformation,[],[f6])).
% 47.61/6.49  
% 47.61/6.49  fof(f7,axiom,(
% 47.61/6.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f39,plain,(
% 47.61/6.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 47.61/6.49    inference(cnf_transformation,[],[f7])).
% 47.61/6.49  
% 47.61/6.49  fof(f12,axiom,(
% 47.61/6.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f44,plain,(
% 47.61/6.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 47.61/6.49    inference(cnf_transformation,[],[f12])).
% 47.61/6.49  
% 47.61/6.49  fof(f56,plain,(
% 47.61/6.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 47.61/6.49    inference(definition_unfolding,[],[f39,f44])).
% 47.61/6.49  
% 47.61/6.49  fof(f9,axiom,(
% 47.61/6.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f41,plain,(
% 47.61/6.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 47.61/6.49    inference(cnf_transformation,[],[f9])).
% 47.61/6.49  
% 47.61/6.49  fof(f14,axiom,(
% 47.61/6.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f46,plain,(
% 47.61/6.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 47.61/6.49    inference(cnf_transformation,[],[f14])).
% 47.61/6.49  
% 47.61/6.49  fof(f57,plain,(
% 47.61/6.49    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 47.61/6.49    inference(definition_unfolding,[],[f46,f44])).
% 47.61/6.49  
% 47.61/6.49  fof(f10,axiom,(
% 47.61/6.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f42,plain,(
% 47.61/6.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 47.61/6.49    inference(cnf_transformation,[],[f10])).
% 47.61/6.49  
% 47.61/6.49  fof(f2,axiom,(
% 47.61/6.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f33,plain,(
% 47.61/6.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 47.61/6.49    inference(cnf_transformation,[],[f2])).
% 47.61/6.49  
% 47.61/6.49  fof(f53,plain,(
% 47.61/6.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 47.61/6.49    inference(definition_unfolding,[],[f33,f44,f44])).
% 47.61/6.49  
% 47.61/6.49  fof(f4,axiom,(
% 47.61/6.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f22,plain,(
% 47.61/6.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 47.61/6.49    inference(ennf_transformation,[],[f4])).
% 47.61/6.49  
% 47.61/6.49  fof(f28,plain,(
% 47.61/6.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 47.61/6.49    introduced(choice_axiom,[])).
% 47.61/6.49  
% 47.61/6.49  fof(f29,plain,(
% 47.61/6.49    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 47.61/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f28])).
% 47.61/6.49  
% 47.61/6.49  fof(f36,plain,(
% 47.61/6.49    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 47.61/6.49    inference(cnf_transformation,[],[f29])).
% 47.61/6.49  
% 47.61/6.49  fof(f3,axiom,(
% 47.61/6.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 47.61/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.61/6.49  
% 47.61/6.49  fof(f19,plain,(
% 47.61/6.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 47.61/6.49    inference(rectify,[],[f3])).
% 47.61/6.49  
% 47.61/6.49  fof(f21,plain,(
% 47.61/6.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 47.61/6.49    inference(ennf_transformation,[],[f19])).
% 47.61/6.49  
% 47.61/6.49  fof(f26,plain,(
% 47.61/6.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 47.61/6.49    introduced(choice_axiom,[])).
% 47.61/6.49  
% 47.61/6.49  fof(f27,plain,(
% 47.61/6.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 47.61/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f26])).
% 47.61/6.49  
% 47.61/6.49  fof(f35,plain,(
% 47.61/6.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 47.61/6.49    inference(cnf_transformation,[],[f27])).
% 47.61/6.49  
% 47.61/6.49  fof(f54,plain,(
% 47.61/6.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 47.61/6.49    inference(definition_unfolding,[],[f35,f44])).
% 47.61/6.49  
% 47.61/6.49  fof(f50,plain,(
% 47.61/6.49    r1_xboole_0(sK4,sK2)),
% 47.61/6.49    inference(cnf_transformation,[],[f31])).
% 47.61/6.49  
% 47.61/6.49  fof(f51,plain,(
% 47.61/6.49    r1_xboole_0(sK5,sK3)),
% 47.61/6.49    inference(cnf_transformation,[],[f31])).
% 47.61/6.49  
% 47.61/6.49  fof(f52,plain,(
% 47.61/6.49    sK3 != sK4),
% 47.61/6.49    inference(cnf_transformation,[],[f31])).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19,negated_conjecture,
% 47.61/6.49      ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(cnf_transformation,[],[f49]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_12,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 47.61/6.49      inference(cnf_transformation,[],[f45]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_0,plain,
% 47.61/6.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 47.61/6.49      inference(cnf_transformation,[],[f32]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_183,negated_conjecture,
% 47.61/6.49      ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(theory_normalisation,[status(thm)],[c_19,c_12,c_0]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_14,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 47.61/6.49      inference(cnf_transformation,[],[f47]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_622,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_183,c_14]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_626,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_622,c_183]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_8,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 47.61/6.49      inference(cnf_transformation,[],[f40]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_5,plain,
% 47.61/6.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 47.61/6.49      inference(cnf_transformation,[],[f37]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_15,plain,
% 47.61/6.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 47.61/6.49      inference(cnf_transformation,[],[f48]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_107,plain,
% 47.61/6.49      ( X0 != X1
% 47.61/6.49      | k4_xboole_0(X1,X2) = k1_xboole_0
% 47.61/6.49      | k2_xboole_0(X0,X3) != X2 ),
% 47.61/6.49      inference(resolution_lifted,[status(thm)],[c_5,c_15]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_108,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 47.61/6.49      inference(unflattening,[status(thm)],[c_107]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_547,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_0,c_108]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1611,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_8,c_547]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_4103,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_0,c_1611]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_11,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 47.61/6.49      inference(cnf_transformation,[],[f43]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_9087,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_4103,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_551,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_108,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_6,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 47.61/6.49      inference(cnf_transformation,[],[f38]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_555,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_551,c_6]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1877,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_0,c_555]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_277,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_12,c_0]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_5480,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,k2_xboole_0(X2,X0)),X2)) = k2_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1877,c_277]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3794,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_277,c_555]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3795,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_277,c_14]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_5503,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_5480,c_3794,c_3795]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_9103,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k4_xboole_0(k1_xboole_0,X2) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_9087,c_5503]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 47.61/6.49      inference(cnf_transformation,[],[f56]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_9,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 47.61/6.49      inference(cnf_transformation,[],[f41]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_270,plain,
% 47.61/6.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_7,c_9]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1044,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_270,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1068,plain,
% 47.61/6.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_1044,c_108]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_9104,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,k2_xboole_0(X2,X0))) = k1_xboole_0 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_9103,c_11,c_1068]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_22520,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_626,c_9104]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_13,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 47.61/6.49      inference(cnf_transformation,[],[f57]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_184,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 47.61/6.49      inference(theory_normalisation,[status(thm)],[c_13,c_12,c_0]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1052,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = k4_xboole_0(X0,X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_11,c_184]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1055,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_11,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1063,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_1052,c_11,c_1055]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_30450,plain,
% 47.61/6.49      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK2,sK4),sK3)) = k4_xboole_0(k4_xboole_0(sK2,sK4),sK3) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_22520,c_1063]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_23174,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK2,sK4)) = k2_xboole_0(k2_xboole_0(sK3,sK2),k1_xboole_0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_22520,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1091,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_183,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1228,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1091,c_0]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_10,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 47.61/6.49      inference(cnf_transformation,[],[f42]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_612,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK2),sK5) = k4_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_183,c_10]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_717,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,k4_xboole_0(sK4,sK5)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_612,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_718,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,sK4) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_717,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1390,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(sK5,sK5)) = k2_xboole_0(sK5,sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1228,c_718]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_552,plain,
% 47.61/6.49      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_270,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_554,plain,
% 47.61/6.49      ( k2_xboole_0(X0,X0) = X0 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_552,c_6]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1232,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1091,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1400,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,sK4) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_1390,c_183,c_554,c_1232]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1483,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1400,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_23185,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK2,sK4)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_23174,c_6,c_1400,c_1483]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 47.61/6.49      inference(cnf_transformation,[],[f53]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1056,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_11,c_1]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1062,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_1056,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_26777,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1877,c_1055]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27018,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_26777,c_1055]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_28600,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_1062,c_27018]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_28629,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK2,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_23185,c_28600]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_550,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_183,c_108]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_676,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK2),sK4) = k2_xboole_0(k2_xboole_0(sK3,sK2),k1_xboole_0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_550,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_677,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK2),sK4) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_676,c_6]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_609,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_0,c_10]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2572,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_609,c_1]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_611,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_8,c_10]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2576,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_2572,c_9,c_108,c_611]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2698,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_11,c_2576]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7600,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = sK4 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_677,c_2698]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1054,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_11,c_1]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24220,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_677,c_1054]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_931,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_184,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1747,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_931,c_0]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1783,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k2_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1747,c_1232]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1784,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_1783,c_183]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1945,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,X0)),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1784,c_547]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3428,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k2_xboole_0(k2_xboole_0(sK3,sK2),k1_xboole_0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1945,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1224,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK5,X0)),X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1091,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1249,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) = k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1232,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1268,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(X0,X1)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_1224,c_1232,c_1249]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3429,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_3428,c_6,c_1268,c_1400,c_1483]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24280,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,X0)),k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,X0)),k4_xboole_0(X1,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(sK3,sK2)),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_3429,c_1054]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7629,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,X0)),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK2,k4_xboole_0(sK5,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1784,c_2698]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24629,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,X0)),k2_xboole_0(sK2,k4_xboole_0(sK5,X0))) = k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(sK3,sK2)),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_24280,c_7629]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24631,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = sP0_iProver_split ),
% 47.61/6.49      inference(splitting,
% 47.61/6.49                [splitting(split),new_symbols(definition,[])],
% 47.61/6.49                [c_24629]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24677,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = sP0_iProver_split ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_24220,c_24631]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24678,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,sK4) = sP0_iProver_split ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_24677,c_7600]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29062,plain,
% 47.61/6.49      ( sP0_iProver_split = k1_xboole_0 ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_28629,c_547,c_7600,c_24678]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_30863,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(k4_xboole_0(sK2,sK4),sK3)) = k4_xboole_0(k4_xboole_0(sK2,sK4),sK3) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_30450,c_29062]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_30864,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK2,k2_xboole_0(sK4,sK3))) = k4_xboole_0(sK2,k2_xboole_0(sK4,sK3)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_30863,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_613,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_10,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_616,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_613,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_276,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_12,c_0]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2464,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_183,c_276]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2992,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(sK4,sK2)) = k2_xboole_0(sK2,sK3) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2464,c_616]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_22672,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK4,sK2),X0),k2_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2992,c_9104]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2461,plain,
% 47.61/6.49      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_6,c_276]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7244,plain,
% 47.61/6.49      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1232,c_2461]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7281,plain,
% 47.61/6.49      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2461,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7329,plain,
% 47.61/6.49      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_7281,c_5503]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7330,plain,
% 47.61/6.49      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_7329,c_2461,c_5503]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7381,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_7244,c_7330]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7382,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(sK2,sK3)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_7381,c_183,c_5503]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_22751,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK4,sK2),X0),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_22672,c_7382]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_31642,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK4,sK2),X0),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = sP0_iProver_split ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_22751,c_22751,c_29062]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_31680,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK4,sK2),sK2),k2_xboole_0(sK2,sK3)) = sP0_iProver_split ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_616,c_31642]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_669,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_672,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_669,c_9,c_547]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2711,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2576,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_17587,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_672,c_2711]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_17687,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_17587,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_31824,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k2_xboole_0(sK2,sK3)) = sP0_iProver_split ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_31680,c_10,c_17687]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_32019,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = sP0_iProver_split ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_0,c_31824]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1766,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_10,c_1747]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_16764,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_0,c_1766]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_55295,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),sK4),sP0_iProver_split) = k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_32019,c_16764]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_55416,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_16764,c_276]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2481,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1747,c_276]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1631,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_547,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1634,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_1631,c_6]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_4219,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_0,c_1634]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_9376,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_276,c_4219]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_4225,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_12,c_1634]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3767,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_277,c_555]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_4314,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_4225,c_12,c_3767]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_9561,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_9376,c_4314]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_55438,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_55416,c_2481,c_9561]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_55812,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK4,sK3),k2_xboole_0(sP0_iProver_split,sK2)) = k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_55295,c_55438]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3003,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2464,c_547]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3616,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK4,sK3),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_14,c_3003]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_8954,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_0,c_3616]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_26708,plain,
% 47.61/6.49      ( k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK3,sK4),sK3)) = k2_xboole_0(sK2,k1_xboole_0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_8954,c_1055]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27106,plain,
% 47.61/6.49      ( k2_xboole_0(sK2,k4_xboole_0(sK4,sK3)) = sK2 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_26708,c_6,c_609]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1742,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_931,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_14682,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k2_xboole_0(X0,X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_0,c_1742]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_37727,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK4,sK3),X0),sK2) = k2_xboole_0(k4_xboole_0(sK4,sK3),sK2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27106,c_14682]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27477,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK4,sK3),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK4,sK3)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27106,c_1877]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27513,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK4,sK3),sK2) = sK2 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_27477,c_27106]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_37949,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK4,sK3),X0),sK2) = sK2 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_37727,c_27513]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_37950,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK3,X0)),sK2) = sK2 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_37949,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42681,plain,
% 47.61/6.49      ( k2_xboole_0(sK2,k4_xboole_0(sK4,k2_xboole_0(sK3,X0))) = k2_xboole_0(k1_xboole_0,sK2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_37950,c_2461]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42705,plain,
% 47.61/6.49      ( k2_xboole_0(sK2,k4_xboole_0(sK4,k2_xboole_0(sK3,X0))) = k2_xboole_0(k4_xboole_0(sK2,X1),sK2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_37950,c_14682]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42719,plain,
% 47.61/6.49      ( k2_xboole_0(sK2,k4_xboole_0(sK4,k2_xboole_0(sK3,X0))) = sK2 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_42705,c_931]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42732,plain,
% 47.61/6.49      ( k2_xboole_0(k1_xboole_0,sK2) = sK2 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_42681,c_42719]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42733,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,sK2) = sK2 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_42732,c_29062]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_55813,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK4,sK3),sK2) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_55812,c_626,c_42733]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_58887,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,sK3)) = k4_xboole_0(sK2,k2_xboole_0(sK4,sK3)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_55813,c_609]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2999,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2464,c_10]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_14057,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK4,sK3)) = k4_xboole_0(sK5,k2_xboole_0(sK4,sK3)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_14,c_2999]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2995,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK5) = k4_xboole_0(k2_xboole_0(sK4,X0),sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2464,c_609]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7130,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK4,sK3),sK5) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_14,c_2995]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7193,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK4,sK3),sK5) = k4_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_7130,c_612]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7922,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK4),sK5) = k4_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_0,c_7193]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_922,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_10,c_184]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_936,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_922,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19070,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK4),sK5) = k2_xboole_0(k4_xboole_0(sK4,sK5),sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_7922,c_936]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19212,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK4),sK5) = k2_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_19070,c_936]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19213,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK4),sK5) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_19212,c_183]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19964,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_19213,c_1611]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_21098,plain,
% 47.61/6.49      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)),k1_xboole_0)) = k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_19964,c_184]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_500,plain,
% 47.61/6.49      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_21125,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(k2_xboole_0(sK3,sK4),k1_xboole_0)) = k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_21098,c_11,c_500]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7286,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2461,c_616]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2761,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_616,c_616]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2778,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_2761,c_1877]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7325,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_7286,c_2778]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_21126,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)) = k4_xboole_0(sK5,k2_xboole_0(sK4,sK3)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_21125,c_7325]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_58941,plain,
% 47.61/6.49      ( k4_xboole_0(sK2,k2_xboole_0(sK4,sK3)) = k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_58887,c_14057,c_21126]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_917,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1,c_184]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1247,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_554,c_1232]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1257,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sK5)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_1247,c_183]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_22542,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK5,sK3),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1257,c_9104]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_26718,plain,
% 47.61/6.49      ( k2_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK5,sK3),sK3)) = k2_xboole_0(sK2,k1_xboole_0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_22542,c_1055]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2546,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_8,c_609]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2584,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_2546,c_609]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27092,plain,
% 47.61/6.49      ( k2_xboole_0(sK2,k4_xboole_0(sK5,sK3)) = sK2 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_26718,c_6,c_2584]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27420,plain,
% 47.61/6.49      ( k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK5,sK3),X0)) = k2_xboole_0(sK2,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27092,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_26732,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK5,k4_xboole_0(X0,sK4)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_183,c_1055]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1231,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1091,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3787,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_277,c_2464]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_10932,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_1231,c_1231,c_1483,c_3787]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27667,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(X0,sK4))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_26732,c_10932]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1098,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_12,c_10]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42096,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k4_xboole_0(X0,sK4)) = k4_xboole_0(k2_xboole_0(sK4,sK5),k4_xboole_0(X0,sK4)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27667,c_1098]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42440,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k4_xboole_0(X0,sK4)) = k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(X0,sK4)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_42096,c_183]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_69498,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),X0),sK4)) = k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),X0),sK4)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27420,c_42440]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27687,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK2,sK4),sK4)) = k2_xboole_0(sK5,k1_xboole_0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_22520,c_26732]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27761,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(sK2,sK4)) = sK5 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_27687,c_6,c_2584]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29411,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK2,sK4),X0)) = k2_xboole_0(sK5,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27761,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74382,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) = k2_xboole_0(sK5,sK2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_917,c_29411]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_4,plain,
% 47.61/6.49      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 47.61/6.49      inference(cnf_transformation,[],[f36]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_269,plain,
% 47.61/6.49      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 47.61/6.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2,plain,
% 47.61/6.49      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 47.61/6.49      | ~ r1_xboole_0(X1,X2) ),
% 47.61/6.49      inference(cnf_transformation,[],[f54]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_18,negated_conjecture,
% 47.61/6.49      ( r1_xboole_0(sK4,sK2) ),
% 47.61/6.49      inference(cnf_transformation,[],[f50]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_135,plain,
% 47.61/6.49      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 47.61/6.49      | sK2 != X2
% 47.61/6.49      | sK4 != X1 ),
% 47.61/6.49      inference(resolution_lifted,[status(thm)],[c_2,c_18]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_136,plain,
% 47.61/6.49      ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) ),
% 47.61/6.49      inference(unflattening,[status(thm)],[c_135]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_266,plain,
% 47.61/6.49      ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) != iProver_top ),
% 47.61/6.49      inference(predicate_to_equality,[status(thm)],[c_136]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_10469,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_269,c_266]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_69421,plain,
% 47.61/6.49      ( k2_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) = k2_xboole_0(sK2,sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_917,c_27420]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_17,negated_conjecture,
% 47.61/6.49      ( r1_xboole_0(sK5,sK3) ),
% 47.61/6.49      inference(cnf_transformation,[],[f51]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_126,plain,
% 47.61/6.49      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 47.61/6.49      | sK5 != X1
% 47.61/6.49      | sK3 != X2 ),
% 47.61/6.49      inference(resolution_lifted,[status(thm)],[c_2,c_17]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_127,plain,
% 47.61/6.49      ( ~ r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) ),
% 47.61/6.49      inference(unflattening,[status(thm)],[c_126]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_267,plain,
% 47.61/6.49      ( r2_hidden(X0,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) != iProver_top ),
% 47.61/6.49      inference(predicate_to_equality,[status(thm)],[c_127]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_662,plain,
% 47.61/6.49      ( r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) != iProver_top ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_1,c_267]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_10470,plain,
% 47.61/6.49      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_269,c_662]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_69591,plain,
% 47.61/6.49      ( k2_xboole_0(sK2,sK5) = k2_xboole_0(sK2,k1_xboole_0) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_69421,c_10470]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_69592,plain,
% 47.61/6.49      ( k2_xboole_0(sK2,sK5) = sK2 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_69591,c_6]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_69687,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,sK2) = sK2 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_69592,c_0]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74572,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k1_xboole_0) = sK2 ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_74382,c_10469,c_69687]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74573,plain,
% 47.61/6.49      ( sK2 = sK5 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74572,c_6]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_141321,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,X0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),X0),sK4)) = k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),X0),sK4)) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_69498,c_69498,c_74573]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_141393,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))),sK4)) = k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))),k4_xboole_0(sK5,sK4)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_917,c_141321]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_141586,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),k1_xboole_0),sK4)) = k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,k1_xboole_0)),k4_xboole_0(sK5,sK4)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_141393,c_10470]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1485,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) = k4_xboole_0(sK5,sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1400,c_10]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2111,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,sK4)) = k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(sK3,sK2))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1485,c_1]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2115,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,sK4)) = k4_xboole_0(sK4,k1_xboole_0) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_2111,c_550]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2116,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,sK4)) = sK4 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_2115,c_9]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74820,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(sK5,sK4)) = sK4 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_2116]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_275,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_12,c_0]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1564,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k2_xboole_0(X2,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_184,c_275]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_114624,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1564,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_114629,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X1,X2),k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1564,c_10]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2902,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_672,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_110475,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_14682,c_2902]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_110385,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1747,c_2902]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_110945,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_110385,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_114773,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_114629,c_11,c_110475,c_110945]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_114776,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_114624,c_114773]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7582,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_8,c_2698]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1038,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_129530,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)),X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_7582,c_1038]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2886,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = X1 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_10,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2920,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_2886,c_1877]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_129547,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_129530,c_2920,c_110475]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_141587,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) = sK4 ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_141586,c_6,c_74820,c_114776,c_129547]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1767,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k4_xboole_0(X0,X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_11,c_1747]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_141411,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),k4_xboole_0(sK5,k2_xboole_0(sK3,X0))),sK4)) = k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,X0)))),k4_xboole_0(k4_xboole_0(sK5,sK3),sK4)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1767,c_141321]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3000,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2464,c_108]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_26698,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),k1_xboole_0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_3000,c_1055]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27122,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK5,X0)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_26698,c_6,c_1400,c_1483]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_28069,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK5,X0),k4_xboole_0(k4_xboole_0(sK5,X0),k4_xboole_0(X1,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(k4_xboole_0(X1,k2_xboole_0(sK3,sK2)),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27122,c_1054]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7586,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = X0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_12,c_2698]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_22035,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK5,X0),k4_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK5,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_3429,c_7586]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_28085,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(k4_xboole_0(sK5,X1),k4_xboole_0(sK5,X1)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_28069,c_22035]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_28086,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK5,X0),k4_xboole_0(sK5,X0)) = sP0_iProver_split ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_28085,c_11,c_24631]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_21589,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) = X1 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1038,c_184]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19100,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_936,c_0]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_21710,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X2))) = X0 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_21589,c_11,c_19100]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_59436,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK5,X0),k4_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(sP0_iProver_split,X1))) = k4_xboole_0(sK5,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_28086,c_21710]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_31197,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(sP0_iProver_split,X1)) = k4_xboole_0(k4_xboole_0(sK5,X0),X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_28086,c_2711]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_31214,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(sP0_iProver_split,X1)) = k4_xboole_0(sK5,k2_xboole_0(X0,X1)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_31197,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_59668,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK5,X0),k4_xboole_0(sK5,k2_xboole_0(X0,X1))) = k4_xboole_0(sK5,X0) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_59436,c_31214]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74834,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_2464]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2570,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X0,X1))) = k2_xboole_0(X1,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_609,c_184]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2577,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_2570,c_8,c_611]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7456,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(X2,k4_xboole_0(X0,X1)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_11,c_2577]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_128413,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK5,k2_xboole_0(sK4,X1))),k2_xboole_0(sK3,sK5)) = k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,X1)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_74834,c_7456]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_4130,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(k2_xboole_0(sK4,X0),sK5),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2464,c_1611]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_55331,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(k2_xboole_0(sK4,X0),sK5)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK4,X0),sK5),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_4130,c_16764]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_55677,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK4,X0),sK5),X0),k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK4,X0),sK5),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_55331,c_55438]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7152,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK4,X0),sK5),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2995,c_931]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27675,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(sK4,sK4)) = k2_xboole_0(sK5,k1_xboole_0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_550,c_26732]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27777,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,sP0_iProver_split) = k2_xboole_0(sK5,k1_xboole_0) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_27675,c_24678]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27778,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,sP0_iProver_split) = sK5 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_27777,c_6]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29275,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27778,c_1228]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29281,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_29275,c_183]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_55678,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK4,X0),sK5),X0),k2_xboole_0(sK3,sK2)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_55677,c_7152,c_29062,c_29281]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74814,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),sK5) = k4_xboole_0(k2_xboole_0(sK4,X0),sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_2995]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2553,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_276,c_609]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74863,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,X0),sK5) = k4_xboole_0(k2_xboole_0(sK4,X0),sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74814,c_2553]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_89714,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X0),sK5),X0),k2_xboole_0(sK3,sK5)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_55678,c_55678,c_74573,c_74863]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_128452,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X1),sK5),X1))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK5))),k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_89714,c_7456]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_128875,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X1),sK5),X1))) = k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,X1)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_128452,c_7456]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_89815,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X1),sK5),X1))) = k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK5)))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_89714,c_1055]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_26730,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,k2_xboole_0(X3,X0)))) = k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_12,c_1055]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1101,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X1)))) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_12,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1105,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X0,X1)))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_1101,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1106,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_1105,c_1055]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_48560,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X3,X0)))) = k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X3))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_11,c_1106]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74848,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,sK5) = k2_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_183]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_75232,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK5),X0) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_74848,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74844,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_1232]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_75271,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK3,sK5),X0) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_75232,c_74844]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_89861,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X1),sK5),X1))) = k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,X1))) ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_89815,c_26730,c_48560,c_75271]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_128876,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(X0,X1)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_128875,c_89861]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_128905,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK5,k2_xboole_0(sK4,X1))),k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,X1))) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_128413,c_128876]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_76004,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(X0,sK5)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_74834,c_275]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_5429,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1228,c_1877]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_5554,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK4,sK5)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_5429,c_5503]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_4239,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,X0)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1228,c_1634]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1590,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_275,c_1228]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_4304,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_4239,c_1590]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_5555,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_5554,c_183,c_4304]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74818,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_5555]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_84698,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,sK5)),k2_xboole_0(sK3,sK5)),k2_xboole_0(sK5,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,sK5)),k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1055,c_74818]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_26855,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X3,X2)) = k2_xboole_0(X3,k2_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1055,c_277]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_5430,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(sK5,X0)) = k2_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1232,c_1877]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_5552,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK4,sK5)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_5430,c_5503]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_4240,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(sK5,X0)) = k2_xboole_0(sK4,k2_xboole_0(sK5,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1232,c_1634]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_4303,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(sK5,X0)) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_4240,c_1590]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_5553,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_5552,c_183,c_4303]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74819,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,X0)),k2_xboole_0(sK5,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_5553]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_76050,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),X1) = k2_xboole_0(sK5,k2_xboole_0(k2_xboole_0(sK4,X0),X1)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_74834,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2997,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(k2_xboole_0(sK4,X0),X1)) = k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2464,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1392,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),X1) = k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1228,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3015,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(k2_xboole_0(sK4,X0),X1)) = k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_2997,c_1392]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_76110,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),X1) = k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK5,X0),X1)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_76050,c_3015]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1589,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK5,X1))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_275,c_1232]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_76111,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),X1) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X0,X1))) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_76110,c_1589,c_9561]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_76112,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),X1) = k2_xboole_0(sK3,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_76111,c_74573]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_84845,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_84698,c_26855,c_74819,c_76112]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_128906,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,k2_xboole_0(X1,sK5))))) = k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,X1))) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_128905,c_76004,c_84845]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_128907,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,X1)))) = k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(X0,X1))) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_128906,c_26730]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_141558,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(sK5,X0))),k4_xboole_0(sK5,k2_xboole_0(sK4,sK3))) = k2_xboole_0(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_141411,c_59668,c_114776,c_128907,c_129547]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_141559,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,k4_xboole_0(sK5,X0))),k4_xboole_0(sK5,k2_xboole_0(sK3,sK4))) = k2_xboole_0(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_141558,c_21126]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74773,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK4),sK5) = k2_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_19213]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_75611,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(sK3,sK4)) = k2_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_74773,c_0]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_76475,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(sK5,k2_xboole_0(sK3,sK4))) = k2_xboole_0(sK3,sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_75611,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_141560,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) = k2_xboole_0(sK3,sK4) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_141559,c_1747,c_76475]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_141588,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,sK4) = sK4 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_141587,c_141560]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24206,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_183,c_1054]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2113,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1485,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2114,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_2113,c_626]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24268,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(k4_xboole_0(sK5,sK4),k4_xboole_0(X0,sK4))) = k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2114,c_1054]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24635,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(X0,sK4))))) = k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_24268,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19429,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X1,X2),X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_11,c_19100]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24636,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_24635,c_11,c_19100,c_19429]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24689,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_24206,c_24636]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_64879,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,sK4),sK5),k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4))) = k4_xboole_0(X0,sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_24689,c_917]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_64914,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK4,sK5)),k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4))) = k4_xboole_0(X0,sK4) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_64879,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_64915,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4))) = k4_xboole_0(X0,sK4) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_64914,c_183]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_64997,plain,
% 47.61/6.49      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)),sK4))) = k4_xboole_0(k2_xboole_0(sK3,sK4),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_8954,c_64915]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_65171,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,sK4)),sK4))) = k4_xboole_0(k2_xboole_0(sK3,sK4),sK4) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_64997,c_29062]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19039,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k2_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_11,c_936]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2482,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK2,k4_xboole_0(sK5,X0)),k2_xboole_0(sK3,X1)) = k2_xboole_0(X1,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1784,c_276]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_11747,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))),sK5) = k4_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK3,sK2)),sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2482,c_2995]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1626,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK2,sK5),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1257,c_547]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2898,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,sK5),k2_xboole_0(sK3,sK2)),k1_xboole_0) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1626,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2478,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK2,sK5),k2_xboole_0(sK3,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1257,c_276]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2910,plain,
% 47.61/6.49      ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_2898,c_9,c_2478]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_11763,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))),sK5) = k4_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_11747,c_612,c_2910]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19075,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))),sK5) = k2_xboole_0(k4_xboole_0(sK4,sK5),sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_11763,c_936]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19205,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))),sK5) = k2_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_19075,c_936]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19206,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK2,k4_xboole_0(sK5,X0))),sK5) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_19205,c_183]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_22698,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK5,X0),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_19206,c_9104]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_30452,plain,
% 47.61/6.49      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK5,X0),X0)) = k4_xboole_0(k4_xboole_0(sK5,X0),X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_22698,c_1063]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_30859,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(k4_xboole_0(sK5,X0),X0)) = k4_xboole_0(k4_xboole_0(sK5,X0),X0) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_30452,c_29062]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_30860,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK5,X0)) = k4_xboole_0(sK5,X0) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_30859,c_2584]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_65172,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK3),sK4)) = k4_xboole_0(sK3,sK4) ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_65171,c_10,c_19039,c_30860]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_21502,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_609,c_1038]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_21833,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k4_xboole_0(X0,X2) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_21502,c_9,c_108]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_150888,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),sK4),sK5),k2_xboole_0(k4_xboole_0(sK3,sK4),X0)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),sK4),X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_65172,c_21833]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2858,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(k2_xboole_0(X0,X1),X2)) = X2 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_12,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_141729,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)),X0)),k4_xboole_0(sK4,X0)) = X0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_141587,c_2858]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_141745,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k4_xboole_0(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)))) = k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_141587,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_141750,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_141587,c_10]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2883,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2922,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_2883,c_1747]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74847,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK5),sK5) = k4_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_612]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74849,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,sK5) = k4_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74847,c_10]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_141863,plain,
% 47.61/6.49      ( k4_xboole_0(sK3,k4_xboole_0(sK5,k4_xboole_0(sK5,sK4))) = k4_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_141750,c_2922,c_74849]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_141865,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK5,k4_xboole_0(sK5,sK4)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_141745,c_141863]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_142434,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK3,sK5)),X0)),k4_xboole_0(sK4,X0)) = X0 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_141729,c_141865]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_17632,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)),k4_xboole_0(X0,X2)) = k2_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2711,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3690,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_8,c_277]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_17668,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X2,X1),X0) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_17632,c_3690]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1089,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_8,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1115,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_1089,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1774,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1747,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_61860,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),k2_xboole_0(X1,X3))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1115,c_1774]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2466,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(X2,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_931,c_276]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_62041,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X2)),X3)) = k2_xboole_0(X3,k2_xboole_0(X1,X0)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_61860,c_2466,c_9561]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_142435,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK3,sK4),X0) = X0 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_142434,c_17668,c_62041]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_151215,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),sK4),sK5),X0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),sK4),X0) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_150888,c_142435]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2463,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_14,c_276]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_99343,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X1,X0),X2),X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_917,c_2463]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_11930,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X1,X0),X2)) = k2_xboole_0(X2,X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_917,c_276]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_99663,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),X0) = k2_xboole_0(X2,X0) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_99343,c_11930]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_151216,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),sK4),X0) = k4_xboole_0(k2_xboole_0(sK4,sK5),X0) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_151215,c_99663]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_151217,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),sK4),X0) = k4_xboole_0(k2_xboole_0(sK3,sK5),X0) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_151216,c_74848]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_65008,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) = k4_xboole_0(X0,sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_0,c_64915]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_96661,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) = k4_xboole_0(X0,sK4) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_65008,c_65008,c_74573]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_152730,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,sK3),sK4))))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK5,sK3),sK4),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_151217,c_96661]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19069,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK4,sK3),sK5) = k2_xboole_0(k4_xboole_0(sK4,sK5),sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_7193,c_936]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19214,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK4,sK3),sK5) = k2_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_19069,c_936]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19215,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK4,sK3),sK5) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_19214,c_183]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_20038,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_19215,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_20665,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK5),sK4) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_20038,c_609]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_20730,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK5),sK4) = k4_xboole_0(sK5,sK4) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_20665,c_1485]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29276,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sP0_iProver_split)) = k2_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27778,c_1232]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29280,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK2,sP0_iProver_split)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_29276,c_183]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_5843,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,X0)),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_5553,c_108]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29605,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sP0_iProver_split,k2_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_29280,c_5843]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29614,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = sP0_iProver_split ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_29605,c_29062,c_29281]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74736,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(sK3,sK5)) = sP0_iProver_split ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_29614]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1233,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(k2_xboole_0(sK3,sK2),X0))) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1091,c_14]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_11233,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(sK5,k2_xboole_0(sK4,X0)))) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_1233,c_1233,c_1483,c_3787]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_4463,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK4,X1))) = k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(X1,X0))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_277,c_3787]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1568,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_626,c_275]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_4954,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_277,c_1568]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_11234,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,sK5),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_11233,c_1590,c_4463,c_4954]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27680,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK2,sK5),sK4)) = k2_xboole_0(sK5,k1_xboole_0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1626,c_26732]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_26691,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_609,c_1055]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27131,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_26691,c_1055]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3793,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = k4_xboole_0(k2_xboole_0(X2,X0),X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_277,c_609]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27132,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_27131,c_3793,c_9561]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27769,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK2,sK5),sK4)) = sK5 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_27680,c_6,c_27132]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_31053,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK5,sK2),sK4)) = sK5 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_0,c_27769]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_35314,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK5,sK2),sK4),X0),k2_xboole_0(X0,sK5)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_31053,c_9104]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_35343,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK5,sK2),sK4),X0),k2_xboole_0(X0,sK5)) = sP0_iProver_split ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_35314,c_29062]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_17597,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2698,c_2711]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_17684,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X3)) = k4_xboole_0(X0,k2_xboole_0(X2,k2_xboole_0(X1,X3))) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_17597,c_11,c_9561]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_35344,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(X0,k2_xboole_0(sK4,sK5))) = sP0_iProver_split ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_35343,c_11,c_17684,c_17687]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_35345,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = sP0_iProver_split ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_35344,c_183]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_35612,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK2),k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = sP0_iProver_split ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_11234,c_35345]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_36055,plain,
% 47.61/6.49      ( k4_xboole_0(X0,sP0_iProver_split) = X0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_35612,c_7586]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_152722,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK5),sP0_iProver_split) = k2_xboole_0(k4_xboole_0(sK5,sK3),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_151217,c_36055]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74846,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_626]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_75708,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK5),k4_xboole_0(sK4,k2_xboole_0(sK3,sK5))) = k2_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_74846,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74730,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k2_xboole_0(sK3,sK5)) = sP0_iProver_split ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_32019]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_75762,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK5),sP0_iProver_split) = k2_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_75708,c_74730]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_152833,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK5,sK3),sK4) = k2_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_152722,c_75762]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_153680,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK3,sK4)))) = k4_xboole_0(sK5,sK4) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_152730,c_20730,c_65172,c_74736,c_152833]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_37731,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK4),X0),sK5) = k2_xboole_0(k4_xboole_0(sK2,sK4),sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27761,c_14682]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29407,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK2,sK4),sK5) = k2_xboole_0(sK5,k4_xboole_0(sK2,sK4)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27761,c_1877]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29455,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK2,sK4),sK5) = sK5 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_29407,c_27761]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_37941,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK4),X0),sK5) = sK5 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_37731,c_29455]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_37942,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK2,k2_xboole_0(sK4,X0)),sK5) = sK5 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_37941,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1041,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_10,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1072,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_1041,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_40005,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK2,k2_xboole_0(sK4,X0)),k2_xboole_0(sK5,X1)) = k4_xboole_0(sK5,k2_xboole_0(sK5,X1)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_37942,c_1072]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1099,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_12,c_108]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29244,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(sK5,k2_xboole_0(sP0_iProver_split,X0))) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27778,c_1099]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29252,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(sP0_iProver_split,X0)) = k2_xboole_0(sK5,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27778,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29302,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(sK5,X0)) = k1_xboole_0 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_29244,c_29252]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29303,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(sK5,X0)) = sP0_iProver_split ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_29302,c_29062]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_40070,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK2,k2_xboole_0(sK4,X0)),k2_xboole_0(sK5,X1)) = sP0_iProver_split ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_40005,c_11,c_29303]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_85107,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK4,X0)),k2_xboole_0(sK5,X1)) = sP0_iProver_split ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_40070,c_40070,c_74573]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_85199,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK5,k2_xboole_0(sK4,X0))) = k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_85107,c_931]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2994,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(sK4,X0))) = k2_xboole_0(sK4,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2464,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_13915,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK4,k1_xboole_0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_6,c_2994]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_13984,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(sK5,sK4)) = sK4 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_13915,c_6,c_2461]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19078,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK4,k4_xboole_0(sK5,sK4)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_13984,c_936]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19201,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK5,sK4) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_19078,c_19100]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_14087,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,sK2)),sK4) = k4_xboole_0(sK5,k2_xboole_0(sK4,k1_xboole_0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_6,c_2999]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2558,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK4) = k4_xboole_0(k2_xboole_0(sK5,X0),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1228,c_609]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_14164,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK2,sK3),sK4) = k4_xboole_0(sK5,sK4) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_14087,c_6,c_2461,c_2558]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_14258,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK2,sK3) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_14164,c_1747]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_19202,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(sK5,sK4)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_19201,c_1400,c_14258]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_21059,plain,
% 47.61/6.49      ( k2_xboole_0(sK2,k2_xboole_0(sK3,k4_xboole_0(sK5,sK4))) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_19202,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_56267,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(sK5,sK4)),sK2) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_21059,c_609]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_56345,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(sK5,sK4)),sK2) = k4_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_56267,c_10]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_87423,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k4_xboole_0(sK5,sK4)),sK5) = k4_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_56345,c_56345,c_74573]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_150923,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,k2_xboole_0(sK3,k4_xboole_0(sK5,sK4))),k2_xboole_0(k4_xboole_0(sK3,sK5),X0)) = k4_xboole_0(sK5,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_87423,c_21833]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74680,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(sK3,k4_xboole_0(sK5,sK4))) = k2_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_21059]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74842,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,sK5) = k2_xboole_0(sK5,sK4) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_1400]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_75318,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_74842,c_1072]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_145803,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k4_xboole_0(sK3,sK5)) = sP0_iProver_split ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_10469,c_10469,c_29062,c_74573,c_74849]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_14217,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(k4_xboole_0(sK5,sK4),X0)) = k4_xboole_0(sK4,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_13984,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_142046,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(k4_xboole_0(sK5,sK4),X0)) = k4_xboole_0(sK4,X0) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_14217,c_14217,c_74573]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_142073,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK4,sK5))) = k4_xboole_0(k2_xboole_0(sK5,sK3),sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_917,c_142046]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_142320,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,sK5))) = k4_xboole_0(k2_xboole_0(sK5,sK3),sK5) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_142073,c_74849]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24213,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,sK5))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1400,c_1054]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1486,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1400,c_108]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_715,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = k4_xboole_0(sK5,k4_xboole_0(sK5,k2_xboole_0(sK3,sK2))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_612,c_1]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1491,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = k4_xboole_0(sK5,k1_xboole_0) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_1486,c_715]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1492,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k4_xboole_0(sK4,sK5)) = sK5 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_1491,c_9]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3971,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK2),sK5)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1492,c_184]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3976,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(sK4,sK5)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_3971,c_612]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24221,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(k4_xboole_0(sK4,sK5),k4_xboole_0(X0,sK5))) = k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_3976,c_1054]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24670,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(sK4,k2_xboole_0(sK5,k4_xboole_0(X0,sK5))))) = k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_24221,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24671,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK5),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,X0),sK5)) ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_24670,c_11,c_19100,c_19429]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_24685,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK4,X0),sK5)) = k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(X0,sK5))) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_24213,c_24671]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1763,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1,c_1747]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1388,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1228,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_92580,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK5))) = k2_xboole_0(sK4,k2_xboole_0(sK5,k2_xboole_0(X0,X1))) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_1388,c_74573]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_92849,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK5))),k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(sK4,sK5),k2_xboole_0(X0,X1)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_92580,c_1098]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_92886,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK5))),k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(X0,X1)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_92849,c_74848]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_112613,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k2_xboole_0(sK3,sK5))),X0) = k4_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1763,c_92886]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_112961,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k2_xboole_0(sK3,sK5))),X0) = k4_xboole_0(k2_xboole_0(sK3,sK5),X0) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_112613,c_1763]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_5337,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k2_xboole_0(X0,X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1763,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42012,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X0) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_276,c_1098]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_112962,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK3),X0) = k4_xboole_0(k2_xboole_0(sK3,sK5),X0) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_112961,c_5337,c_42012]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_142321,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK3,sK5))) = k4_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_142320,c_10,c_24685,c_112962]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_145804,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,sP0_iProver_split) = k4_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_145803,c_142321]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_30435,plain,
% 47.61/6.49      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK4,X0),X0)) = k4_xboole_0(k2_xboole_0(sK4,X0),X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_3003,c_1063]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_30885,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(k2_xboole_0(sK4,X0),X0)) = k4_xboole_0(k2_xboole_0(sK4,X0),X0) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_30435,c_29062]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_30886,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK4,X0)) = k4_xboole_0(sK4,X0) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_30885,c_10]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_34389,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,sP0_iProver_split) = k2_xboole_0(sP0_iProver_split,sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_30886,c_8]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_32038,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,sK4) = sK4 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_31824,c_931]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_34414,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,sP0_iProver_split) = sK4 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_34389,c_32038]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_145805,plain,
% 47.61/6.49      ( k4_xboole_0(sK3,sK5) = sK4 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_145804,c_34414]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_151166,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,X0) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_150923,c_74680,c_75318,c_145805]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_153681,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK5,sK4) ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_153680,c_30860,c_85199,c_151166]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29259,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,sK5) = sK5 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27778,c_0]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29356,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k4_xboole_0(sP0_iProver_split,sK5)) = sK5 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_29259,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29258,plain,
% 47.61/6.49      ( k4_xboole_0(sP0_iProver_split,sK5) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27778,c_547]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29292,plain,
% 47.61/6.49      ( k4_xboole_0(sP0_iProver_split,sK5) = sP0_iProver_split ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_29258,c_29062]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_29388,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,sP0_iProver_split) = sK5 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_29356,c_29292]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_141751,plain,
% 47.61/6.49      ( k4_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_141587,c_108]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_142404,plain,
% 47.61/6.49      ( k4_xboole_0(sK3,sK4) = sP0_iProver_split ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_141751,c_29062]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_153682,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,sK4) = sK5 ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_153681,c_29388,c_142404]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_161568,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK5,k2_xboole_0(sK3,sK4))) = sK5 ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_30864,c_30864,c_58941,c_141588,c_153682]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_30451,plain,
% 47.61/6.49      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK5,sK3),sK3)) = k4_xboole_0(k4_xboole_0(sK5,sK3),sK3) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_22542,c_1063]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_30861,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(k4_xboole_0(sK5,sK3),sK3)) = k4_xboole_0(k4_xboole_0(sK5,sK3),sK3) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_30451,c_29062]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_30862,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK5,sK3)) = k4_xboole_0(sK5,sK3) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_30861,c_2584]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_37726,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK5,sK3),X0),sK2) = k2_xboole_0(k4_xboole_0(sK5,sK3),sK2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27092,c_14682]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27416,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK5,sK3),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK5,sK3)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27092,c_1877]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27459,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK5,sK3),sK2) = sK2 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_27416,c_27092]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_37951,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK5,sK3),X0),sK2) = sK2 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_37726,c_27459]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_37952,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,X0)),sK2) = sK2 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_37951,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42818,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,X0)),k2_xboole_0(sK2,X1)) = k4_xboole_0(sK2,k2_xboole_0(sK2,X1)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_37952,c_1072]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42679,plain,
% 47.61/6.49      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK3,X0)),k2_xboole_0(sK2,X1))) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_37950,c_1099]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42686,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK4,k2_xboole_0(sK3,X0)),k2_xboole_0(sK2,X1)) = k2_xboole_0(sK2,X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_37950,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42736,plain,
% 47.61/6.49      ( k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k1_xboole_0 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_42679,c_42686]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42737,plain,
% 47.61/6.49      ( k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = sP0_iProver_split ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_42736,c_29062]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42880,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,X0)),k2_xboole_0(sK2,X1)) = sP0_iProver_split ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_42818,c_11,c_42737]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_86104,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK3,X0)),k2_xboole_0(sK5,X1)) = sP0_iProver_split ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_42880,c_42880,c_74573]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_86192,plain,
% 47.61/6.49      ( k2_xboole_0(sP0_iProver_split,k4_xboole_0(sK5,k2_xboole_0(sK3,X0))) = k4_xboole_0(sK5,k2_xboole_0(sK3,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_86104,c_931]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27684,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK4),sK4)) = k2_xboole_0(sK5,k1_xboole_0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_8954,c_26732]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_27765,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(sK3,sK4)) = sK5 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_27684,c_6,c_10]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_48544,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(sK5,sK3)) = k2_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_27765,c_1106]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_49106,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(sK5,sK3)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_48544,c_183]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_50607,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK3),sK4) = k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_49106,c_609]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_50697,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK3),sK4) = k4_xboole_0(sK5,sK4) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_50607,c_1485]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_160029,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK3),sK4) = sK5 ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_50697,c_50697,c_153682]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_160073,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_160029,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_161209,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK4,X0)) = k4_xboole_0(sK5,k2_xboole_0(X0,sK4)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_616,c_160073]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_161499,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(X0,sK4)) = k4_xboole_0(sK5,X0) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_161209,c_160073]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_161569,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,sK3) = sK5 ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_161568,c_30862,c_86192,c_161499]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_65026,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK5),X1),k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X1),sK4))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK5),X1),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2711,c_64915]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3735,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_8,c_277]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42289,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),sK4)) = k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK2))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1098,c_26732]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_42311,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),sK4)) = k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,X1),sK4)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_42289,c_26732]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_65024,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(k1_xboole_0,sK4))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_3000,c_64915]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1379,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(X0,sK5)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_0,c_1228]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_14330,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),sK4) = k4_xboole_0(k2_xboole_0(X0,sK5),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1379,c_609]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_65135,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,sK4)) = k4_xboole_0(k2_xboole_0(X0,sK5),sK4) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_65024,c_14330,c_29062,c_32038]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_65136,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,sK4)) = k4_xboole_0(k2_xboole_0(X0,sK5),sK4) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_65135,c_10]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3126,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2)))) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_12,c_3000]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_65027,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,k2_xboole_0(k1_xboole_0,sK4))) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_3126,c_64915]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_65130,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,sK4)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),sK4) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_65027,c_29062,c_32038]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_65131,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK2)),k4_xboole_0(sK5,sK4)) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))),sK4) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_65130,c_2553]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_65137,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),sK4) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X1,X0),sK5),sK4) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_65136,c_65131]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_65138,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(sK3,sK2))),sK4) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK5)),sK4) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_65137,c_9561]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_102576,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK5)),sK4)) = k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,X1),sK4)) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_42311,c_42311,c_65138]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74748,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k2_xboole_0(sK5,k4_xboole_0(X0,sK4)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_26732]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_77334,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(X0,sK3)) = k2_xboole_0(sK5,k4_xboole_0(X0,sK4)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_74748,c_1055]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_102577,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK5)),sK4)) = k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,X1),sK3)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_102576,c_77334]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_102658,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(X0,X1),sK3)),sK5) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK5)),sK4),sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_102577,c_609]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7642,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))),X0) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2698,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7660,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),X0) = k4_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_7642,c_1055]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_102794,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK5)),k2_xboole_0(sK3,sK5)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_102658,c_11,c_7660,c_74848]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_116051,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK5),X1),k2_xboole_0(sK3,sK5)) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(sK5,X0)),k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_3735,c_102794]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_103027,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK5,X1)),k2_xboole_0(sK3,sK5)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,sK5)),k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1877,c_102794]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_103165,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK5,X1)),k2_xboole_0(sK3,sK5)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_103027,c_102794]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_116149,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK5),X1),k2_xboole_0(sK3,sK5)) = k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_116051,c_103165]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_138071,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK5),X0),sK4) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_65026,c_65026,c_74573,c_116149]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_96725,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0))),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_96661,c_609]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_75245,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k4_xboole_0(sK5,k4_xboole_0(sK5,k4_xboole_0(X0,sK4))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_74848,c_1054]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_75265,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_75245,c_24689]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_96801,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0))),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_96725,c_75265]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_22121,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X3,X0))) = k4_xboole_0(X0,X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1747,c_7586]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_96802,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0))) = k4_xboole_0(sK5,k2_xboole_0(k4_xboole_0(sK5,X0),sK4)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_96801,c_22121]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_138072,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK5),X0),sK4) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_138071,c_96802]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_161637,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK3,X0),k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(sK4,sK5))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK5),sK3),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_161569,c_138072]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74841,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK5)) = k1_xboole_0 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_1486]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74850,plain,
% 47.61/6.49      ( k4_xboole_0(sK5,k2_xboole_0(sK3,sK5)) = sP0_iProver_split ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_74841,c_29062]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1900,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_555,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1914,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_1900,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_50617,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,sK3)) = k4_xboole_0(k2_xboole_0(X0,sK4),k2_xboole_0(sK5,sK3)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_49106,c_1098]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_50623,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK4,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_49106,c_276]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_51565,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK2)),k2_xboole_0(sK5,sK3)) = k4_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(sK5,sK3)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_50623,c_609]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74688,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(sK5,sK3)) = k2_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_49106]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_75416,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),k2_xboole_0(sK5,sK3)) = k4_xboole_0(k2_xboole_0(X0,sK4),k2_xboole_0(sK5,sK3)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_74688,c_1098]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_36470,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1877,c_1072]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_36804,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_36470,c_1877]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_75456,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,sK4),k2_xboole_0(sK5,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK5,sK3)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_75416,c_36804]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_76027,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k2_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_74834,c_2711]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_17558,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X3,X0)))) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_276,c_2711]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74824,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK5,X0)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_3787]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_76138,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) = k4_xboole_0(X0,k2_xboole_0(sK5,sK3)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_76027,c_17558,c_74824]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_88803,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK3,sK5)),k2_xboole_0(sK5,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_50617,c_51565,c_74573,c_75456,c_76138]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_97233,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK5)),k2_xboole_0(sK5,sK3)) = k4_xboole_0(k2_xboole_0(sK3,X0),k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1914,c_88803]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_88830,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,k2_xboole_0(sK4,X0)),k2_xboole_0(sK5,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_74834,c_88803]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_88949,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK5)),k2_xboole_0(sK5,sK3)) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_88830,c_76004]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_97269,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,X0),k2_xboole_0(sK3,sK5)) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_97233,c_88949]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_96729,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) = k4_xboole_0(k4_xboole_0(X0,sK4),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_96661,c_10]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_48690,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X0)))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X3,X0),k2_xboole_0(X1,X2))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1106,c_2711]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_48860,plain,
% 47.61/6.49      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,X0)))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_48690,c_2711]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_96797,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) = k4_xboole_0(X0,k2_xboole_0(sK4,sK5)) ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_96729,c_11,c_27018,c_48860]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_96798,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(sK5,k2_xboole_0(sK4,k4_xboole_0(sK5,X0)))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_96797,c_74848]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_113299,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(X0,k2_xboole_0(sK3,sK5)))) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_96798,c_184]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3751,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK4,X0),k2_xboole_0(X1,sK5)) = k2_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2464,c_277]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_16444,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK4,sK5),k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK3,sK2))),sK5)) = k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_3751,c_5553]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_778,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = k2_xboole_0(k2_xboole_0(sK3,sK2),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_677,c_14]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_782,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_778,c_677]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3101,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK5) = k2_xboole_0(sK5,k2_xboole_0(sK4,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2992,c_555]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3118,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK5) = k2_xboole_0(sK2,sK3) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_3101,c_2992]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_12328,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK4),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2992,c_1099]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_12467,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_12328,c_1400]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_12794,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK3)),k1_xboole_0) = k2_xboole_0(sK2,sK3) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_12467,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2888,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),k1_xboole_0) = k2_xboole_0(X0,X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_108,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2470,plain,
% 47.61/6.49      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_554,c_276]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2919,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_2888,c_2470]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3139,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_3000,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2998,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2464,c_14]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1480,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_1400,c_718]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2095,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1480,c_275]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2366,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK5,sK4),X0)) = k2_xboole_0(k2_xboole_0(sK3,sK2),X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2114,c_12]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2375,plain,
% 47.61/6.49      ( k2_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK5,sK4),X0)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_2366,c_1483]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2376,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k2_xboole_0(sK5,k2_xboole_0(sK4,X0)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_2375,c_1115,c_1590]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3014,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK3,k2_xboole_0(X0,sK2)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_2998,c_2095,c_2376]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_3151,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK2)),k1_xboole_0) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_3139,c_3014]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_8776,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_2910,c_276]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_12816,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK2,sK3) ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_12794,c_2919,c_3151,c_8776]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_16445,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_16444,c_183,c_782,c_2910,c_3118,c_12816]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74779,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK5),k2_xboole_0(sK5,sK3)) = k2_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_16445]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_75804,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK3),k4_xboole_0(k2_xboole_0(sK5,sK3),k4_xboole_0(X0,k2_xboole_0(sK3,sK5)))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_74779,c_1054]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_50605,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,sK3)) = k2_xboole_0(sK4,k2_xboole_0(sK5,sK3)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_49106,c_1634]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_50698,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,sK2),k2_xboole_0(sK5,sK3)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_50605,c_49106]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_51193,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK3),k4_xboole_0(k2_xboole_0(sK5,sK3),k4_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK2)),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_50698,c_1054]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7636,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,X0),k4_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK3,sK2)))) = k2_xboole_0(sK5,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_5555,c_2698]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_46954,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK3),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK5,sK3) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_14,c_7636]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_51231,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK5,sK3)) = sP0_iProver_split ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_51193,c_24631,c_46954]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_17943,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(X0,k2_xboole_0(sK3,sK2))) = k2_xboole_0(sK2,sK3) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_16445,c_2698]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_74778,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK3),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k2_xboole_0(sK5,sK3) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_74573,c_17943]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_75849,plain,
% 47.61/6.49      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = sP0_iProver_split ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_75804,c_51231,c_74778]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_113324,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(sK3,sK5)),sP0_iProver_split) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_113299,c_75849]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_161666,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK5),sK3),sK4) = k4_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_161637,c_74848,c_74850,c_97269,c_113324]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_162090,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK5),sK3),k4_xboole_0(X0,k2_xboole_0(sK3,sK5))) = k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(X0,sK5),sK3))) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_161666,c_1]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_2887,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X1,X2))) = X2 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_11,c_672]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_109769,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2),k4_xboole_0(X0,k2_xboole_0(X2,X1))) = X2 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1877,c_2887]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_109975,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(X0,k2_xboole_0(X2,X1))) = X2 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_109769,c_19039]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_75250,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_74848,c_1742]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_75263,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_75250,c_74848]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_102621,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK3),sK3)) = k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(sK3,sK5),sK4)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_75263,c_102577]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_102841,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(k2_xboole_0(k4_xboole_0(sK4,X0),sK3),sK3)) = k2_xboole_0(sK5,k4_xboole_0(sK5,sK4)) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_102621,c_20730]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_102842,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(k4_xboole_0(sK4,X0),sK3)) = sK5 ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_102841,c_10,c_1747,c_77334]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_102843,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k4_xboole_0(sK4,k2_xboole_0(X0,sK3))) = sK5 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_102842,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_156078,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,sK5),sK4) = sK5 ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_20730,c_20730,c_153682]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_156158,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK5,sK4)),sK5) = sK4 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_156078,c_2858]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7247,plain,
% 47.61/6.49      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(k2_xboole_0(sK4,X0),sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_3787,c_2461]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7378,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK4,X0),sK5) = k2_xboole_0(X0,k2_xboole_0(sK2,sK3)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_7247,c_7330]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_7383,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK4,X0),sK5) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_7382,c_7378]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_59527,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1)),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_21710,c_7383]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1731,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1,c_931]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_14710,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_1731,c_1742]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_14902,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),X1) = X1 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_14710,c_1731]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_14903,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)),X1) = X1 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_14902,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_50637,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(X0,sK4)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_49106,c_277]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_54799,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1)),k2_xboole_0(sK3,sK2)) = k2_xboole_0(k2_xboole_0(sK5,sK3),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_14903,c_50637]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_50613,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK3,sK2)) = k2_xboole_0(k2_xboole_0(sK5,sK3),sK4) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_49106,c_616]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_5849,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK5,X0),k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k2_xboole_0(X0,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_5553,c_0]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_44043,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,k2_xboole_0(sK3,sK2)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_616,c_5849]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_44195,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK2,sK3) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_44043,c_12816]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_50692,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK5,sK3),sK4) = k2_xboole_0(sK2,sK3) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_50613,c_44195]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_54830,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1)),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK2,sK3) ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_54799,c_50692]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_59592,plain,
% 47.61/6.49      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1)),k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_59527,c_183,c_54830]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_59965,plain,
% 47.61/6.49      ( k2_xboole_0(sK2,k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1)))) = k2_xboole_0(sK3,sK2) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_59592,c_276]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_81476,plain,
% 47.61/6.49      ( k2_xboole_0(sK5,k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1)))) = k2_xboole_0(sK3,sK5) ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_59965,c_59965,c_74573]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_84715,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1))),k2_xboole_0(sK3,sK5)),k2_xboole_0(sK3,sK5)) = k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1))),k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_81476,c_74818]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_75970,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK5,k2_xboole_0(sK4,X0)),k2_xboole_0(sK3,sK5)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_74834,c_1634]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_76176,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(X0,sK5)),k2_xboole_0(sK3,sK5)) = k2_xboole_0(X0,k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_75970,c_76004]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_81582,plain,
% 47.61/6.49      ( k2_xboole_0(k2_xboole_0(sK3,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK4),X1))),k2_xboole_0(X2,sK5)) = k2_xboole_0(X2,k2_xboole_0(sK3,sK5)) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_81476,c_277]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_84822,plain,
% 47.61/6.49      ( k2_xboole_0(sK3,k2_xboole_0(sK3,sK5)) = k2_xboole_0(sK5,sK3) ),
% 47.61/6.49      inference(demodulation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_84715,c_2470,c_76112,c_76176,c_81582]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_156172,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK3),sK5) = sK4 ),
% 47.61/6.49      inference(light_normalisation,
% 47.61/6.49                [status(thm)],
% 47.61/6.49                [c_156158,c_74842,c_84822]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_156301,plain,
% 47.61/6.49      ( k4_xboole_0(k2_xboole_0(sK5,sK3),k2_xboole_0(sK5,X0)) = k4_xboole_0(sK4,X0) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_156172,c_11]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_156528,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(X0,sK3))) = k4_xboole_0(k2_xboole_0(sK5,sK3),sK5) ),
% 47.61/6.49      inference(superposition,[status(thm)],[c_102843,c_156301]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_156743,plain,
% 47.61/6.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(X0,sK3))) = sK4 ),
% 47.61/6.49      inference(light_normalisation,[status(thm)],[c_156528,c_156172]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_162146,plain,
% 47.61/6.49      ( sK4 = sK3 ),
% 47.61/6.49      inference(demodulation,[status(thm)],[c_162090,c_109975,c_156743]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_186,plain,( X0 = X0 ),theory(equality) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_1186,plain,
% 47.61/6.49      ( sK3 = sK3 ),
% 47.61/6.49      inference(instantiation,[status(thm)],[c_186]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_187,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_281,plain,
% 47.61/6.49      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 47.61/6.49      inference(instantiation,[status(thm)],[c_187]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_492,plain,
% 47.61/6.49      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 47.61/6.49      inference(instantiation,[status(thm)],[c_281]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(c_16,negated_conjecture,
% 47.61/6.49      ( sK3 != sK4 ),
% 47.61/6.49      inference(cnf_transformation,[],[f52]) ).
% 47.61/6.49  
% 47.61/6.49  cnf(contradiction,plain,
% 47.61/6.49      ( $false ),
% 47.61/6.49      inference(minisat,[status(thm)],[c_162146,c_1186,c_492,c_16]) ).
% 47.61/6.49  
% 47.61/6.49  
% 47.61/6.49  % SZS output end CNFRefutation for theBenchmark.p
% 47.61/6.49  
% 47.61/6.49  ------                               Statistics
% 47.61/6.49  
% 47.61/6.49  ------ General
% 47.61/6.49  
% 47.61/6.49  abstr_ref_over_cycles:                  0
% 47.61/6.49  abstr_ref_under_cycles:                 0
% 47.61/6.49  gc_basic_clause_elim:                   0
% 47.61/6.49  forced_gc_time:                         0
% 47.61/6.49  parsing_time:                           0.008
% 47.61/6.49  unif_index_cands_time:                  0.
% 47.61/6.49  unif_index_add_time:                    0.
% 47.61/6.49  orderings_time:                         0.
% 47.61/6.49  out_proof_time:                         0.028
% 47.61/6.49  total_time:                             5.577
% 47.61/6.49  num_of_symbols:                         45
% 47.61/6.49  num_of_terms:                           300607
% 47.61/6.49  
% 47.61/6.49  ------ Preprocessing
% 47.61/6.49  
% 47.61/6.49  num_of_splits:                          0
% 47.61/6.49  num_of_split_atoms:                     2
% 47.61/6.49  num_of_reused_defs:                     0
% 47.61/6.49  num_eq_ax_congr_red:                    10
% 47.61/6.49  num_of_sem_filtered_clauses:            1
% 47.61/6.49  num_of_subtypes:                        0
% 47.61/6.49  monotx_restored_types:                  0
% 47.61/6.49  sat_num_of_epr_types:                   0
% 47.61/6.49  sat_num_of_non_cyclic_types:            0
% 47.61/6.49  sat_guarded_non_collapsed_types:        0
% 47.61/6.49  num_pure_diseq_elim:                    0
% 47.61/6.49  simp_replaced_by:                       0
% 47.61/6.49  res_preprocessed:                       85
% 47.61/6.49  prep_upred:                             0
% 47.61/6.49  prep_unflattend:                        8
% 47.61/6.49  smt_new_axioms:                         0
% 47.61/6.49  pred_elim_cands:                        1
% 47.61/6.49  pred_elim:                              2
% 47.61/6.49  pred_elim_cl:                           2
% 47.61/6.49  pred_elim_cycles:                       4
% 47.61/6.49  merged_defs:                            0
% 47.61/6.49  merged_defs_ncl:                        0
% 47.61/6.49  bin_hyper_res:                          0
% 47.61/6.49  prep_cycles:                            4
% 47.61/6.49  pred_elim_time:                         0.001
% 47.61/6.49  splitting_time:                         0.
% 47.61/6.49  sem_filter_time:                        0.
% 47.61/6.49  monotx_time:                            0.
% 47.61/6.49  subtype_inf_time:                       0.
% 47.61/6.49  
% 47.61/6.49  ------ Problem properties
% 47.61/6.49  
% 47.61/6.49  clauses:                                18
% 47.61/6.49  conjectures:                            2
% 47.61/6.49  epr:                                    1
% 47.61/6.49  horn:                                   17
% 47.61/6.49  ground:                                 2
% 47.61/6.49  unary:                                  16
% 47.61/6.49  binary:                                 2
% 47.61/6.49  lits:                                   20
% 47.61/6.49  lits_eq:                                15
% 47.61/6.49  fd_pure:                                0
% 47.61/6.49  fd_pseudo:                              0
% 47.61/6.49  fd_cond:                                1
% 47.61/6.49  fd_pseudo_cond:                         0
% 47.61/6.49  ac_symbols:                             1
% 47.61/6.49  
% 47.61/6.49  ------ Propositional Solver
% 47.61/6.49  
% 47.61/6.49  prop_solver_calls:                      38
% 47.61/6.49  prop_fast_solver_calls:                 1290
% 47.61/6.49  smt_solver_calls:                       0
% 47.61/6.49  smt_fast_solver_calls:                  0
% 47.61/6.49  prop_num_of_clauses:                    37073
% 47.61/6.49  prop_preprocess_simplified:             17913
% 47.61/6.49  prop_fo_subsumed:                       0
% 47.61/6.49  prop_solver_time:                       0.
% 47.61/6.49  smt_solver_time:                        0.
% 47.61/6.49  smt_fast_solver_time:                   0.
% 47.61/6.49  prop_fast_solver_time:                  0.
% 47.61/6.49  prop_unsat_core_time:                   0.003
% 47.61/6.49  
% 47.61/6.49  ------ QBF
% 47.61/6.49  
% 47.61/6.49  qbf_q_res:                              0
% 47.61/6.49  qbf_num_tautologies:                    0
% 47.61/6.49  qbf_prep_cycles:                        0
% 47.61/6.49  
% 47.61/6.49  ------ BMC1
% 47.61/6.49  
% 47.61/6.49  bmc1_current_bound:                     -1
% 47.61/6.49  bmc1_last_solved_bound:                 -1
% 47.61/6.49  bmc1_unsat_core_size:                   -1
% 47.61/6.49  bmc1_unsat_core_parents_size:           -1
% 47.61/6.49  bmc1_merge_next_fun:                    0
% 47.61/6.49  bmc1_unsat_core_clauses_time:           0.
% 47.61/6.49  
% 47.61/6.49  ------ Instantiation
% 47.61/6.49  
% 47.61/6.49  inst_num_of_clauses:                    4566
% 47.61/6.49  inst_num_in_passive:                    1483
% 47.61/6.49  inst_num_in_active:                     1946
% 47.61/6.49  inst_num_in_unprocessed:                1137
% 47.61/6.49  inst_num_of_loops:                      2790
% 47.61/6.49  inst_num_of_learning_restarts:          0
% 47.61/6.49  inst_num_moves_active_passive:          840
% 47.61/6.49  inst_lit_activity:                      0
% 47.61/6.49  inst_lit_activity_moves:                0
% 47.61/6.49  inst_num_tautologies:                   0
% 47.61/6.49  inst_num_prop_implied:                  0
% 47.61/6.49  inst_num_existing_simplified:           0
% 47.61/6.49  inst_num_eq_res_simplified:             0
% 47.61/6.49  inst_num_child_elim:                    0
% 47.61/6.49  inst_num_of_dismatching_blockings:      2964
% 47.61/6.49  inst_num_of_non_proper_insts:           5383
% 47.61/6.49  inst_num_of_duplicates:                 0
% 47.61/6.49  inst_inst_num_from_inst_to_res:         0
% 47.61/6.49  inst_dismatching_checking_time:         0.
% 47.61/6.49  
% 47.61/6.49  ------ Resolution
% 47.61/6.49  
% 47.61/6.49  res_num_of_clauses:                     0
% 47.61/6.49  res_num_in_passive:                     0
% 47.61/6.49  res_num_in_active:                      0
% 47.61/6.49  res_num_of_loops:                       89
% 47.61/6.49  res_forward_subset_subsumed:            1112
% 47.61/6.49  res_backward_subset_subsumed:           2
% 47.61/6.49  res_forward_subsumed:                   0
% 47.61/6.49  res_backward_subsumed:                  0
% 47.61/6.49  res_forward_subsumption_resolution:     0
% 47.61/6.49  res_backward_subsumption_resolution:    0
% 47.61/6.49  res_clause_to_clause_subsumption:       365607
% 47.61/6.49  res_orphan_elimination:                 0
% 47.61/6.49  res_tautology_del:                      520
% 47.61/6.49  res_num_eq_res_simplified:              0
% 47.61/6.49  res_num_sel_changes:                    0
% 47.61/6.49  res_moves_from_active_to_pass:          0
% 47.61/6.49  
% 47.61/6.49  ------ Superposition
% 47.61/6.49  
% 47.61/6.49  sup_time_total:                         0.
% 47.61/6.49  sup_time_generating:                    0.
% 47.61/6.49  sup_time_sim_full:                      0.
% 47.61/6.49  sup_time_sim_immed:                     0.
% 47.61/6.49  
% 47.61/6.49  sup_num_of_clauses:                     16147
% 47.61/6.49  sup_num_in_active:                      259
% 47.61/6.49  sup_num_in_passive:                     15888
% 47.61/6.49  sup_num_of_loops:                       556
% 47.61/6.49  sup_fw_superposition:                   35272
% 47.61/6.49  sup_bw_superposition:                   30660
% 47.61/6.49  sup_immediate_simplified:               44092
% 47.61/6.49  sup_given_eliminated:                   13
% 47.61/6.49  comparisons_done:                       0
% 47.61/6.49  comparisons_avoided:                    0
% 47.61/6.49  
% 47.61/6.49  ------ Simplifications
% 47.61/6.49  
% 47.61/6.49  
% 47.61/6.49  sim_fw_subset_subsumed:                 0
% 47.61/6.49  sim_bw_subset_subsumed:                 0
% 47.61/6.49  sim_fw_subsumed:                        4825
% 47.61/6.49  sim_bw_subsumed:                        349
% 47.61/6.49  sim_fw_subsumption_res:                 0
% 47.61/6.49  sim_bw_subsumption_res:                 0
% 47.61/6.49  sim_tautology_del:                      0
% 47.61/6.49  sim_eq_tautology_del:                   12220
% 47.61/6.49  sim_eq_res_simp:                        0
% 47.61/6.49  sim_fw_demodulated:                     33417
% 47.61/6.49  sim_bw_demodulated:                     806
% 47.61/6.49  sim_light_normalised:                   21310
% 47.61/6.49  sim_joinable_taut:                      1139
% 47.61/6.49  sim_joinable_simp:                      0
% 47.61/6.49  sim_ac_normalised:                      0
% 47.61/6.49  sim_smt_subsumption:                    0
% 47.61/6.49  
%------------------------------------------------------------------------------
