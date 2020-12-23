%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:06 EST 2020

% Result     : Theorem 47.94s
% Output     : CNFRefutation 47.94s
% Verified   : 
% Statistics : Number of formulae       :  154 (13215 expanded)
%              Number of clauses        :   92 (4828 expanded)
%              Number of leaves         :   20 (3068 expanded)
%              Depth                    :   34
%              Number of atoms          :  195 (20186 expanded)
%              Number of equality atoms :  144 (13077 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29])).

fof(f53,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f17])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f55])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f19,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f40,f36])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f41,f36,f36])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f39,f44,f44,f36])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f38,f36])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f42,f36,f36])).

fof(f54,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(definition_unfolding,[],[f54,f44,f36,f58,f58])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_469,plain,
    ( r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_471,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_473,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1817,plain,
    ( k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = k4_enumset1(X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_471,c_473])).

cnf(c_169116,plain,
    ( k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_469,c_1817])).

cnf(c_14,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_470,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_475,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4612,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_470,c_475])).

cnf(c_1818,plain,
    ( k3_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0))) = X0 ),
    inference(superposition,[status(thm)],[c_470,c_473])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_476,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1815,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_476,c_473])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_834,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_2574,plain,
    ( k5_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1815,c_834])).

cnf(c_4621,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4612,c_1818,c_2574])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2745,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_2574,c_11])).

cnf(c_3398,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2574,c_2745])).

cnf(c_3508,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3398,c_9])).

cnf(c_5364,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_4621,c_3508])).

cnf(c_5366,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4621,c_2574])).

cnf(c_5842,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5366,c_11])).

cnf(c_5365,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(demodulation,[status(thm)],[c_4621,c_2745])).

cnf(c_5378,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_5364,c_5365])).

cnf(c_6642,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5842,c_5378])).

cnf(c_5368,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_4621,c_9])).

cnf(c_6660,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_6642,c_5368])).

cnf(c_7198,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_6660,c_5378])).

cnf(c_6332,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_11,c_5378])).

cnf(c_6693,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0)) = X1 ),
    inference(superposition,[status(thm)],[c_5366,c_6332])).

cnf(c_6728,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(light_normalisation,[status(thm)],[c_6693,c_5368])).

cnf(c_7466,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
    inference(superposition,[status(thm)],[c_11,c_6728])).

cnf(c_8955,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X2,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_7198,c_7466])).

cnf(c_9105,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X0)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_8955,c_11])).

cnf(c_10495,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5364,c_9105])).

cnf(c_11478,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_10495,c_6728])).

cnf(c_11999,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)),k5_xboole_0(X1,X0)) = X2 ),
    inference(superposition,[status(thm)],[c_11478,c_7466])).

cnf(c_12067,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_11999,c_11478])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1204,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0)))),k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k3_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_11,c_8])).

cnf(c_7,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_472,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_837,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_472])).

cnf(c_1819,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_837,c_473])).

cnf(c_10,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_995,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))))) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_42540,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))))) = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X1) ),
    inference(superposition,[status(thm)],[c_1819,c_995])).

cnf(c_43866,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X1) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_42540,c_10,c_4621,c_5366,c_5368])).

cnf(c_47598,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X1))) ),
    inference(superposition,[status(thm)],[c_43866,c_10])).

cnf(c_47616,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_47598,c_10,c_5366])).

cnf(c_836,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_0])).

cnf(c_10110,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_836,c_5378])).

cnf(c_10155,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_10110,c_0])).

cnf(c_49372,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_47616,c_10155])).

cnf(c_52493,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_49372])).

cnf(c_62344,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0)))),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k3_xboole_0(X0,k5_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_1204,c_52493])).

cnf(c_12006,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_11478,c_11])).

cnf(c_12057,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_12006,c_11])).

cnf(c_33774,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k1_xboole_0) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_12057,c_6728])).

cnf(c_34063,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_33774,c_11])).

cnf(c_62345,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X0,X2),X1)))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),k3_xboole_0(X1,k5_xboole_0(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_62344,c_34063])).

cnf(c_6678,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),X2))) = X2 ),
    inference(superposition,[status(thm)],[c_5378,c_6332])).

cnf(c_62691,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X2)))))) = k3_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_62345,c_6678])).

cnf(c_6340,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = X2 ),
    inference(superposition,[status(thm)],[c_5378,c_11])).

cnf(c_6343,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
    inference(light_normalisation,[status(thm)],[c_6340,c_11])).

cnf(c_7151,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(k5_xboole_0(X3,X1),k5_xboole_0(X3,X2)) ),
    inference(superposition,[status(thm)],[c_6343,c_6332])).

cnf(c_7201,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_6660,c_6332])).

cnf(c_7247,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
    inference(demodulation,[status(thm)],[c_7151,c_7201])).

cnf(c_7558,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,X2),X0)) = X2 ),
    inference(superposition,[status(thm)],[c_7198,c_6332])).

cnf(c_62720,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,X2)) = k3_xboole_0(k5_xboole_0(X1,X2),X0) ),
    inference(demodulation,[status(thm)],[c_62691,c_7247,c_7558])).

cnf(c_103314,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),k5_xboole_0(X3,X2))) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_12067,c_62720])).

cnf(c_103893,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_103314,c_12067])).

cnf(c_176284,plain,
    ( k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_169116,c_103893])).

cnf(c_52549,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_49372,c_49372])).

cnf(c_52599,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_52549,c_5368])).

cnf(c_15,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_733,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(demodulation,[status(thm)],[c_11,c_15])).

cnf(c_750,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(superposition,[status(thm)],[c_11,c_733])).

cnf(c_7520,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(demodulation,[status(thm)],[c_7198,c_750])).

cnf(c_7920,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(superposition,[status(thm)],[c_11,c_7520])).

cnf(c_53435,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0))) != sK1 ),
    inference(demodulation,[status(thm)],[c_52599,c_7920])).

cnf(c_53441,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(demodulation,[status(thm)],[c_53435,c_5368])).

cnf(c_190605,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(demodulation,[status(thm)],[c_176284,c_53441])).

cnf(c_190608,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_190605,c_5366,c_5368])).

cnf(c_190609,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_190608])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:30:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 47.94/6.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.94/6.49  
% 47.94/6.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.94/6.49  
% 47.94/6.49  ------  iProver source info
% 47.94/6.49  
% 47.94/6.49  git: date: 2020-06-30 10:37:57 +0100
% 47.94/6.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.94/6.49  git: non_committed_changes: false
% 47.94/6.49  git: last_make_outside_of_git: false
% 47.94/6.49  
% 47.94/6.49  ------ 
% 47.94/6.49  ------ Parsing...
% 47.94/6.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.94/6.49  
% 47.94/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 47.94/6.49  
% 47.94/6.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.94/6.49  
% 47.94/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.94/6.49  ------ Proving...
% 47.94/6.49  ------ Problem Properties 
% 47.94/6.49  
% 47.94/6.49  
% 47.94/6.49  clauses                                 16
% 47.94/6.49  conjectures                             2
% 47.94/6.49  EPR                                     3
% 47.94/6.49  Horn                                    16
% 47.94/6.49  unary                                   11
% 47.94/6.49  binary                                  4
% 47.94/6.49  lits                                    22
% 47.94/6.49  lits eq                                 11
% 47.94/6.49  fd_pure                                 0
% 47.94/6.49  fd_pseudo                               0
% 47.94/6.49  fd_cond                                 0
% 47.94/6.49  fd_pseudo_cond                          1
% 47.94/6.49  AC symbols                              0
% 47.94/6.49  
% 47.94/6.49  ------ Input Options Time Limit: Unbounded
% 47.94/6.49  
% 47.94/6.49  
% 47.94/6.49  ------ 
% 47.94/6.49  Current options:
% 47.94/6.49  ------ 
% 47.94/6.49  
% 47.94/6.49  
% 47.94/6.49  
% 47.94/6.49  
% 47.94/6.49  ------ Proving...
% 47.94/6.49  
% 47.94/6.49  
% 47.94/6.49  % SZS status Theorem for theBenchmark.p
% 47.94/6.49  
% 47.94/6.49   Resolution empty clause
% 47.94/6.49  
% 47.94/6.49  % SZS output start CNFRefutation for theBenchmark.p
% 47.94/6.49  
% 47.94/6.49  fof(f20,conjecture,(
% 47.94/6.49    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f21,negated_conjecture,(
% 47.94/6.49    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 47.94/6.49    inference(negated_conjecture,[],[f20])).
% 47.94/6.49  
% 47.94/6.49  fof(f25,plain,(
% 47.94/6.49    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 47.94/6.49    inference(ennf_transformation,[],[f21])).
% 47.94/6.49  
% 47.94/6.49  fof(f29,plain,(
% 47.94/6.49    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1))),
% 47.94/6.49    introduced(choice_axiom,[])).
% 47.94/6.49  
% 47.94/6.49  fof(f30,plain,(
% 47.94/6.49    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1)),
% 47.94/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29])).
% 47.94/6.49  
% 47.94/6.49  fof(f53,plain,(
% 47.94/6.49    r2_hidden(sK0,sK1)),
% 47.94/6.49    inference(cnf_transformation,[],[f30])).
% 47.94/6.49  
% 47.94/6.49  fof(f17,axiom,(
% 47.94/6.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f22,plain,(
% 47.94/6.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 47.94/6.49    inference(unused_predicate_definition_removal,[],[f17])).
% 47.94/6.49  
% 47.94/6.49  fof(f24,plain,(
% 47.94/6.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 47.94/6.49    inference(ennf_transformation,[],[f22])).
% 47.94/6.49  
% 47.94/6.49  fof(f50,plain,(
% 47.94/6.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 47.94/6.49    inference(cnf_transformation,[],[f24])).
% 47.94/6.49  
% 47.94/6.49  fof(f12,axiom,(
% 47.94/6.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f45,plain,(
% 47.94/6.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 47.94/6.49    inference(cnf_transformation,[],[f12])).
% 47.94/6.49  
% 47.94/6.49  fof(f13,axiom,(
% 47.94/6.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f46,plain,(
% 47.94/6.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 47.94/6.49    inference(cnf_transformation,[],[f13])).
% 47.94/6.49  
% 47.94/6.49  fof(f14,axiom,(
% 47.94/6.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f47,plain,(
% 47.94/6.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 47.94/6.49    inference(cnf_transformation,[],[f14])).
% 47.94/6.49  
% 47.94/6.49  fof(f15,axiom,(
% 47.94/6.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f48,plain,(
% 47.94/6.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 47.94/6.49    inference(cnf_transformation,[],[f15])).
% 47.94/6.49  
% 47.94/6.49  fof(f16,axiom,(
% 47.94/6.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f49,plain,(
% 47.94/6.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 47.94/6.49    inference(cnf_transformation,[],[f16])).
% 47.94/6.49  
% 47.94/6.49  fof(f55,plain,(
% 47.94/6.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 47.94/6.49    inference(definition_unfolding,[],[f48,f49])).
% 47.94/6.49  
% 47.94/6.49  fof(f56,plain,(
% 47.94/6.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 47.94/6.49    inference(definition_unfolding,[],[f47,f55])).
% 47.94/6.49  
% 47.94/6.49  fof(f57,plain,(
% 47.94/6.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 47.94/6.49    inference(definition_unfolding,[],[f46,f56])).
% 47.94/6.49  
% 47.94/6.49  fof(f58,plain,(
% 47.94/6.49    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 47.94/6.49    inference(definition_unfolding,[],[f45,f57])).
% 47.94/6.49  
% 47.94/6.49  fof(f66,plain,(
% 47.94/6.49    ( ! [X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 47.94/6.49    inference(definition_unfolding,[],[f50,f58])).
% 47.94/6.49  
% 47.94/6.49  fof(f4,axiom,(
% 47.94/6.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f23,plain,(
% 47.94/6.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 47.94/6.49    inference(ennf_transformation,[],[f4])).
% 47.94/6.49  
% 47.94/6.49  fof(f37,plain,(
% 47.94/6.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 47.94/6.49    inference(cnf_transformation,[],[f23])).
% 47.94/6.49  
% 47.94/6.49  fof(f19,axiom,(
% 47.94/6.49    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f52,plain,(
% 47.94/6.49    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 47.94/6.49    inference(cnf_transformation,[],[f19])).
% 47.94/6.49  
% 47.94/6.49  fof(f2,axiom,(
% 47.94/6.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f28,plain,(
% 47.94/6.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 47.94/6.49    inference(nnf_transformation,[],[f2])).
% 47.94/6.49  
% 47.94/6.49  fof(f35,plain,(
% 47.94/6.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 47.94/6.49    inference(cnf_transformation,[],[f28])).
% 47.94/6.49  
% 47.94/6.49  fof(f3,axiom,(
% 47.94/6.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f36,plain,(
% 47.94/6.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 47.94/6.49    inference(cnf_transformation,[],[f3])).
% 47.94/6.49  
% 47.94/6.49  fof(f60,plain,(
% 47.94/6.49    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 47.94/6.49    inference(definition_unfolding,[],[f35,f36])).
% 47.94/6.49  
% 47.94/6.49  fof(f1,axiom,(
% 47.94/6.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f26,plain,(
% 47.94/6.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 47.94/6.49    inference(nnf_transformation,[],[f1])).
% 47.94/6.49  
% 47.94/6.49  fof(f27,plain,(
% 47.94/6.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 47.94/6.49    inference(flattening,[],[f26])).
% 47.94/6.49  
% 47.94/6.49  fof(f31,plain,(
% 47.94/6.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 47.94/6.49    inference(cnf_transformation,[],[f27])).
% 47.94/6.49  
% 47.94/6.49  fof(f70,plain,(
% 47.94/6.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 47.94/6.49    inference(equality_resolution,[],[f31])).
% 47.94/6.49  
% 47.94/6.49  fof(f7,axiom,(
% 47.94/6.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f40,plain,(
% 47.94/6.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 47.94/6.49    inference(cnf_transformation,[],[f7])).
% 47.94/6.49  
% 47.94/6.49  fof(f64,plain,(
% 47.94/6.49    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 47.94/6.49    inference(definition_unfolding,[],[f40,f36])).
% 47.94/6.49  
% 47.94/6.49  fof(f8,axiom,(
% 47.94/6.49    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f41,plain,(
% 47.94/6.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 47.94/6.49    inference(cnf_transformation,[],[f8])).
% 47.94/6.49  
% 47.94/6.49  fof(f59,plain,(
% 47.94/6.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 47.94/6.49    inference(definition_unfolding,[],[f41,f36,f36])).
% 47.94/6.49  
% 47.94/6.49  fof(f10,axiom,(
% 47.94/6.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f43,plain,(
% 47.94/6.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 47.94/6.49    inference(cnf_transformation,[],[f10])).
% 47.94/6.49  
% 47.94/6.49  fof(f6,axiom,(
% 47.94/6.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f39,plain,(
% 47.94/6.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 47.94/6.49    inference(cnf_transformation,[],[f6])).
% 47.94/6.49  
% 47.94/6.49  fof(f11,axiom,(
% 47.94/6.49    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f44,plain,(
% 47.94/6.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 47.94/6.49    inference(cnf_transformation,[],[f11])).
% 47.94/6.49  
% 47.94/6.49  fof(f63,plain,(
% 47.94/6.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 47.94/6.49    inference(definition_unfolding,[],[f39,f44,f44,f36])).
% 47.94/6.49  
% 47.94/6.49  fof(f5,axiom,(
% 47.94/6.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f38,plain,(
% 47.94/6.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 47.94/6.49    inference(cnf_transformation,[],[f5])).
% 47.94/6.49  
% 47.94/6.49  fof(f62,plain,(
% 47.94/6.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 47.94/6.49    inference(definition_unfolding,[],[f38,f36])).
% 47.94/6.49  
% 47.94/6.49  fof(f9,axiom,(
% 47.94/6.49    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 47.94/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.94/6.49  
% 47.94/6.49  fof(f42,plain,(
% 47.94/6.49    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 47.94/6.49    inference(cnf_transformation,[],[f9])).
% 47.94/6.49  
% 47.94/6.49  fof(f65,plain,(
% 47.94/6.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 47.94/6.49    inference(definition_unfolding,[],[f42,f36,f36])).
% 47.94/6.49  
% 47.94/6.49  fof(f54,plain,(
% 47.94/6.49    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1),
% 47.94/6.49    inference(cnf_transformation,[],[f30])).
% 47.94/6.49  
% 47.94/6.49  fof(f68,plain,(
% 47.94/6.49    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) != sK1),
% 47.94/6.49    inference(definition_unfolding,[],[f54,f44,f36,f58,f58])).
% 47.94/6.49  
% 47.94/6.49  cnf(c_16,negated_conjecture,
% 47.94/6.49      ( r2_hidden(sK0,sK1) ),
% 47.94/6.49      inference(cnf_transformation,[],[f53]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_469,plain,
% 47.94/6.49      ( r2_hidden(sK0,sK1) = iProver_top ),
% 47.94/6.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_12,plain,
% 47.94/6.49      ( ~ r2_hidden(X0,X1) | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) ),
% 47.94/6.49      inference(cnf_transformation,[],[f66]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_471,plain,
% 47.94/6.49      ( r2_hidden(X0,X1) != iProver_top
% 47.94/6.49      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 47.94/6.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_6,plain,
% 47.94/6.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 47.94/6.49      inference(cnf_transformation,[],[f37]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_473,plain,
% 47.94/6.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 47.94/6.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_1817,plain,
% 47.94/6.49      ( k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = k4_enumset1(X0,X0,X0,X0,X0,X0)
% 47.94/6.49      | r2_hidden(X0,X1) != iProver_top ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_471,c_473]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_169116,plain,
% 47.94/6.49      ( k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_469,c_1817]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_14,plain,
% 47.94/6.49      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
% 47.94/6.49      inference(cnf_transformation,[],[f52]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_470,plain,
% 47.94/6.49      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) = iProver_top ),
% 47.94/6.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_4,plain,
% 47.94/6.49      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 47.94/6.49      inference(cnf_transformation,[],[f60]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_475,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 47.94/6.49      | r1_tarski(X0,X1) != iProver_top ),
% 47.94/6.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_4612,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0)))) = k1_xboole_0 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_470,c_475]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_1818,plain,
% 47.94/6.49      ( k3_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0))) = X0 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_470,c_473]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f70]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_476,plain,
% 47.94/6.49      ( r1_tarski(X0,X0) = iProver_top ),
% 47.94/6.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_1815,plain,
% 47.94/6.49      ( k3_xboole_0(X0,X0) = X0 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_476,c_473]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_9,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 47.94/6.49      inference(cnf_transformation,[],[f64]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_0,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 47.94/6.49      inference(cnf_transformation,[],[f59]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_834,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_2574,plain,
% 47.94/6.49      ( k5_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_1815,c_834]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_4621,plain,
% 47.94/6.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 47.94/6.49      inference(light_normalisation,[status(thm)],[c_4612,c_1818,c_2574]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_11,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 47.94/6.49      inference(cnf_transformation,[],[f43]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_2745,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_2574,c_11]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_3398,plain,
% 47.94/6.49      ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_2574,c_2745]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_3508,plain,
% 47.94/6.49      ( k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0 ),
% 47.94/6.49      inference(light_normalisation,[status(thm)],[c_3398,c_9]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_5364,plain,
% 47.94/6.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_4621,c_3508]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_5366,plain,
% 47.94/6.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_4621,c_2574]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_5842,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_5366,c_11]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_5365,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_4621,c_2745]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_5378,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_5364,c_5365]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_6642,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_5842,c_5378]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_5368,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_4621,c_9]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_6660,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_6642,c_5368]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_7198,plain,
% 47.94/6.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_6660,c_5378]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_6332,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_11,c_5378]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_6693,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k1_xboole_0)) = X1 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_5366,c_6332]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_6728,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 47.94/6.49      inference(light_normalisation,[status(thm)],[c_6693,c_5368]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_7466,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_11,c_6728]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_8955,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X2,X0)) = X1 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_7198,c_7466]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_9105,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X0)) = X1 ),
% 47.94/6.49      inference(light_normalisation,[status(thm)],[c_8955,c_11]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_10495,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X0)) = k1_xboole_0 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_5364,c_9105]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_11478,plain,
% 47.94/6.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_10495,c_6728]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_11999,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)),k5_xboole_0(X1,X0)) = X2 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_11478,c_7466]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_12067,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X2,X1)) = X0 ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_11999,c_11478]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_8,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 47.94/6.49      inference(cnf_transformation,[],[f63]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_1204,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0)))),k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k3_xboole_0(X0,k5_xboole_0(X1,X2))) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_11,c_8]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_7,plain,
% 47.94/6.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 47.94/6.49      inference(cnf_transformation,[],[f62]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_472,plain,
% 47.94/6.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 47.94/6.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_837,plain,
% 47.94/6.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_0,c_472]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_1819,plain,
% 47.94/6.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_837,c_473]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_10,plain,
% 47.94/6.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 47.94/6.49      inference(cnf_transformation,[],[f65]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_995,plain,
% 47.94/6.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))))) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_42540,plain,
% 47.94/6.49      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))))) = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X1) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_1819,c_995]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_43866,plain,
% 47.94/6.49      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X1) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_42540,c_10,c_4621,c_5366,c_5368]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_47598,plain,
% 47.94/6.49      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(k3_xboole_0(X1,X2),X1))) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_43866,c_10]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_47616,plain,
% 47.94/6.49      ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k1_xboole_0 ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_47598,c_10,c_5366]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_836,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_0,c_0]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_10110,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_836,c_5378]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_10155,plain,
% 47.94/6.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 47.94/6.49      inference(light_normalisation,[status(thm)],[c_10110,c_0]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_49372,plain,
% 47.94/6.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_47616,c_10155]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_52493,plain,
% 47.94/6.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0)))) = k1_xboole_0 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_11,c_49372]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_62344,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0)))),k1_xboole_0) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k3_xboole_0(X0,k5_xboole_0(X1,X2))) ),
% 47.94/6.49      inference(light_normalisation,[status(thm)],[c_1204,c_52493]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_12006,plain,
% 47.94/6.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_11478,c_11]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_12057,plain,
% 47.94/6.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 47.94/6.49      inference(light_normalisation,[status(thm)],[c_12006,c_11]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_33774,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k1_xboole_0) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_12057,c_6728]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_34063,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k1_xboole_0) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 47.94/6.49      inference(light_normalisation,[status(thm)],[c_33774,c_11]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_62345,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X0,X2),X1)))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X2)),k3_xboole_0(X1,k5_xboole_0(X0,X2))) ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_62344,c_34063]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_6678,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),X2))) = X2 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_5378,c_6332]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_62691,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),X2)))))) = k3_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_62345,c_6678]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_6340,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = X2 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_5378,c_11]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_6343,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = X2 ),
% 47.94/6.49      inference(light_normalisation,[status(thm)],[c_6340,c_11]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_7151,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(k5_xboole_0(X3,X1),k5_xboole_0(X3,X2)) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_6343,c_6332]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_7201,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X2,X1) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_6660,c_6332]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_7247,plain,
% 47.94/6.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_7151,c_7201]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_7558,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,X2),X0)) = X2 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_7198,c_6332]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_62720,plain,
% 47.94/6.49      ( k3_xboole_0(X0,k5_xboole_0(X1,X2)) = k3_xboole_0(k5_xboole_0(X1,X2),X0) ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_62691,c_7247,c_7558]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_103314,plain,
% 47.94/6.49      ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),k5_xboole_0(X3,X2))) = k3_xboole_0(X1,X0) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_12067,c_62720]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_103893,plain,
% 47.94/6.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_103314,c_12067]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_176284,plain,
% 47.94/6.49      ( k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_169116,c_103893]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_52549,plain,
% 47.94/6.49      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_49372,c_49372]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_52599,plain,
% 47.94/6.49      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_52549,c_5368]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_15,negated_conjecture,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 47.94/6.49      inference(cnf_transformation,[],[f68]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_733,plain,
% 47.94/6.49      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_11,c_15]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_750,plain,
% 47.94/6.49      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_11,c_733]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_7520,plain,
% 47.94/6.49      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_7198,c_750]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_7920,plain,
% 47.94/6.49      ( k5_xboole_0(sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 47.94/6.49      inference(superposition,[status(thm)],[c_11,c_7520]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_53435,plain,
% 47.94/6.49      ( k5_xboole_0(sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0))) != sK1 ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_52599,c_7920]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_53441,plain,
% 47.94/6.49      ( k5_xboole_0(sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_53435,c_5368]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_190605,plain,
% 47.94/6.49      ( k5_xboole_0(sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_176284,c_53441]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_190608,plain,
% 47.94/6.49      ( sK1 != sK1 ),
% 47.94/6.49      inference(demodulation,[status(thm)],[c_190605,c_5366,c_5368]) ).
% 47.94/6.49  
% 47.94/6.49  cnf(c_190609,plain,
% 47.94/6.49      ( $false ),
% 47.94/6.49      inference(equality_resolution_simp,[status(thm)],[c_190608]) ).
% 47.94/6.49  
% 47.94/6.49  
% 47.94/6.49  % SZS output end CNFRefutation for theBenchmark.p
% 47.94/6.49  
% 47.94/6.49  ------                               Statistics
% 47.94/6.49  
% 47.94/6.49  ------ Selected
% 47.94/6.49  
% 47.94/6.49  total_time:                             5.925
% 47.94/6.49  
%------------------------------------------------------------------------------
