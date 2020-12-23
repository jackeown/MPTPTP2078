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
% DateTime   : Thu Dec  3 11:23:43 EST 2020

% Result     : Theorem 19.83s
% Output     : CNFRefutation 19.83s
% Verified   : 
% Statistics : Number of formulae       :  125 (1027 expanded)
%              Number of clauses        :   78 ( 421 expanded)
%              Number of leaves         :   18 ( 262 expanded)
%              Depth                    :   22
%              Number of atoms          :  191 (1345 expanded)
%              Number of equality atoms :  128 (1094 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f36,f40])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f21])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK2 != sK4
      & r1_xboole_0(sK4,sK3)
      & r1_xboole_0(sK2,sK3)
      & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( sK2 != sK4
    & r1_xboole_0(sK4,sK3)
    & r1_xboole_0(sK2,sK3)
    & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f27])).

fof(f42,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f25])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f23])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f43,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f44,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_261,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_9])).

cnf(c_580,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10,c_261])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_581,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_580,c_8])).

cnf(c_678,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_581])).

cnf(c_15,negated_conjecture,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_688,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_581,c_8])).

cnf(c_690,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_688,c_6])).

cnf(c_1010,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK3) = k2_xboole_0(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_15,c_690])).

cnf(c_1022,plain,
    ( k2_xboole_0(sK4,sK3) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_1010,c_690])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_579,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_10,c_8])).

cnf(c_2110,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_579])).

cnf(c_56711,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k2_xboole_0(sK4,k4_xboole_0(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_1022,c_2110])).

cnf(c_57597,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(k1_xboole_0,sK3)) = k2_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_678,c_56711])).

cnf(c_676,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_581])).

cnf(c_57598,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(sK2,sK3)) = k2_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_676,c_56711])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_260,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_129,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_14])).

cnf(c_130,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(unflattening,[status(thm)],[c_129])).

cnf(c_257,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_130])).

cnf(c_7414,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_260,c_257])).

cnf(c_7730,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7414,c_8])).

cnf(c_730,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15,c_676])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_99,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | k2_xboole_0(X0,X1) = X1 ),
    inference(resolution,[status(thm)],[c_4,c_5])).

cnf(c_746,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_730,c_99])).

cnf(c_11,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_680,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_581])).

cnf(c_837,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_680,c_10])).

cnf(c_843,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_837,c_10,c_678])).

cnf(c_1564,plain,
    ( k4_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_746,c_843])).

cnf(c_2109,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,X0),sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1564,c_579])).

cnf(c_2148,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK4,k2_xboole_0(X0,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_2109,c_6,c_10])).

cnf(c_1553,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_843])).

cnf(c_577,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k1_xboole_0
    | k2_xboole_0(k4_xboole_0(X0,X1),X2) = X2 ),
    inference(superposition,[status(thm)],[c_10,c_99])).

cnf(c_2485,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1553,c_577])).

cnf(c_2495,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2485,c_10])).

cnf(c_4725,plain,
    ( k2_xboole_0(k4_xboole_0(X0,sK3),X0) = X0 ),
    inference(superposition,[status(thm)],[c_2148,c_2495])).

cnf(c_7733,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_7730,c_6,c_4725])).

cnf(c_2101,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_680,c_579])).

cnf(c_2155,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2101,c_6])).

cnf(c_2156,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_2155,c_10])).

cnf(c_1357,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,sK2),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_730,c_577])).

cnf(c_1649,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK4,sK2),X0),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1357,c_843])).

cnf(c_1650,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK2,X0),sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1649,c_10])).

cnf(c_3413,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1650])).

cnf(c_6285,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,X0),k4_xboole_0(sK4,sK3)) = k2_xboole_0(k2_xboole_0(sK2,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3413,c_579])).

cnf(c_6286,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,X0),k4_xboole_0(sK4,sK3)) = k2_xboole_0(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_6285,c_6])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_120,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK3 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_13])).

cnf(c_121,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) ),
    inference(unflattening,[status(thm)],[c_120])).

cnf(c_258,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_121])).

cnf(c_7413,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_260,c_258])).

cnf(c_7620,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,sK3),sK4) = k2_xboole_0(k4_xboole_0(sK4,sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7413,c_8])).

cnf(c_7624,plain,
    ( k4_xboole_0(sK4,sK3) = sK4 ),
    inference(demodulation,[status(thm)],[c_7620,c_6,c_4725])).

cnf(c_22367,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,X0),sK4) = k2_xboole_0(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_6286,c_6286,c_7624])).

cnf(c_22402,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_22367,c_0])).

cnf(c_22667,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(X0,sK2),k2_xboole_0(X1,X0))) = k2_xboole_0(sK4,sK2) ),
    inference(superposition,[status(thm)],[c_2156,c_22402])).

cnf(c_22727,plain,
    ( k2_xboole_0(sK4,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_22667,c_2156])).

cnf(c_57748,plain,
    ( k2_xboole_0(sK4,k1_xboole_0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_57598,c_7733,c_22727])).

cnf(c_57749,plain,
    ( k2_xboole_0(sK4,k4_xboole_0(k1_xboole_0,sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_57597,c_57748])).

cnf(c_57750,plain,
    ( sK4 = sK2 ),
    inference(demodulation,[status(thm)],[c_57749,c_6,c_678])).

cnf(c_178,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_568,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_179,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_268,plain,
    ( sK4 != X0
    | sK2 != X0
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_179])).

cnf(c_411,plain,
    ( sK4 != sK2
    | sK2 = sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_268])).

cnf(c_12,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_57750,c_568,c_411,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 19.83/3.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.83/3.00  
% 19.83/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.83/3.00  
% 19.83/3.00  ------  iProver source info
% 19.83/3.00  
% 19.83/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.83/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.83/3.00  git: non_committed_changes: false
% 19.83/3.00  git: last_make_outside_of_git: false
% 19.83/3.00  
% 19.83/3.00  ------ 
% 19.83/3.00  
% 19.83/3.00  ------ Input Options
% 19.83/3.00  
% 19.83/3.00  --out_options                           all
% 19.83/3.00  --tptp_safe_out                         true
% 19.83/3.00  --problem_path                          ""
% 19.83/3.00  --include_path                          ""
% 19.83/3.00  --clausifier                            res/vclausify_rel
% 19.83/3.00  --clausifier_options                    ""
% 19.83/3.00  --stdin                                 false
% 19.83/3.00  --stats_out                             all
% 19.83/3.00  
% 19.83/3.00  ------ General Options
% 19.83/3.00  
% 19.83/3.00  --fof                                   false
% 19.83/3.00  --time_out_real                         305.
% 19.83/3.00  --time_out_virtual                      -1.
% 19.83/3.00  --symbol_type_check                     false
% 19.83/3.00  --clausify_out                          false
% 19.83/3.00  --sig_cnt_out                           false
% 19.83/3.00  --trig_cnt_out                          false
% 19.83/3.00  --trig_cnt_out_tolerance                1.
% 19.83/3.00  --trig_cnt_out_sk_spl                   false
% 19.83/3.00  --abstr_cl_out                          false
% 19.83/3.00  
% 19.83/3.00  ------ Global Options
% 19.83/3.00  
% 19.83/3.00  --schedule                              default
% 19.83/3.00  --add_important_lit                     false
% 19.83/3.00  --prop_solver_per_cl                    1000
% 19.83/3.00  --min_unsat_core                        false
% 19.83/3.00  --soft_assumptions                      false
% 19.83/3.00  --soft_lemma_size                       3
% 19.83/3.00  --prop_impl_unit_size                   0
% 19.83/3.00  --prop_impl_unit                        []
% 19.83/3.00  --share_sel_clauses                     true
% 19.83/3.00  --reset_solvers                         false
% 19.83/3.00  --bc_imp_inh                            [conj_cone]
% 19.83/3.00  --conj_cone_tolerance                   3.
% 19.83/3.00  --extra_neg_conj                        none
% 19.83/3.00  --large_theory_mode                     true
% 19.83/3.00  --prolific_symb_bound                   200
% 19.83/3.00  --lt_threshold                          2000
% 19.83/3.00  --clause_weak_htbl                      true
% 19.83/3.00  --gc_record_bc_elim                     false
% 19.83/3.00  
% 19.83/3.00  ------ Preprocessing Options
% 19.83/3.00  
% 19.83/3.00  --preprocessing_flag                    true
% 19.83/3.00  --time_out_prep_mult                    0.1
% 19.83/3.00  --splitting_mode                        input
% 19.83/3.00  --splitting_grd                         true
% 19.83/3.00  --splitting_cvd                         false
% 19.83/3.00  --splitting_cvd_svl                     false
% 19.83/3.00  --splitting_nvd                         32
% 19.83/3.00  --sub_typing                            true
% 19.83/3.00  --prep_gs_sim                           true
% 19.83/3.00  --prep_unflatten                        true
% 19.83/3.00  --prep_res_sim                          true
% 19.83/3.00  --prep_upred                            true
% 19.83/3.00  --prep_sem_filter                       exhaustive
% 19.83/3.00  --prep_sem_filter_out                   false
% 19.83/3.00  --pred_elim                             true
% 19.83/3.00  --res_sim_input                         true
% 19.83/3.00  --eq_ax_congr_red                       true
% 19.83/3.00  --pure_diseq_elim                       true
% 19.83/3.00  --brand_transform                       false
% 19.83/3.00  --non_eq_to_eq                          false
% 19.83/3.00  --prep_def_merge                        true
% 19.83/3.00  --prep_def_merge_prop_impl              false
% 19.83/3.00  --prep_def_merge_mbd                    true
% 19.83/3.00  --prep_def_merge_tr_red                 false
% 19.83/3.00  --prep_def_merge_tr_cl                  false
% 19.83/3.00  --smt_preprocessing                     true
% 19.83/3.00  --smt_ac_axioms                         fast
% 19.83/3.00  --preprocessed_out                      false
% 19.83/3.00  --preprocessed_stats                    false
% 19.83/3.00  
% 19.83/3.00  ------ Abstraction refinement Options
% 19.83/3.00  
% 19.83/3.00  --abstr_ref                             []
% 19.83/3.00  --abstr_ref_prep                        false
% 19.83/3.00  --abstr_ref_until_sat                   false
% 19.83/3.00  --abstr_ref_sig_restrict                funpre
% 19.83/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.83/3.00  --abstr_ref_under                       []
% 19.83/3.00  
% 19.83/3.00  ------ SAT Options
% 19.83/3.00  
% 19.83/3.00  --sat_mode                              false
% 19.83/3.00  --sat_fm_restart_options                ""
% 19.83/3.00  --sat_gr_def                            false
% 19.83/3.00  --sat_epr_types                         true
% 19.83/3.00  --sat_non_cyclic_types                  false
% 19.83/3.00  --sat_finite_models                     false
% 19.83/3.00  --sat_fm_lemmas                         false
% 19.83/3.00  --sat_fm_prep                           false
% 19.83/3.00  --sat_fm_uc_incr                        true
% 19.83/3.00  --sat_out_model                         small
% 19.83/3.00  --sat_out_clauses                       false
% 19.83/3.00  
% 19.83/3.00  ------ QBF Options
% 19.83/3.00  
% 19.83/3.00  --qbf_mode                              false
% 19.83/3.00  --qbf_elim_univ                         false
% 19.83/3.00  --qbf_dom_inst                          none
% 19.83/3.00  --qbf_dom_pre_inst                      false
% 19.83/3.00  --qbf_sk_in                             false
% 19.83/3.00  --qbf_pred_elim                         true
% 19.83/3.00  --qbf_split                             512
% 19.83/3.00  
% 19.83/3.00  ------ BMC1 Options
% 19.83/3.00  
% 19.83/3.00  --bmc1_incremental                      false
% 19.83/3.00  --bmc1_axioms                           reachable_all
% 19.83/3.00  --bmc1_min_bound                        0
% 19.83/3.00  --bmc1_max_bound                        -1
% 19.83/3.00  --bmc1_max_bound_default                -1
% 19.83/3.00  --bmc1_symbol_reachability              true
% 19.83/3.00  --bmc1_property_lemmas                  false
% 19.83/3.00  --bmc1_k_induction                      false
% 19.83/3.00  --bmc1_non_equiv_states                 false
% 19.83/3.00  --bmc1_deadlock                         false
% 19.83/3.00  --bmc1_ucm                              false
% 19.83/3.00  --bmc1_add_unsat_core                   none
% 19.83/3.00  --bmc1_unsat_core_children              false
% 19.83/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.83/3.00  --bmc1_out_stat                         full
% 19.83/3.00  --bmc1_ground_init                      false
% 19.83/3.00  --bmc1_pre_inst_next_state              false
% 19.83/3.00  --bmc1_pre_inst_state                   false
% 19.83/3.00  --bmc1_pre_inst_reach_state             false
% 19.83/3.00  --bmc1_out_unsat_core                   false
% 19.83/3.00  --bmc1_aig_witness_out                  false
% 19.83/3.00  --bmc1_verbose                          false
% 19.83/3.00  --bmc1_dump_clauses_tptp                false
% 19.83/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.83/3.00  --bmc1_dump_file                        -
% 19.83/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.83/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.83/3.00  --bmc1_ucm_extend_mode                  1
% 19.83/3.00  --bmc1_ucm_init_mode                    2
% 19.83/3.00  --bmc1_ucm_cone_mode                    none
% 19.83/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.83/3.00  --bmc1_ucm_relax_model                  4
% 19.83/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.83/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.83/3.00  --bmc1_ucm_layered_model                none
% 19.83/3.00  --bmc1_ucm_max_lemma_size               10
% 19.83/3.00  
% 19.83/3.00  ------ AIG Options
% 19.83/3.00  
% 19.83/3.00  --aig_mode                              false
% 19.83/3.00  
% 19.83/3.00  ------ Instantiation Options
% 19.83/3.00  
% 19.83/3.00  --instantiation_flag                    true
% 19.83/3.00  --inst_sos_flag                         true
% 19.83/3.00  --inst_sos_phase                        true
% 19.83/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.83/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.83/3.00  --inst_lit_sel_side                     num_symb
% 19.83/3.00  --inst_solver_per_active                1400
% 19.83/3.00  --inst_solver_calls_frac                1.
% 19.83/3.00  --inst_passive_queue_type               priority_queues
% 19.83/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.83/3.00  --inst_passive_queues_freq              [25;2]
% 19.83/3.00  --inst_dismatching                      true
% 19.83/3.00  --inst_eager_unprocessed_to_passive     true
% 19.83/3.00  --inst_prop_sim_given                   true
% 19.83/3.00  --inst_prop_sim_new                     false
% 19.83/3.00  --inst_subs_new                         false
% 19.83/3.00  --inst_eq_res_simp                      false
% 19.83/3.00  --inst_subs_given                       false
% 19.83/3.00  --inst_orphan_elimination               true
% 19.83/3.00  --inst_learning_loop_flag               true
% 19.83/3.00  --inst_learning_start                   3000
% 19.83/3.00  --inst_learning_factor                  2
% 19.83/3.00  --inst_start_prop_sim_after_learn       3
% 19.83/3.00  --inst_sel_renew                        solver
% 19.83/3.00  --inst_lit_activity_flag                true
% 19.83/3.00  --inst_restr_to_given                   false
% 19.83/3.00  --inst_activity_threshold               500
% 19.83/3.00  --inst_out_proof                        true
% 19.83/3.00  
% 19.83/3.00  ------ Resolution Options
% 19.83/3.00  
% 19.83/3.00  --resolution_flag                       true
% 19.83/3.00  --res_lit_sel                           adaptive
% 19.83/3.00  --res_lit_sel_side                      none
% 19.83/3.00  --res_ordering                          kbo
% 19.83/3.00  --res_to_prop_solver                    active
% 19.83/3.00  --res_prop_simpl_new                    false
% 19.83/3.00  --res_prop_simpl_given                  true
% 19.83/3.00  --res_passive_queue_type                priority_queues
% 19.83/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.83/3.00  --res_passive_queues_freq               [15;5]
% 19.83/3.00  --res_forward_subs                      full
% 19.83/3.00  --res_backward_subs                     full
% 19.83/3.00  --res_forward_subs_resolution           true
% 19.83/3.00  --res_backward_subs_resolution          true
% 19.83/3.00  --res_orphan_elimination                true
% 19.83/3.00  --res_time_limit                        2.
% 19.83/3.00  --res_out_proof                         true
% 19.83/3.00  
% 19.83/3.00  ------ Superposition Options
% 19.83/3.00  
% 19.83/3.00  --superposition_flag                    true
% 19.83/3.00  --sup_passive_queue_type                priority_queues
% 19.83/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.83/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.83/3.00  --demod_completeness_check              fast
% 19.83/3.00  --demod_use_ground                      true
% 19.83/3.00  --sup_to_prop_solver                    passive
% 19.83/3.00  --sup_prop_simpl_new                    true
% 19.83/3.00  --sup_prop_simpl_given                  true
% 19.83/3.00  --sup_fun_splitting                     true
% 19.83/3.00  --sup_smt_interval                      50000
% 19.83/3.00  
% 19.83/3.00  ------ Superposition Simplification Setup
% 19.83/3.00  
% 19.83/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.83/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.83/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.83/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.83/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.83/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.83/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.83/3.00  --sup_immed_triv                        [TrivRules]
% 19.83/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.83/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.83/3.00  --sup_immed_bw_main                     []
% 19.83/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.83/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.83/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.83/3.00  --sup_input_bw                          []
% 19.83/3.00  
% 19.83/3.00  ------ Combination Options
% 19.83/3.00  
% 19.83/3.00  --comb_res_mult                         3
% 19.83/3.00  --comb_sup_mult                         2
% 19.83/3.00  --comb_inst_mult                        10
% 19.83/3.00  
% 19.83/3.00  ------ Debug Options
% 19.83/3.00  
% 19.83/3.00  --dbg_backtrace                         false
% 19.83/3.00  --dbg_dump_prop_clauses                 false
% 19.83/3.00  --dbg_dump_prop_clauses_file            -
% 19.83/3.00  --dbg_out_stat                          false
% 19.83/3.00  ------ Parsing...
% 19.83/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.83/3.00  
% 19.83/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.83/3.00  
% 19.83/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.83/3.00  
% 19.83/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.83/3.00  ------ Proving...
% 19.83/3.00  ------ Problem Properties 
% 19.83/3.00  
% 19.83/3.00  
% 19.83/3.00  clauses                                 14
% 19.83/3.00  conjectures                             2
% 19.83/3.00  EPR                                     1
% 19.83/3.00  Horn                                    13
% 19.83/3.00  unary                                   11
% 19.83/3.00  binary                                  3
% 19.83/3.00  lits                                    17
% 19.83/3.00  lits eq                                 12
% 19.83/3.00  fd_pure                                 0
% 19.83/3.00  fd_pseudo                               0
% 19.83/3.00  fd_cond                                 1
% 19.83/3.00  fd_pseudo_cond                          0
% 19.83/3.00  AC symbols                              0
% 19.83/3.00  
% 19.83/3.00  ------ Schedule dynamic 5 is on 
% 19.83/3.00  
% 19.83/3.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.83/3.00  
% 19.83/3.00  
% 19.83/3.00  ------ 
% 19.83/3.00  Current options:
% 19.83/3.00  ------ 
% 19.83/3.00  
% 19.83/3.00  ------ Input Options
% 19.83/3.00  
% 19.83/3.00  --out_options                           all
% 19.83/3.00  --tptp_safe_out                         true
% 19.83/3.00  --problem_path                          ""
% 19.83/3.00  --include_path                          ""
% 19.83/3.00  --clausifier                            res/vclausify_rel
% 19.83/3.00  --clausifier_options                    ""
% 19.83/3.00  --stdin                                 false
% 19.83/3.00  --stats_out                             all
% 19.83/3.00  
% 19.83/3.00  ------ General Options
% 19.83/3.00  
% 19.83/3.00  --fof                                   false
% 19.83/3.00  --time_out_real                         305.
% 19.83/3.00  --time_out_virtual                      -1.
% 19.83/3.00  --symbol_type_check                     false
% 19.83/3.00  --clausify_out                          false
% 19.83/3.00  --sig_cnt_out                           false
% 19.83/3.00  --trig_cnt_out                          false
% 19.83/3.00  --trig_cnt_out_tolerance                1.
% 19.83/3.00  --trig_cnt_out_sk_spl                   false
% 19.83/3.00  --abstr_cl_out                          false
% 19.83/3.00  
% 19.83/3.00  ------ Global Options
% 19.83/3.00  
% 19.83/3.00  --schedule                              default
% 19.83/3.00  --add_important_lit                     false
% 19.83/3.00  --prop_solver_per_cl                    1000
% 19.83/3.00  --min_unsat_core                        false
% 19.83/3.00  --soft_assumptions                      false
% 19.83/3.00  --soft_lemma_size                       3
% 19.83/3.00  --prop_impl_unit_size                   0
% 19.83/3.00  --prop_impl_unit                        []
% 19.83/3.00  --share_sel_clauses                     true
% 19.83/3.00  --reset_solvers                         false
% 19.83/3.00  --bc_imp_inh                            [conj_cone]
% 19.83/3.00  --conj_cone_tolerance                   3.
% 19.83/3.00  --extra_neg_conj                        none
% 19.83/3.00  --large_theory_mode                     true
% 19.83/3.00  --prolific_symb_bound                   200
% 19.83/3.00  --lt_threshold                          2000
% 19.83/3.00  --clause_weak_htbl                      true
% 19.83/3.00  --gc_record_bc_elim                     false
% 19.83/3.00  
% 19.83/3.00  ------ Preprocessing Options
% 19.83/3.00  
% 19.83/3.00  --preprocessing_flag                    true
% 19.83/3.00  --time_out_prep_mult                    0.1
% 19.83/3.00  --splitting_mode                        input
% 19.83/3.00  --splitting_grd                         true
% 19.83/3.00  --splitting_cvd                         false
% 19.83/3.00  --splitting_cvd_svl                     false
% 19.83/3.00  --splitting_nvd                         32
% 19.83/3.00  --sub_typing                            true
% 19.83/3.00  --prep_gs_sim                           true
% 19.83/3.00  --prep_unflatten                        true
% 19.83/3.00  --prep_res_sim                          true
% 19.83/3.00  --prep_upred                            true
% 19.83/3.00  --prep_sem_filter                       exhaustive
% 19.83/3.00  --prep_sem_filter_out                   false
% 19.83/3.00  --pred_elim                             true
% 19.83/3.00  --res_sim_input                         true
% 19.83/3.00  --eq_ax_congr_red                       true
% 19.83/3.00  --pure_diseq_elim                       true
% 19.83/3.00  --brand_transform                       false
% 19.83/3.00  --non_eq_to_eq                          false
% 19.83/3.00  --prep_def_merge                        true
% 19.83/3.00  --prep_def_merge_prop_impl              false
% 19.83/3.00  --prep_def_merge_mbd                    true
% 19.83/3.00  --prep_def_merge_tr_red                 false
% 19.83/3.00  --prep_def_merge_tr_cl                  false
% 19.83/3.00  --smt_preprocessing                     true
% 19.83/3.00  --smt_ac_axioms                         fast
% 19.83/3.00  --preprocessed_out                      false
% 19.83/3.00  --preprocessed_stats                    false
% 19.83/3.00  
% 19.83/3.00  ------ Abstraction refinement Options
% 19.83/3.00  
% 19.83/3.00  --abstr_ref                             []
% 19.83/3.00  --abstr_ref_prep                        false
% 19.83/3.00  --abstr_ref_until_sat                   false
% 19.83/3.00  --abstr_ref_sig_restrict                funpre
% 19.83/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.83/3.00  --abstr_ref_under                       []
% 19.83/3.00  
% 19.83/3.00  ------ SAT Options
% 19.83/3.00  
% 19.83/3.00  --sat_mode                              false
% 19.83/3.00  --sat_fm_restart_options                ""
% 19.83/3.00  --sat_gr_def                            false
% 19.83/3.00  --sat_epr_types                         true
% 19.83/3.00  --sat_non_cyclic_types                  false
% 19.83/3.00  --sat_finite_models                     false
% 19.83/3.00  --sat_fm_lemmas                         false
% 19.83/3.00  --sat_fm_prep                           false
% 19.83/3.00  --sat_fm_uc_incr                        true
% 19.83/3.00  --sat_out_model                         small
% 19.83/3.00  --sat_out_clauses                       false
% 19.83/3.00  
% 19.83/3.00  ------ QBF Options
% 19.83/3.00  
% 19.83/3.00  --qbf_mode                              false
% 19.83/3.00  --qbf_elim_univ                         false
% 19.83/3.00  --qbf_dom_inst                          none
% 19.83/3.00  --qbf_dom_pre_inst                      false
% 19.83/3.00  --qbf_sk_in                             false
% 19.83/3.00  --qbf_pred_elim                         true
% 19.83/3.00  --qbf_split                             512
% 19.83/3.00  
% 19.83/3.00  ------ BMC1 Options
% 19.83/3.00  
% 19.83/3.00  --bmc1_incremental                      false
% 19.83/3.00  --bmc1_axioms                           reachable_all
% 19.83/3.00  --bmc1_min_bound                        0
% 19.83/3.00  --bmc1_max_bound                        -1
% 19.83/3.00  --bmc1_max_bound_default                -1
% 19.83/3.00  --bmc1_symbol_reachability              true
% 19.83/3.00  --bmc1_property_lemmas                  false
% 19.83/3.00  --bmc1_k_induction                      false
% 19.83/3.00  --bmc1_non_equiv_states                 false
% 19.83/3.00  --bmc1_deadlock                         false
% 19.83/3.00  --bmc1_ucm                              false
% 19.83/3.00  --bmc1_add_unsat_core                   none
% 19.83/3.00  --bmc1_unsat_core_children              false
% 19.83/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.83/3.00  --bmc1_out_stat                         full
% 19.83/3.00  --bmc1_ground_init                      false
% 19.83/3.00  --bmc1_pre_inst_next_state              false
% 19.83/3.00  --bmc1_pre_inst_state                   false
% 19.83/3.00  --bmc1_pre_inst_reach_state             false
% 19.83/3.00  --bmc1_out_unsat_core                   false
% 19.83/3.00  --bmc1_aig_witness_out                  false
% 19.83/3.00  --bmc1_verbose                          false
% 19.83/3.00  --bmc1_dump_clauses_tptp                false
% 19.83/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.83/3.00  --bmc1_dump_file                        -
% 19.83/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.83/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.83/3.00  --bmc1_ucm_extend_mode                  1
% 19.83/3.00  --bmc1_ucm_init_mode                    2
% 19.83/3.00  --bmc1_ucm_cone_mode                    none
% 19.83/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.83/3.00  --bmc1_ucm_relax_model                  4
% 19.83/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.83/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.83/3.00  --bmc1_ucm_layered_model                none
% 19.83/3.00  --bmc1_ucm_max_lemma_size               10
% 19.83/3.00  
% 19.83/3.00  ------ AIG Options
% 19.83/3.00  
% 19.83/3.00  --aig_mode                              false
% 19.83/3.00  
% 19.83/3.00  ------ Instantiation Options
% 19.83/3.00  
% 19.83/3.00  --instantiation_flag                    true
% 19.83/3.00  --inst_sos_flag                         true
% 19.83/3.00  --inst_sos_phase                        true
% 19.83/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.83/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.83/3.00  --inst_lit_sel_side                     none
% 19.83/3.00  --inst_solver_per_active                1400
% 19.83/3.00  --inst_solver_calls_frac                1.
% 19.83/3.00  --inst_passive_queue_type               priority_queues
% 19.83/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.83/3.00  --inst_passive_queues_freq              [25;2]
% 19.83/3.00  --inst_dismatching                      true
% 19.83/3.00  --inst_eager_unprocessed_to_passive     true
% 19.83/3.00  --inst_prop_sim_given                   true
% 19.83/3.00  --inst_prop_sim_new                     false
% 19.83/3.00  --inst_subs_new                         false
% 19.83/3.00  --inst_eq_res_simp                      false
% 19.83/3.00  --inst_subs_given                       false
% 19.83/3.00  --inst_orphan_elimination               true
% 19.83/3.00  --inst_learning_loop_flag               true
% 19.83/3.00  --inst_learning_start                   3000
% 19.83/3.00  --inst_learning_factor                  2
% 19.83/3.00  --inst_start_prop_sim_after_learn       3
% 19.83/3.00  --inst_sel_renew                        solver
% 19.83/3.00  --inst_lit_activity_flag                true
% 19.83/3.00  --inst_restr_to_given                   false
% 19.83/3.00  --inst_activity_threshold               500
% 19.83/3.00  --inst_out_proof                        true
% 19.83/3.00  
% 19.83/3.00  ------ Resolution Options
% 19.83/3.00  
% 19.83/3.00  --resolution_flag                       false
% 19.83/3.00  --res_lit_sel                           adaptive
% 19.83/3.00  --res_lit_sel_side                      none
% 19.83/3.00  --res_ordering                          kbo
% 19.83/3.00  --res_to_prop_solver                    active
% 19.83/3.00  --res_prop_simpl_new                    false
% 19.83/3.00  --res_prop_simpl_given                  true
% 19.83/3.00  --res_passive_queue_type                priority_queues
% 19.83/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.83/3.00  --res_passive_queues_freq               [15;5]
% 19.83/3.00  --res_forward_subs                      full
% 19.83/3.00  --res_backward_subs                     full
% 19.83/3.00  --res_forward_subs_resolution           true
% 19.83/3.00  --res_backward_subs_resolution          true
% 19.83/3.00  --res_orphan_elimination                true
% 19.83/3.00  --res_time_limit                        2.
% 19.83/3.00  --res_out_proof                         true
% 19.83/3.00  
% 19.83/3.00  ------ Superposition Options
% 19.83/3.00  
% 19.83/3.00  --superposition_flag                    true
% 19.83/3.00  --sup_passive_queue_type                priority_queues
% 19.83/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.83/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.83/3.00  --demod_completeness_check              fast
% 19.83/3.00  --demod_use_ground                      true
% 19.83/3.00  --sup_to_prop_solver                    passive
% 19.83/3.00  --sup_prop_simpl_new                    true
% 19.83/3.00  --sup_prop_simpl_given                  true
% 19.83/3.00  --sup_fun_splitting                     true
% 19.83/3.00  --sup_smt_interval                      50000
% 19.83/3.00  
% 19.83/3.00  ------ Superposition Simplification Setup
% 19.83/3.00  
% 19.83/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.83/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.83/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.83/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.83/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.83/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.83/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.83/3.00  --sup_immed_triv                        [TrivRules]
% 19.83/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.83/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.83/3.00  --sup_immed_bw_main                     []
% 19.83/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.83/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.83/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.83/3.00  --sup_input_bw                          []
% 19.83/3.00  
% 19.83/3.00  ------ Combination Options
% 19.83/3.00  
% 19.83/3.00  --comb_res_mult                         3
% 19.83/3.00  --comb_sup_mult                         2
% 19.83/3.00  --comb_inst_mult                        10
% 19.83/3.00  
% 19.83/3.00  ------ Debug Options
% 19.83/3.00  
% 19.83/3.00  --dbg_backtrace                         false
% 19.83/3.00  --dbg_dump_prop_clauses                 false
% 19.83/3.00  --dbg_dump_prop_clauses_file            -
% 19.83/3.00  --dbg_out_stat                          false
% 19.83/3.00  
% 19.83/3.00  
% 19.83/3.00  
% 19.83/3.00  
% 19.83/3.00  ------ Proving...
% 19.83/3.00  
% 19.83/3.00  
% 19.83/3.00  % SZS status Theorem for theBenchmark.p
% 19.83/3.00  
% 19.83/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.83/3.00  
% 19.83/3.00  fof(f6,axiom,(
% 19.83/3.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 19.83/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.00  
% 19.83/3.00  fof(f35,plain,(
% 19.83/3.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.83/3.00    inference(cnf_transformation,[],[f6])).
% 19.83/3.00  
% 19.83/3.00  fof(f10,axiom,(
% 19.83/3.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 19.83/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.00  
% 19.83/3.00  fof(f39,plain,(
% 19.83/3.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 19.83/3.00    inference(cnf_transformation,[],[f10])).
% 19.83/3.00  
% 19.83/3.00  fof(f7,axiom,(
% 19.83/3.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 19.83/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.00  
% 19.83/3.00  fof(f36,plain,(
% 19.83/3.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 19.83/3.00    inference(cnf_transformation,[],[f7])).
% 19.83/3.00  
% 19.83/3.00  fof(f11,axiom,(
% 19.83/3.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 19.83/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.00  
% 19.83/3.00  fof(f40,plain,(
% 19.83/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.83/3.00    inference(cnf_transformation,[],[f11])).
% 19.83/3.00  
% 19.83/3.00  fof(f48,plain,(
% 19.83/3.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 19.83/3.00    inference(definition_unfolding,[],[f36,f40])).
% 19.83/3.00  
% 19.83/3.00  fof(f9,axiom,(
% 19.83/3.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 19.83/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.00  
% 19.83/3.00  fof(f38,plain,(
% 19.83/3.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.83/3.00    inference(cnf_transformation,[],[f9])).
% 19.83/3.00  
% 19.83/3.00  fof(f8,axiom,(
% 19.83/3.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 19.83/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.00  
% 19.83/3.00  fof(f37,plain,(
% 19.83/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 19.83/3.00    inference(cnf_transformation,[],[f8])).
% 19.83/3.00  
% 19.83/3.00  fof(f13,conjecture,(
% 19.83/3.00    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 19.83/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.00  
% 19.83/3.00  fof(f14,negated_conjecture,(
% 19.83/3.00    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 19.83/3.00    inference(negated_conjecture,[],[f13])).
% 19.83/3.00  
% 19.83/3.00  fof(f21,plain,(
% 19.83/3.00    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 19.83/3.00    inference(ennf_transformation,[],[f14])).
% 19.83/3.00  
% 19.83/3.00  fof(f22,plain,(
% 19.83/3.00    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 19.83/3.00    inference(flattening,[],[f21])).
% 19.83/3.00  
% 19.83/3.00  fof(f27,plain,(
% 19.83/3.00    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK2 != sK4 & r1_xboole_0(sK4,sK3) & r1_xboole_0(sK2,sK3) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3))),
% 19.83/3.00    introduced(choice_axiom,[])).
% 19.83/3.00  
% 19.83/3.00  fof(f28,plain,(
% 19.83/3.00    sK2 != sK4 & r1_xboole_0(sK4,sK3) & r1_xboole_0(sK2,sK3) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3)),
% 19.83/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f27])).
% 19.83/3.00  
% 19.83/3.00  fof(f42,plain,(
% 19.83/3.00    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3)),
% 19.83/3.00    inference(cnf_transformation,[],[f28])).
% 19.83/3.00  
% 19.83/3.00  fof(f1,axiom,(
% 19.83/3.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 19.83/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.00  
% 19.83/3.00  fof(f29,plain,(
% 19.83/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 19.83/3.00    inference(cnf_transformation,[],[f1])).
% 19.83/3.00  
% 19.83/3.00  fof(f3,axiom,(
% 19.83/3.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 19.83/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.00  
% 19.83/3.00  fof(f18,plain,(
% 19.83/3.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 19.83/3.00    inference(ennf_transformation,[],[f3])).
% 19.83/3.00  
% 19.83/3.00  fof(f25,plain,(
% 19.83/3.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 19.83/3.00    introduced(choice_axiom,[])).
% 19.83/3.00  
% 19.83/3.00  fof(f26,plain,(
% 19.83/3.00    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 19.83/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f25])).
% 19.83/3.00  
% 19.83/3.00  fof(f32,plain,(
% 19.83/3.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 19.83/3.00    inference(cnf_transformation,[],[f26])).
% 19.83/3.00  
% 19.83/3.00  fof(f2,axiom,(
% 19.83/3.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 19.83/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.00  
% 19.83/3.00  fof(f15,plain,(
% 19.83/3.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 19.83/3.00    inference(rectify,[],[f2])).
% 19.83/3.00  
% 19.83/3.00  fof(f17,plain,(
% 19.83/3.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 19.83/3.00    inference(ennf_transformation,[],[f15])).
% 19.83/3.00  
% 19.83/3.00  fof(f23,plain,(
% 19.83/3.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 19.83/3.00    introduced(choice_axiom,[])).
% 19.83/3.00  
% 19.83/3.00  fof(f24,plain,(
% 19.83/3.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 19.83/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f23])).
% 19.83/3.00  
% 19.83/3.00  fof(f31,plain,(
% 19.83/3.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 19.83/3.00    inference(cnf_transformation,[],[f24])).
% 19.83/3.00  
% 19.83/3.00  fof(f46,plain,(
% 19.83/3.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 19.83/3.00    inference(definition_unfolding,[],[f31,f40])).
% 19.83/3.00  
% 19.83/3.00  fof(f43,plain,(
% 19.83/3.00    r1_xboole_0(sK2,sK3)),
% 19.83/3.00    inference(cnf_transformation,[],[f28])).
% 19.83/3.00  
% 19.83/3.00  fof(f4,axiom,(
% 19.83/3.00    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 19.83/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.00  
% 19.83/3.00  fof(f16,plain,(
% 19.83/3.00    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) => r1_tarski(X0,X1))),
% 19.83/3.00    inference(unused_predicate_definition_removal,[],[f4])).
% 19.83/3.00  
% 19.83/3.00  fof(f19,plain,(
% 19.83/3.00    ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 19.83/3.00    inference(ennf_transformation,[],[f16])).
% 19.83/3.00  
% 19.83/3.00  fof(f33,plain,(
% 19.83/3.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 19.83/3.00    inference(cnf_transformation,[],[f19])).
% 19.83/3.00  
% 19.83/3.00  fof(f5,axiom,(
% 19.83/3.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 19.83/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.00  
% 19.83/3.00  fof(f20,plain,(
% 19.83/3.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 19.83/3.00    inference(ennf_transformation,[],[f5])).
% 19.83/3.00  
% 19.83/3.00  fof(f34,plain,(
% 19.83/3.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 19.83/3.00    inference(cnf_transformation,[],[f20])).
% 19.83/3.00  
% 19.83/3.00  fof(f12,axiom,(
% 19.83/3.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 19.83/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/3.00  
% 19.83/3.00  fof(f41,plain,(
% 19.83/3.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 19.83/3.00    inference(cnf_transformation,[],[f12])).
% 19.83/3.00  
% 19.83/3.00  fof(f49,plain,(
% 19.83/3.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 19.83/3.00    inference(definition_unfolding,[],[f41,f40])).
% 19.83/3.00  
% 19.83/3.00  fof(f44,plain,(
% 19.83/3.00    r1_xboole_0(sK4,sK3)),
% 19.83/3.00    inference(cnf_transformation,[],[f28])).
% 19.83/3.00  
% 19.83/3.00  fof(f45,plain,(
% 19.83/3.00    sK2 != sK4),
% 19.83/3.00    inference(cnf_transformation,[],[f28])).
% 19.83/3.00  
% 19.83/3.00  cnf(c_6,plain,
% 19.83/3.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.83/3.00      inference(cnf_transformation,[],[f35]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_10,plain,
% 19.83/3.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 19.83/3.00      inference(cnf_transformation,[],[f39]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_7,plain,
% 19.83/3.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 19.83/3.00      inference(cnf_transformation,[],[f48]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_9,plain,
% 19.83/3.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.83/3.00      inference(cnf_transformation,[],[f38]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_261,plain,
% 19.83/3.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.83/3.00      inference(light_normalisation,[status(thm)],[c_7,c_9]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_580,plain,
% 19.83/3.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_10,c_261]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_8,plain,
% 19.83/3.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 19.83/3.00      inference(cnf_transformation,[],[f37]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_581,plain,
% 19.83/3.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 19.83/3.00      inference(demodulation,[status(thm)],[c_580,c_8]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_678,plain,
% 19.83/3.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_6,c_581]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_15,negated_conjecture,
% 19.83/3.00      ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
% 19.83/3.00      inference(cnf_transformation,[],[f42]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_688,plain,
% 19.83/3.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_581,c_8]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_690,plain,
% 19.83/3.00      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 19.83/3.00      inference(demodulation,[status(thm)],[c_688,c_6]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_1010,plain,
% 19.83/3.00      ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK3) = k2_xboole_0(sK4,sK3) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_15,c_690]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_1022,plain,
% 19.83/3.00      ( k2_xboole_0(sK4,sK3) = k2_xboole_0(sK2,sK3) ),
% 19.83/3.00      inference(demodulation,[status(thm)],[c_1010,c_690]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_0,plain,
% 19.83/3.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 19.83/3.00      inference(cnf_transformation,[],[f29]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_579,plain,
% 19.83/3.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_10,c_8]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_2110,plain,
% 19.83/3.00      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_0,c_579]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_56711,plain,
% 19.83/3.00      ( k2_xboole_0(sK4,k4_xboole_0(X0,k2_xboole_0(sK2,sK3))) = k2_xboole_0(sK4,k4_xboole_0(X0,sK3)) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_1022,c_2110]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_57597,plain,
% 19.83/3.00      ( k2_xboole_0(sK4,k4_xboole_0(k1_xboole_0,sK3)) = k2_xboole_0(sK4,k1_xboole_0) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_678,c_56711]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_676,plain,
% 19.83/3.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_0,c_581]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_57598,plain,
% 19.83/3.00      ( k2_xboole_0(sK4,k4_xboole_0(sK2,sK3)) = k2_xboole_0(sK4,k1_xboole_0) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_676,c_56711]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_3,plain,
% 19.83/3.00      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 19.83/3.00      inference(cnf_transformation,[],[f32]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_260,plain,
% 19.83/3.00      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 19.83/3.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_1,plain,
% 19.83/3.00      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 19.83/3.00      | ~ r1_xboole_0(X1,X2) ),
% 19.83/3.00      inference(cnf_transformation,[],[f46]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_14,negated_conjecture,
% 19.83/3.00      ( r1_xboole_0(sK2,sK3) ),
% 19.83/3.00      inference(cnf_transformation,[],[f43]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_129,plain,
% 19.83/3.00      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 19.83/3.00      | sK3 != X2
% 19.83/3.00      | sK2 != X1 ),
% 19.83/3.00      inference(resolution_lifted,[status(thm)],[c_1,c_14]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_130,plain,
% 19.83/3.00      ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 19.83/3.00      inference(unflattening,[status(thm)],[c_129]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_257,plain,
% 19.83/3.00      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 19.83/3.00      inference(predicate_to_equality,[status(thm)],[c_130]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_7414,plain,
% 19.83/3.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_260,c_257]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_7730,plain,
% 19.83/3.00      ( k2_xboole_0(k4_xboole_0(sK2,sK3),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_7414,c_8]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_730,plain,
% 19.83/3.00      ( k4_xboole_0(sK4,k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_15,c_676]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_4,plain,
% 19.83/3.00      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 19.83/3.00      inference(cnf_transformation,[],[f33]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_5,plain,
% 19.83/3.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 19.83/3.00      inference(cnf_transformation,[],[f34]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_99,plain,
% 19.83/3.00      ( k4_xboole_0(X0,X1) != k1_xboole_0 | k2_xboole_0(X0,X1) = X1 ),
% 19.83/3.00      inference(resolution,[status(thm)],[c_4,c_5]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_746,plain,
% 19.83/3.00      ( k2_xboole_0(sK4,k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK2,sK3) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_730,c_99]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_11,plain,
% 19.83/3.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 19.83/3.00      inference(cnf_transformation,[],[f49]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_680,plain,
% 19.83/3.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_11,c_581]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_837,plain,
% 19.83/3.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_680,c_10]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_843,plain,
% 19.83/3.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 19.83/3.00      inference(demodulation,[status(thm)],[c_837,c_10,c_678]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_1564,plain,
% 19.83/3.00      ( k4_xboole_0(k4_xboole_0(sK4,X0),k2_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_746,c_843]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_2109,plain,
% 19.83/3.00      ( k2_xboole_0(sK3,k4_xboole_0(k4_xboole_0(sK4,X0),sK2)) = k2_xboole_0(sK3,k1_xboole_0) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_1564,c_579]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_2148,plain,
% 19.83/3.00      ( k2_xboole_0(sK3,k4_xboole_0(sK4,k2_xboole_0(X0,sK2))) = sK3 ),
% 19.83/3.00      inference(demodulation,[status(thm)],[c_2109,c_6,c_10]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_1553,plain,
% 19.83/3.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X0)) = k1_xboole_0 ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_0,c_843]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_577,plain,
% 19.83/3.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k1_xboole_0
% 19.83/3.00      | k2_xboole_0(k4_xboole_0(X0,X1),X2) = X2 ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_10,c_99]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_2485,plain,
% 19.83/3.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X0) = X0 ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_1553,c_577]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_2495,plain,
% 19.83/3.00      ( k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X0) = X0 ),
% 19.83/3.00      inference(light_normalisation,[status(thm)],[c_2485,c_10]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_4725,plain,
% 19.83/3.00      ( k2_xboole_0(k4_xboole_0(X0,sK3),X0) = X0 ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_2148,c_2495]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_7733,plain,
% 19.83/3.00      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 19.83/3.00      inference(demodulation,[status(thm)],[c_7730,c_6,c_4725]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_2101,plain,
% 19.83/3.00      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_680,c_579]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_2155,plain,
% 19.83/3.00      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(k2_xboole_0(X1,X0),X2),X1)) = X0 ),
% 19.83/3.00      inference(light_normalisation,[status(thm)],[c_2101,c_6]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_2156,plain,
% 19.83/3.00      ( k2_xboole_0(X0,k4_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X2,X1))) = X0 ),
% 19.83/3.00      inference(demodulation,[status(thm)],[c_2155,c_10]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_1357,plain,
% 19.83/3.00      ( k2_xboole_0(k4_xboole_0(sK4,sK2),sK3) = sK3 ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_730,c_577]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_1649,plain,
% 19.83/3.00      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK4,sK2),X0),sK3) = k1_xboole_0 ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_1357,c_843]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_1650,plain,
% 19.83/3.00      ( k4_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK2,X0),sK3)) = k1_xboole_0 ),
% 19.83/3.00      inference(demodulation,[status(thm)],[c_1649,c_10]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_3413,plain,
% 19.83/3.00      ( k4_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK2,X0))) = k1_xboole_0 ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_0,c_1650]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_6285,plain,
% 19.83/3.00      ( k2_xboole_0(k2_xboole_0(sK2,X0),k4_xboole_0(sK4,sK3)) = k2_xboole_0(k2_xboole_0(sK2,X0),k1_xboole_0) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_3413,c_579]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_6286,plain,
% 19.83/3.00      ( k2_xboole_0(k2_xboole_0(sK2,X0),k4_xboole_0(sK4,sK3)) = k2_xboole_0(sK2,X0) ),
% 19.83/3.00      inference(demodulation,[status(thm)],[c_6285,c_6]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_13,negated_conjecture,
% 19.83/3.00      ( r1_xboole_0(sK4,sK3) ),
% 19.83/3.00      inference(cnf_transformation,[],[f44]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_120,plain,
% 19.83/3.00      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 19.83/3.00      | sK3 != X2
% 19.83/3.00      | sK4 != X1 ),
% 19.83/3.00      inference(resolution_lifted,[status(thm)],[c_1,c_13]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_121,plain,
% 19.83/3.00      ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) ),
% 19.83/3.00      inference(unflattening,[status(thm)],[c_120]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_258,plain,
% 19.83/3.00      ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) != iProver_top ),
% 19.83/3.00      inference(predicate_to_equality,[status(thm)],[c_121]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_7413,plain,
% 19.83/3.00      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) = k1_xboole_0 ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_260,c_258]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_7620,plain,
% 19.83/3.00      ( k2_xboole_0(k4_xboole_0(sK4,sK3),sK4) = k2_xboole_0(k4_xboole_0(sK4,sK3),k1_xboole_0) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_7413,c_8]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_7624,plain,
% 19.83/3.00      ( k4_xboole_0(sK4,sK3) = sK4 ),
% 19.83/3.00      inference(demodulation,[status(thm)],[c_7620,c_6,c_4725]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_22367,plain,
% 19.83/3.00      ( k2_xboole_0(k2_xboole_0(sK2,X0),sK4) = k2_xboole_0(sK2,X0) ),
% 19.83/3.00      inference(light_normalisation,[status(thm)],[c_6286,c_6286,c_7624]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_22402,plain,
% 19.83/3.00      ( k2_xboole_0(sK4,k2_xboole_0(sK2,X0)) = k2_xboole_0(sK2,X0) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_22367,c_0]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_22667,plain,
% 19.83/3.00      ( k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(X0,sK2),k2_xboole_0(X1,X0))) = k2_xboole_0(sK4,sK2) ),
% 19.83/3.00      inference(superposition,[status(thm)],[c_2156,c_22402]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_22727,plain,
% 19.83/3.00      ( k2_xboole_0(sK4,sK2) = sK2 ),
% 19.83/3.00      inference(demodulation,[status(thm)],[c_22667,c_2156]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_57748,plain,
% 19.83/3.00      ( k2_xboole_0(sK4,k1_xboole_0) = sK2 ),
% 19.83/3.00      inference(light_normalisation,
% 19.83/3.00                [status(thm)],
% 19.83/3.00                [c_57598,c_7733,c_22727]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_57749,plain,
% 19.83/3.00      ( k2_xboole_0(sK4,k4_xboole_0(k1_xboole_0,sK3)) = sK2 ),
% 19.83/3.00      inference(demodulation,[status(thm)],[c_57597,c_57748]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_57750,plain,
% 19.83/3.00      ( sK4 = sK2 ),
% 19.83/3.00      inference(demodulation,[status(thm)],[c_57749,c_6,c_678]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_178,plain,( X0 = X0 ),theory(equality) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_568,plain,
% 19.83/3.00      ( sK2 = sK2 ),
% 19.83/3.00      inference(instantiation,[status(thm)],[c_178]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_179,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_268,plain,
% 19.83/3.00      ( sK4 != X0 | sK2 != X0 | sK2 = sK4 ),
% 19.83/3.00      inference(instantiation,[status(thm)],[c_179]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_411,plain,
% 19.83/3.00      ( sK4 != sK2 | sK2 = sK4 | sK2 != sK2 ),
% 19.83/3.00      inference(instantiation,[status(thm)],[c_268]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(c_12,negated_conjecture,
% 19.83/3.00      ( sK2 != sK4 ),
% 19.83/3.00      inference(cnf_transformation,[],[f45]) ).
% 19.83/3.00  
% 19.83/3.00  cnf(contradiction,plain,
% 19.83/3.00      ( $false ),
% 19.83/3.00      inference(minisat,[status(thm)],[c_57750,c_568,c_411,c_12]) ).
% 19.83/3.00  
% 19.83/3.00  
% 19.83/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.83/3.00  
% 19.83/3.00  ------                               Statistics
% 19.83/3.00  
% 19.83/3.00  ------ General
% 19.83/3.00  
% 19.83/3.00  abstr_ref_over_cycles:                  0
% 19.83/3.00  abstr_ref_under_cycles:                 0
% 19.83/3.00  gc_basic_clause_elim:                   0
% 19.83/3.00  forced_gc_time:                         0
% 19.83/3.00  parsing_time:                           0.008
% 19.83/3.00  unif_index_cands_time:                  0.
% 19.83/3.00  unif_index_add_time:                    0.
% 19.83/3.00  orderings_time:                         0.
% 19.83/3.00  out_proof_time:                         0.01
% 19.83/3.00  total_time:                             2.264
% 19.83/3.00  num_of_symbols:                         42
% 19.83/3.00  num_of_terms:                           77136
% 19.83/3.00  
% 19.83/3.00  ------ Preprocessing
% 19.83/3.00  
% 19.83/3.00  num_of_splits:                          0
% 19.83/3.00  num_of_split_atoms:                     0
% 19.83/3.00  num_of_reused_defs:                     0
% 19.83/3.00  num_eq_ax_congr_red:                    11
% 19.83/3.00  num_of_sem_filtered_clauses:            1
% 19.83/3.00  num_of_subtypes:                        0
% 19.83/3.00  monotx_restored_types:                  0
% 19.83/3.00  sat_num_of_epr_types:                   0
% 19.83/3.00  sat_num_of_non_cyclic_types:            0
% 19.83/3.00  sat_guarded_non_collapsed_types:        0
% 19.83/3.00  num_pure_diseq_elim:                    0
% 19.83/3.00  simp_replaced_by:                       0
% 19.83/3.00  res_preprocessed:                       69
% 19.83/3.00  prep_upred:                             0
% 19.83/3.00  prep_unflattend:                        6
% 19.83/3.00  smt_new_axioms:                         0
% 19.83/3.00  pred_elim_cands:                        1
% 19.83/3.00  pred_elim:                              2
% 19.83/3.00  pred_elim_cl:                           2
% 19.83/3.00  pred_elim_cycles:                       4
% 19.83/3.00  merged_defs:                            0
% 19.83/3.00  merged_defs_ncl:                        0
% 19.83/3.00  bin_hyper_res:                          0
% 19.83/3.00  prep_cycles:                            4
% 19.83/3.00  pred_elim_time:                         0.001
% 19.83/3.00  splitting_time:                         0.
% 19.83/3.00  sem_filter_time:                        0.
% 19.83/3.00  monotx_time:                            0.001
% 19.83/3.00  subtype_inf_time:                       0.
% 19.83/3.00  
% 19.83/3.00  ------ Problem properties
% 19.83/3.00  
% 19.83/3.00  clauses:                                14
% 19.83/3.00  conjectures:                            2
% 19.83/3.00  epr:                                    1
% 19.83/3.00  horn:                                   13
% 19.83/3.00  ground:                                 2
% 19.83/3.00  unary:                                  11
% 19.83/3.00  binary:                                 3
% 19.83/3.00  lits:                                   17
% 19.83/3.00  lits_eq:                                12
% 19.83/3.00  fd_pure:                                0
% 19.83/3.00  fd_pseudo:                              0
% 19.83/3.00  fd_cond:                                1
% 19.83/3.00  fd_pseudo_cond:                         0
% 19.83/3.00  ac_symbols:                             0
% 19.83/3.00  
% 19.83/3.00  ------ Propositional Solver
% 19.83/3.00  
% 19.83/3.00  prop_solver_calls:                      35
% 19.83/3.00  prop_fast_solver_calls:                 592
% 19.83/3.00  smt_solver_calls:                       0
% 19.83/3.00  smt_fast_solver_calls:                  0
% 19.83/3.00  prop_num_of_clauses:                    14640
% 19.83/3.00  prop_preprocess_simplified:             18392
% 19.83/3.00  prop_fo_subsumed:                       0
% 19.83/3.00  prop_solver_time:                       0.
% 19.83/3.00  smt_solver_time:                        0.
% 19.83/3.00  smt_fast_solver_time:                   0.
% 19.83/3.00  prop_fast_solver_time:                  0.
% 19.83/3.00  prop_unsat_core_time:                   0.001
% 19.83/3.00  
% 19.83/3.00  ------ QBF
% 19.83/3.00  
% 19.83/3.00  qbf_q_res:                              0
% 19.83/3.00  qbf_num_tautologies:                    0
% 19.83/3.00  qbf_prep_cycles:                        0
% 19.83/3.00  
% 19.83/3.00  ------ BMC1
% 19.83/3.00  
% 19.83/3.00  bmc1_current_bound:                     -1
% 19.83/3.00  bmc1_last_solved_bound:                 -1
% 19.83/3.00  bmc1_unsat_core_size:                   -1
% 19.83/3.00  bmc1_unsat_core_parents_size:           -1
% 19.83/3.00  bmc1_merge_next_fun:                    0
% 19.83/3.00  bmc1_unsat_core_clauses_time:           0.
% 19.83/3.00  
% 19.83/3.00  ------ Instantiation
% 19.83/3.00  
% 19.83/3.00  inst_num_of_clauses:                    4561
% 19.83/3.00  inst_num_in_passive:                    2253
% 19.83/3.00  inst_num_in_active:                     1518
% 19.83/3.00  inst_num_in_unprocessed:                791
% 19.83/3.00  inst_num_of_loops:                      1710
% 19.83/3.00  inst_num_of_learning_restarts:          0
% 19.83/3.00  inst_num_moves_active_passive:          188
% 19.83/3.00  inst_lit_activity:                      0
% 19.83/3.00  inst_lit_activity_moves:                0
% 19.83/3.00  inst_num_tautologies:                   0
% 19.83/3.00  inst_num_prop_implied:                  0
% 19.83/3.00  inst_num_existing_simplified:           0
% 19.83/3.00  inst_num_eq_res_simplified:             0
% 19.83/3.00  inst_num_child_elim:                    0
% 19.83/3.00  inst_num_of_dismatching_blockings:      3948
% 19.83/3.00  inst_num_of_non_proper_insts:           5172
% 19.83/3.00  inst_num_of_duplicates:                 0
% 19.83/3.00  inst_inst_num_from_inst_to_res:         0
% 19.83/3.00  inst_dismatching_checking_time:         0.
% 19.83/3.00  
% 19.83/3.00  ------ Resolution
% 19.83/3.00  
% 19.83/3.00  res_num_of_clauses:                     0
% 19.83/3.00  res_num_in_passive:                     0
% 19.83/3.00  res_num_in_active:                      0
% 19.83/3.00  res_num_of_loops:                       73
% 19.83/3.00  res_forward_subset_subsumed:            1073
% 19.83/3.00  res_backward_subset_subsumed:           2
% 19.83/3.00  res_forward_subsumed:                   0
% 19.83/3.00  res_backward_subsumed:                  0
% 19.83/3.00  res_forward_subsumption_resolution:     0
% 19.83/3.00  res_backward_subsumption_resolution:    0
% 19.83/3.00  res_clause_to_clause_subsumption:       84103
% 19.83/3.00  res_orphan_elimination:                 0
% 19.83/3.00  res_tautology_del:                      378
% 19.83/3.00  res_num_eq_res_simplified:              0
% 19.83/3.00  res_num_sel_changes:                    0
% 19.83/3.00  res_moves_from_active_to_pass:          0
% 19.83/3.00  
% 19.83/3.00  ------ Superposition
% 19.83/3.00  
% 19.83/3.00  sup_time_total:                         0.
% 19.83/3.00  sup_time_generating:                    0.
% 19.83/3.00  sup_time_sim_full:                      0.
% 19.83/3.00  sup_time_sim_immed:                     0.
% 19.83/3.00  
% 19.83/3.00  sup_num_of_clauses:                     4146
% 19.83/3.00  sup_num_in_active:                      308
% 19.83/3.00  sup_num_in_passive:                     3838
% 19.83/3.00  sup_num_of_loops:                       340
% 19.83/3.00  sup_fw_superposition:                   12746
% 19.83/3.00  sup_bw_superposition:                   11020
% 19.83/3.00  sup_immediate_simplified:               11190
% 19.83/3.00  sup_given_eliminated:                   4
% 19.83/3.00  comparisons_done:                       0
% 19.83/3.00  comparisons_avoided:                    0
% 19.83/3.00  
% 19.83/3.00  ------ Simplifications
% 19.83/3.00  
% 19.83/3.00  
% 19.83/3.00  sim_fw_subset_subsumed:                 0
% 19.83/3.00  sim_bw_subset_subsumed:                 0
% 19.83/3.00  sim_fw_subsumed:                        3708
% 19.83/3.00  sim_bw_subsumed:                        286
% 19.83/3.00  sim_fw_subsumption_res:                 0
% 19.83/3.00  sim_bw_subsumption_res:                 0
% 19.83/3.00  sim_tautology_del:                      4
% 19.83/3.00  sim_eq_tautology_del:                   3312
% 19.83/3.00  sim_eq_res_simp:                        0
% 19.83/3.00  sim_fw_demodulated:                     6198
% 19.83/3.00  sim_bw_demodulated:                     67
% 19.83/3.00  sim_light_normalised:                   2790
% 19.83/3.00  sim_joinable_taut:                      0
% 19.83/3.00  sim_joinable_simp:                      0
% 19.83/3.00  sim_ac_normalised:                      0
% 19.83/3.00  sim_smt_subsumption:                    0
% 19.83/3.00  
%------------------------------------------------------------------------------
