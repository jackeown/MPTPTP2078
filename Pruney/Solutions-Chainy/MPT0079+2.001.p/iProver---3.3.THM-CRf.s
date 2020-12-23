%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:45 EST 2020

% Result     : Theorem 15.95s
% Output     : CNFRefutation 15.95s
% Verified   : 
% Statistics : Number of formulae       :  163 (1868 expanded)
%              Number of clauses        :  118 ( 691 expanded)
%              Number of leaves         :   17 ( 463 expanded)
%              Depth                    :   21
%              Number of atoms          :  240 (2737 expanded)
%              Number of equality atoms :  195 (2140 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f40,f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f23])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f26])).

fof(f46,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f44,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f35,f40,f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_240,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_394,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_1504,plain,
    ( X0 != k2_xboole_0(X1,sK2)
    | sK2 = X0
    | sK2 != k2_xboole_0(X1,sK2) ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_2016,plain,
    ( k2_xboole_0(sK2,X0) != k2_xboole_0(X0,sK2)
    | sK2 != k2_xboole_0(X0,sK2)
    | sK2 = k2_xboole_0(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_1504])).

cnf(c_73202,plain,
    ( k2_xboole_0(sK2,sK1) != k2_xboole_0(sK1,sK2)
    | sK2 = k2_xboole_0(sK2,sK1)
    | sK2 != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2016])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_98,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_183,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_98,c_16])).

cnf(c_184,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_183])).

cnf(c_707,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_184])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_884,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_707,c_11])).

cnf(c_12,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1566,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0))) = k4_xboole_0(sK1,k4_xboole_0(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_884,c_12])).

cnf(c_887,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_884,c_707])).

cnf(c_1567,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,sK3)) = k2_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1566,c_887])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_630,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_10])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1385,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_630,c_8])).

cnf(c_1387,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1385,c_4])).

cnf(c_1568,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,sK3)) = k4_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_1567,c_1387])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_18,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_574,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_0,c_18])).

cnf(c_7,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_375,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_378,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_375,c_12])).

cnf(c_3483,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,sK2),sK3)),k2_xboole_0(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_378])).

cnf(c_696,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10,c_8])).

cnf(c_4793,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_696,c_1387])).

cnf(c_4796,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4793])).

cnf(c_5010,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_574,c_4796])).

cnf(c_628,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_10])).

cnf(c_2242,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_574,c_628])).

cnf(c_2336,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(k2_xboole_0(sK1,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2242,c_8])).

cnf(c_2339,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_2336,c_1387])).

cnf(c_5045,plain,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_5010,c_2339])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_374,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5498,plain,
    ( r1_tarski(X0,k2_xboole_0(sK1,sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5045,c_374])).

cnf(c_73017,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,sK2),sK3)),sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3483,c_5498])).

cnf(c_73111,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1568,c_73017])).

cnf(c_1563,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK1,k4_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_884,c_12])).

cnf(c_1571,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_1563,c_12])).

cnf(c_1395,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1387,c_0])).

cnf(c_1943,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1395,c_10])).

cnf(c_11068,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK3,X0)) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1571,c_1571,c_1943])).

cnf(c_1948,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1395,c_8])).

cnf(c_1949,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1948,c_1395])).

cnf(c_11069,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK3,X0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_11068,c_1571,c_1949])).

cnf(c_11082,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(superposition,[status(thm)],[c_2242,c_11069])).

cnf(c_797,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_11])).

cnf(c_11104,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(superposition,[status(thm)],[c_11069,c_797])).

cnf(c_14,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_373,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1110,plain,
    ( r1_tarski(X0,k2_xboole_0(sK1,sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_374])).

cnf(c_1556,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_373,c_1110])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_377,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2701,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1556,c_377])).

cnf(c_2240,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_628])).

cnf(c_3799,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_2240])).

cnf(c_4170,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_3799])).

cnf(c_20798,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,k4_xboole_0(sK1,sK2))),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2701,c_4170])).

cnf(c_799,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[status(thm)],[c_184,c_11])).

cnf(c_1222,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_799,c_12])).

cnf(c_1248,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_1222,c_12])).

cnf(c_9853,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1248,c_1248,c_1943])).

cnf(c_9854,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) = sK3 ),
    inference(demodulation,[status(thm)],[c_9853,c_1248,c_1949])).

cnf(c_9881,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK3,sK3)) = k4_xboole_0(k4_xboole_0(sK1,X0),sK3) ),
    inference(superposition,[status(thm)],[c_9854,c_797])).

cnf(c_9892,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0),sK3) = k4_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_9881,c_630,c_1949])).

cnf(c_20838,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20798,c_9854,c_9892])).

cnf(c_73161,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_73111,c_11082,c_11104,c_20838])).

cnf(c_73165,plain,
    ( k2_xboole_0(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_73161,c_377])).

cnf(c_391,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_13317,plain,
    ( sK2 != k2_xboole_0(sK2,X0)
    | sK1 != k2_xboole_0(sK2,X0)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_391])).

cnf(c_39585,plain,
    ( sK2 != k2_xboole_0(sK2,sK1)
    | sK1 != k2_xboole_0(sK2,sK1)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_13317])).

cnf(c_612,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_685,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_954,plain,
    ( k2_xboole_0(X0,sK1) != sK1
    | sK1 = k2_xboole_0(X0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_39584,plain,
    ( k2_xboole_0(sK2,sK1) != sK1
    | sK1 = k2_xboole_0(sK2,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_4850,plain,
    ( k2_xboole_0(sK2,X0) = k2_xboole_0(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_25220,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_4850])).

cnf(c_395,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_411,plain,
    ( k2_xboole_0(X0,sK2) != sK2
    | sK2 = k2_xboole_0(X0,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_25198,plain,
    ( k2_xboole_0(sK1,sK2) != sK2
    | sK2 = k2_xboole_0(sK1,sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_411])).

cnf(c_814,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_373])).

cnf(c_1106,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_374])).

cnf(c_10873,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_814,c_1106])).

cnf(c_813,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_574,c_10])).

cnf(c_1234,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_813,c_12])).

cnf(c_1386,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_630,c_12])).

cnf(c_7352,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(sK2,k4_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_1234,c_1386])).

cnf(c_7383,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_7352,c_12])).

cnf(c_7393,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(X0,sK2)) ),
    inference(demodulation,[status(thm)],[c_7383,c_7352])).

cnf(c_1241,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_12,c_8])).

cnf(c_1242,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1241,c_630])).

cnf(c_7394,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7393,c_12,c_630,c_1242,c_1949])).

cnf(c_7395,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_7394,c_1949])).

cnf(c_7396,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = sK2 ),
    inference(demodulation,[status(thm)],[c_7395,c_7352])).

cnf(c_7436,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_7383,c_7396])).

cnf(c_7437,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = sK2 ),
    inference(demodulation,[status(thm)],[c_7436,c_12,c_1242,c_7395])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_188,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_98,c_17])).

cnf(c_189,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_800,plain,
    ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_189,c_11])).

cnf(c_7674,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_7437,c_800])).

cnf(c_10903,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10873,c_7674])).

cnf(c_19094,plain,
    ( k2_xboole_0(sK2,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_10903,c_377])).

cnf(c_239,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_657,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_398,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_15,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73202,c_73165,c_39585,c_39584,c_25220,c_25198,c_19094,c_657,c_398,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:30:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.95/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.95/2.49  
% 15.95/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.95/2.49  
% 15.95/2.49  ------  iProver source info
% 15.95/2.49  
% 15.95/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.95/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.95/2.49  git: non_committed_changes: false
% 15.95/2.49  git: last_make_outside_of_git: false
% 15.95/2.49  
% 15.95/2.49  ------ 
% 15.95/2.49  
% 15.95/2.49  ------ Input Options
% 15.95/2.49  
% 15.95/2.49  --out_options                           all
% 15.95/2.49  --tptp_safe_out                         true
% 15.95/2.49  --problem_path                          ""
% 15.95/2.49  --include_path                          ""
% 15.95/2.49  --clausifier                            res/vclausify_rel
% 15.95/2.49  --clausifier_options                    ""
% 15.95/2.49  --stdin                                 false
% 15.95/2.49  --stats_out                             all
% 15.95/2.49  
% 15.95/2.49  ------ General Options
% 15.95/2.49  
% 15.95/2.49  --fof                                   false
% 15.95/2.49  --time_out_real                         305.
% 15.95/2.49  --time_out_virtual                      -1.
% 15.95/2.49  --symbol_type_check                     false
% 15.95/2.49  --clausify_out                          false
% 15.95/2.49  --sig_cnt_out                           false
% 15.95/2.49  --trig_cnt_out                          false
% 15.95/2.49  --trig_cnt_out_tolerance                1.
% 15.95/2.49  --trig_cnt_out_sk_spl                   false
% 15.95/2.49  --abstr_cl_out                          false
% 15.95/2.49  
% 15.95/2.49  ------ Global Options
% 15.95/2.49  
% 15.95/2.49  --schedule                              default
% 15.95/2.49  --add_important_lit                     false
% 15.95/2.49  --prop_solver_per_cl                    1000
% 15.95/2.49  --min_unsat_core                        false
% 15.95/2.49  --soft_assumptions                      false
% 15.95/2.49  --soft_lemma_size                       3
% 15.95/2.49  --prop_impl_unit_size                   0
% 15.95/2.49  --prop_impl_unit                        []
% 15.95/2.49  --share_sel_clauses                     true
% 15.95/2.49  --reset_solvers                         false
% 15.95/2.49  --bc_imp_inh                            [conj_cone]
% 15.95/2.49  --conj_cone_tolerance                   3.
% 15.95/2.49  --extra_neg_conj                        none
% 15.95/2.49  --large_theory_mode                     true
% 15.95/2.49  --prolific_symb_bound                   200
% 15.95/2.49  --lt_threshold                          2000
% 15.95/2.49  --clause_weak_htbl                      true
% 15.95/2.49  --gc_record_bc_elim                     false
% 15.95/2.49  
% 15.95/2.49  ------ Preprocessing Options
% 15.95/2.49  
% 15.95/2.49  --preprocessing_flag                    true
% 15.95/2.49  --time_out_prep_mult                    0.1
% 15.95/2.49  --splitting_mode                        input
% 15.95/2.49  --splitting_grd                         true
% 15.95/2.49  --splitting_cvd                         false
% 15.95/2.49  --splitting_cvd_svl                     false
% 15.95/2.49  --splitting_nvd                         32
% 15.95/2.49  --sub_typing                            true
% 15.95/2.49  --prep_gs_sim                           true
% 15.95/2.49  --prep_unflatten                        true
% 15.95/2.49  --prep_res_sim                          true
% 15.95/2.49  --prep_upred                            true
% 15.95/2.49  --prep_sem_filter                       exhaustive
% 15.95/2.49  --prep_sem_filter_out                   false
% 15.95/2.49  --pred_elim                             true
% 15.95/2.49  --res_sim_input                         true
% 15.95/2.49  --eq_ax_congr_red                       true
% 15.95/2.49  --pure_diseq_elim                       true
% 15.95/2.49  --brand_transform                       false
% 15.95/2.49  --non_eq_to_eq                          false
% 15.95/2.49  --prep_def_merge                        true
% 15.95/2.49  --prep_def_merge_prop_impl              false
% 15.95/2.49  --prep_def_merge_mbd                    true
% 15.95/2.49  --prep_def_merge_tr_red                 false
% 15.95/2.49  --prep_def_merge_tr_cl                  false
% 15.95/2.49  --smt_preprocessing                     true
% 15.95/2.49  --smt_ac_axioms                         fast
% 15.95/2.49  --preprocessed_out                      false
% 15.95/2.49  --preprocessed_stats                    false
% 15.95/2.49  
% 15.95/2.49  ------ Abstraction refinement Options
% 15.95/2.49  
% 15.95/2.49  --abstr_ref                             []
% 15.95/2.49  --abstr_ref_prep                        false
% 15.95/2.49  --abstr_ref_until_sat                   false
% 15.95/2.49  --abstr_ref_sig_restrict                funpre
% 15.95/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.95/2.49  --abstr_ref_under                       []
% 15.95/2.49  
% 15.95/2.49  ------ SAT Options
% 15.95/2.49  
% 15.95/2.49  --sat_mode                              false
% 15.95/2.49  --sat_fm_restart_options                ""
% 15.95/2.49  --sat_gr_def                            false
% 15.95/2.49  --sat_epr_types                         true
% 15.95/2.49  --sat_non_cyclic_types                  false
% 15.95/2.49  --sat_finite_models                     false
% 15.95/2.49  --sat_fm_lemmas                         false
% 15.95/2.49  --sat_fm_prep                           false
% 15.95/2.49  --sat_fm_uc_incr                        true
% 15.95/2.49  --sat_out_model                         small
% 15.95/2.49  --sat_out_clauses                       false
% 15.95/2.49  
% 15.95/2.49  ------ QBF Options
% 15.95/2.49  
% 15.95/2.49  --qbf_mode                              false
% 15.95/2.49  --qbf_elim_univ                         false
% 15.95/2.49  --qbf_dom_inst                          none
% 15.95/2.49  --qbf_dom_pre_inst                      false
% 15.95/2.49  --qbf_sk_in                             false
% 15.95/2.49  --qbf_pred_elim                         true
% 15.95/2.49  --qbf_split                             512
% 15.95/2.49  
% 15.95/2.49  ------ BMC1 Options
% 15.95/2.49  
% 15.95/2.49  --bmc1_incremental                      false
% 15.95/2.49  --bmc1_axioms                           reachable_all
% 15.95/2.49  --bmc1_min_bound                        0
% 15.95/2.49  --bmc1_max_bound                        -1
% 15.95/2.49  --bmc1_max_bound_default                -1
% 15.95/2.49  --bmc1_symbol_reachability              true
% 15.95/2.49  --bmc1_property_lemmas                  false
% 15.95/2.49  --bmc1_k_induction                      false
% 15.95/2.49  --bmc1_non_equiv_states                 false
% 15.95/2.49  --bmc1_deadlock                         false
% 15.95/2.49  --bmc1_ucm                              false
% 15.95/2.49  --bmc1_add_unsat_core                   none
% 15.95/2.49  --bmc1_unsat_core_children              false
% 15.95/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.95/2.49  --bmc1_out_stat                         full
% 15.95/2.49  --bmc1_ground_init                      false
% 15.95/2.49  --bmc1_pre_inst_next_state              false
% 15.95/2.49  --bmc1_pre_inst_state                   false
% 15.95/2.49  --bmc1_pre_inst_reach_state             false
% 15.95/2.49  --bmc1_out_unsat_core                   false
% 15.95/2.49  --bmc1_aig_witness_out                  false
% 15.95/2.49  --bmc1_verbose                          false
% 15.95/2.49  --bmc1_dump_clauses_tptp                false
% 15.95/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.95/2.49  --bmc1_dump_file                        -
% 15.95/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.95/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.95/2.49  --bmc1_ucm_extend_mode                  1
% 15.95/2.49  --bmc1_ucm_init_mode                    2
% 15.95/2.49  --bmc1_ucm_cone_mode                    none
% 15.95/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.95/2.49  --bmc1_ucm_relax_model                  4
% 15.95/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.95/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.95/2.49  --bmc1_ucm_layered_model                none
% 15.95/2.49  --bmc1_ucm_max_lemma_size               10
% 15.95/2.49  
% 15.95/2.49  ------ AIG Options
% 15.95/2.49  
% 15.95/2.49  --aig_mode                              false
% 15.95/2.49  
% 15.95/2.49  ------ Instantiation Options
% 15.95/2.49  
% 15.95/2.49  --instantiation_flag                    true
% 15.95/2.49  --inst_sos_flag                         true
% 15.95/2.49  --inst_sos_phase                        true
% 15.95/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.95/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.95/2.49  --inst_lit_sel_side                     num_symb
% 15.95/2.49  --inst_solver_per_active                1400
% 15.95/2.49  --inst_solver_calls_frac                1.
% 15.95/2.49  --inst_passive_queue_type               priority_queues
% 15.95/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.95/2.49  --inst_passive_queues_freq              [25;2]
% 15.95/2.49  --inst_dismatching                      true
% 15.95/2.49  --inst_eager_unprocessed_to_passive     true
% 15.95/2.49  --inst_prop_sim_given                   true
% 15.95/2.49  --inst_prop_sim_new                     false
% 15.95/2.49  --inst_subs_new                         false
% 15.95/2.49  --inst_eq_res_simp                      false
% 15.95/2.49  --inst_subs_given                       false
% 15.95/2.49  --inst_orphan_elimination               true
% 15.95/2.49  --inst_learning_loop_flag               true
% 15.95/2.49  --inst_learning_start                   3000
% 15.95/2.49  --inst_learning_factor                  2
% 15.95/2.49  --inst_start_prop_sim_after_learn       3
% 15.95/2.49  --inst_sel_renew                        solver
% 15.95/2.49  --inst_lit_activity_flag                true
% 15.95/2.49  --inst_restr_to_given                   false
% 15.95/2.49  --inst_activity_threshold               500
% 15.95/2.49  --inst_out_proof                        true
% 15.95/2.49  
% 15.95/2.49  ------ Resolution Options
% 15.95/2.49  
% 15.95/2.49  --resolution_flag                       true
% 15.95/2.49  --res_lit_sel                           adaptive
% 15.95/2.49  --res_lit_sel_side                      none
% 15.95/2.49  --res_ordering                          kbo
% 15.95/2.49  --res_to_prop_solver                    active
% 15.95/2.49  --res_prop_simpl_new                    false
% 15.95/2.49  --res_prop_simpl_given                  true
% 15.95/2.49  --res_passive_queue_type                priority_queues
% 15.95/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.95/2.49  --res_passive_queues_freq               [15;5]
% 15.95/2.49  --res_forward_subs                      full
% 15.95/2.49  --res_backward_subs                     full
% 15.95/2.49  --res_forward_subs_resolution           true
% 15.95/2.49  --res_backward_subs_resolution          true
% 15.95/2.49  --res_orphan_elimination                true
% 15.95/2.49  --res_time_limit                        2.
% 15.95/2.49  --res_out_proof                         true
% 15.95/2.49  
% 15.95/2.49  ------ Superposition Options
% 15.95/2.49  
% 15.95/2.49  --superposition_flag                    true
% 15.95/2.49  --sup_passive_queue_type                priority_queues
% 15.95/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.95/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.95/2.49  --demod_completeness_check              fast
% 15.95/2.49  --demod_use_ground                      true
% 15.95/2.49  --sup_to_prop_solver                    passive
% 15.95/2.49  --sup_prop_simpl_new                    true
% 15.95/2.49  --sup_prop_simpl_given                  true
% 15.95/2.49  --sup_fun_splitting                     true
% 15.95/2.49  --sup_smt_interval                      50000
% 15.95/2.49  
% 15.95/2.49  ------ Superposition Simplification Setup
% 15.95/2.49  
% 15.95/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.95/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.95/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.95/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.95/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.95/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.95/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.95/2.49  --sup_immed_triv                        [TrivRules]
% 15.95/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.95/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.95/2.49  --sup_immed_bw_main                     []
% 15.95/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.95/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.95/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.95/2.49  --sup_input_bw                          []
% 15.95/2.49  
% 15.95/2.49  ------ Combination Options
% 15.95/2.49  
% 15.95/2.49  --comb_res_mult                         3
% 15.95/2.49  --comb_sup_mult                         2
% 15.95/2.49  --comb_inst_mult                        10
% 15.95/2.49  
% 15.95/2.49  ------ Debug Options
% 15.95/2.49  
% 15.95/2.49  --dbg_backtrace                         false
% 15.95/2.49  --dbg_dump_prop_clauses                 false
% 15.95/2.49  --dbg_dump_prop_clauses_file            -
% 15.95/2.49  --dbg_out_stat                          false
% 15.95/2.49  ------ Parsing...
% 15.95/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.95/2.49  
% 15.95/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 15.95/2.49  
% 15.95/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.95/2.49  
% 15.95/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.95/2.49  ------ Proving...
% 15.95/2.49  ------ Problem Properties 
% 15.95/2.49  
% 15.95/2.49  
% 15.95/2.49  clauses                                 19
% 15.95/2.49  conjectures                             2
% 15.95/2.49  EPR                                     3
% 15.95/2.49  Horn                                    19
% 15.95/2.49  unary                                   14
% 15.95/2.49  binary                                  2
% 15.95/2.49  lits                                    28
% 15.95/2.49  lits eq                                 16
% 15.95/2.49  fd_pure                                 0
% 15.95/2.49  fd_pseudo                               0
% 15.95/2.49  fd_cond                                 3
% 15.95/2.49  fd_pseudo_cond                          0
% 15.95/2.49  AC symbols                              0
% 15.95/2.49  
% 15.95/2.49  ------ Schedule dynamic 5 is on 
% 15.95/2.49  
% 15.95/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.95/2.49  
% 15.95/2.49  
% 15.95/2.49  ------ 
% 15.95/2.49  Current options:
% 15.95/2.49  ------ 
% 15.95/2.49  
% 15.95/2.49  ------ Input Options
% 15.95/2.49  
% 15.95/2.49  --out_options                           all
% 15.95/2.49  --tptp_safe_out                         true
% 15.95/2.49  --problem_path                          ""
% 15.95/2.49  --include_path                          ""
% 15.95/2.49  --clausifier                            res/vclausify_rel
% 15.95/2.49  --clausifier_options                    ""
% 15.95/2.49  --stdin                                 false
% 15.95/2.49  --stats_out                             all
% 15.95/2.49  
% 15.95/2.49  ------ General Options
% 15.95/2.49  
% 15.95/2.49  --fof                                   false
% 15.95/2.49  --time_out_real                         305.
% 15.95/2.49  --time_out_virtual                      -1.
% 15.95/2.49  --symbol_type_check                     false
% 15.95/2.49  --clausify_out                          false
% 15.95/2.49  --sig_cnt_out                           false
% 15.95/2.49  --trig_cnt_out                          false
% 15.95/2.49  --trig_cnt_out_tolerance                1.
% 15.95/2.49  --trig_cnt_out_sk_spl                   false
% 15.95/2.49  --abstr_cl_out                          false
% 15.95/2.49  
% 15.95/2.49  ------ Global Options
% 15.95/2.49  
% 15.95/2.49  --schedule                              default
% 15.95/2.49  --add_important_lit                     false
% 15.95/2.49  --prop_solver_per_cl                    1000
% 15.95/2.49  --min_unsat_core                        false
% 15.95/2.49  --soft_assumptions                      false
% 15.95/2.49  --soft_lemma_size                       3
% 15.95/2.49  --prop_impl_unit_size                   0
% 15.95/2.49  --prop_impl_unit                        []
% 15.95/2.49  --share_sel_clauses                     true
% 15.95/2.49  --reset_solvers                         false
% 15.95/2.49  --bc_imp_inh                            [conj_cone]
% 15.95/2.49  --conj_cone_tolerance                   3.
% 15.95/2.49  --extra_neg_conj                        none
% 15.95/2.49  --large_theory_mode                     true
% 15.95/2.49  --prolific_symb_bound                   200
% 15.95/2.49  --lt_threshold                          2000
% 15.95/2.49  --clause_weak_htbl                      true
% 15.95/2.49  --gc_record_bc_elim                     false
% 15.95/2.49  
% 15.95/2.49  ------ Preprocessing Options
% 15.95/2.49  
% 15.95/2.49  --preprocessing_flag                    true
% 15.95/2.49  --time_out_prep_mult                    0.1
% 15.95/2.49  --splitting_mode                        input
% 15.95/2.49  --splitting_grd                         true
% 15.95/2.49  --splitting_cvd                         false
% 15.95/2.49  --splitting_cvd_svl                     false
% 15.95/2.49  --splitting_nvd                         32
% 15.95/2.49  --sub_typing                            true
% 15.95/2.49  --prep_gs_sim                           true
% 15.95/2.49  --prep_unflatten                        true
% 15.95/2.49  --prep_res_sim                          true
% 15.95/2.49  --prep_upred                            true
% 15.95/2.49  --prep_sem_filter                       exhaustive
% 15.95/2.49  --prep_sem_filter_out                   false
% 15.95/2.49  --pred_elim                             true
% 15.95/2.49  --res_sim_input                         true
% 15.95/2.49  --eq_ax_congr_red                       true
% 15.95/2.49  --pure_diseq_elim                       true
% 15.95/2.49  --brand_transform                       false
% 15.95/2.49  --non_eq_to_eq                          false
% 15.95/2.49  --prep_def_merge                        true
% 15.95/2.49  --prep_def_merge_prop_impl              false
% 15.95/2.49  --prep_def_merge_mbd                    true
% 15.95/2.49  --prep_def_merge_tr_red                 false
% 15.95/2.49  --prep_def_merge_tr_cl                  false
% 15.95/2.49  --smt_preprocessing                     true
% 15.95/2.49  --smt_ac_axioms                         fast
% 15.95/2.49  --preprocessed_out                      false
% 15.95/2.49  --preprocessed_stats                    false
% 15.95/2.49  
% 15.95/2.49  ------ Abstraction refinement Options
% 15.95/2.49  
% 15.95/2.49  --abstr_ref                             []
% 15.95/2.49  --abstr_ref_prep                        false
% 15.95/2.49  --abstr_ref_until_sat                   false
% 15.95/2.49  --abstr_ref_sig_restrict                funpre
% 15.95/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.95/2.49  --abstr_ref_under                       []
% 15.95/2.49  
% 15.95/2.49  ------ SAT Options
% 15.95/2.49  
% 15.95/2.49  --sat_mode                              false
% 15.95/2.49  --sat_fm_restart_options                ""
% 15.95/2.49  --sat_gr_def                            false
% 15.95/2.49  --sat_epr_types                         true
% 15.95/2.49  --sat_non_cyclic_types                  false
% 15.95/2.49  --sat_finite_models                     false
% 15.95/2.49  --sat_fm_lemmas                         false
% 15.95/2.49  --sat_fm_prep                           false
% 15.95/2.49  --sat_fm_uc_incr                        true
% 15.95/2.49  --sat_out_model                         small
% 15.95/2.49  --sat_out_clauses                       false
% 15.95/2.49  
% 15.95/2.49  ------ QBF Options
% 15.95/2.49  
% 15.95/2.49  --qbf_mode                              false
% 15.95/2.49  --qbf_elim_univ                         false
% 15.95/2.49  --qbf_dom_inst                          none
% 15.95/2.49  --qbf_dom_pre_inst                      false
% 15.95/2.49  --qbf_sk_in                             false
% 15.95/2.49  --qbf_pred_elim                         true
% 15.95/2.49  --qbf_split                             512
% 15.95/2.49  
% 15.95/2.49  ------ BMC1 Options
% 15.95/2.49  
% 15.95/2.49  --bmc1_incremental                      false
% 15.95/2.49  --bmc1_axioms                           reachable_all
% 15.95/2.49  --bmc1_min_bound                        0
% 15.95/2.49  --bmc1_max_bound                        -1
% 15.95/2.49  --bmc1_max_bound_default                -1
% 15.95/2.49  --bmc1_symbol_reachability              true
% 15.95/2.49  --bmc1_property_lemmas                  false
% 15.95/2.49  --bmc1_k_induction                      false
% 15.95/2.49  --bmc1_non_equiv_states                 false
% 15.95/2.49  --bmc1_deadlock                         false
% 15.95/2.49  --bmc1_ucm                              false
% 15.95/2.49  --bmc1_add_unsat_core                   none
% 15.95/2.49  --bmc1_unsat_core_children              false
% 15.95/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.95/2.49  --bmc1_out_stat                         full
% 15.95/2.49  --bmc1_ground_init                      false
% 15.95/2.49  --bmc1_pre_inst_next_state              false
% 15.95/2.49  --bmc1_pre_inst_state                   false
% 15.95/2.49  --bmc1_pre_inst_reach_state             false
% 15.95/2.49  --bmc1_out_unsat_core                   false
% 15.95/2.49  --bmc1_aig_witness_out                  false
% 15.95/2.49  --bmc1_verbose                          false
% 15.95/2.49  --bmc1_dump_clauses_tptp                false
% 15.95/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.95/2.49  --bmc1_dump_file                        -
% 15.95/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.95/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.95/2.49  --bmc1_ucm_extend_mode                  1
% 15.95/2.49  --bmc1_ucm_init_mode                    2
% 15.95/2.49  --bmc1_ucm_cone_mode                    none
% 15.95/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.95/2.49  --bmc1_ucm_relax_model                  4
% 15.95/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.95/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.95/2.49  --bmc1_ucm_layered_model                none
% 15.95/2.49  --bmc1_ucm_max_lemma_size               10
% 15.95/2.49  
% 15.95/2.49  ------ AIG Options
% 15.95/2.49  
% 15.95/2.49  --aig_mode                              false
% 15.95/2.49  
% 15.95/2.49  ------ Instantiation Options
% 15.95/2.49  
% 15.95/2.49  --instantiation_flag                    true
% 15.95/2.49  --inst_sos_flag                         true
% 15.95/2.49  --inst_sos_phase                        true
% 15.95/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.95/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.95/2.49  --inst_lit_sel_side                     none
% 15.95/2.49  --inst_solver_per_active                1400
% 15.95/2.49  --inst_solver_calls_frac                1.
% 15.95/2.49  --inst_passive_queue_type               priority_queues
% 15.95/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.95/2.49  --inst_passive_queues_freq              [25;2]
% 15.95/2.49  --inst_dismatching                      true
% 15.95/2.49  --inst_eager_unprocessed_to_passive     true
% 15.95/2.49  --inst_prop_sim_given                   true
% 15.95/2.49  --inst_prop_sim_new                     false
% 15.95/2.49  --inst_subs_new                         false
% 15.95/2.49  --inst_eq_res_simp                      false
% 15.95/2.49  --inst_subs_given                       false
% 15.95/2.49  --inst_orphan_elimination               true
% 15.95/2.49  --inst_learning_loop_flag               true
% 15.95/2.49  --inst_learning_start                   3000
% 15.95/2.49  --inst_learning_factor                  2
% 15.95/2.49  --inst_start_prop_sim_after_learn       3
% 15.95/2.49  --inst_sel_renew                        solver
% 15.95/2.49  --inst_lit_activity_flag                true
% 15.95/2.49  --inst_restr_to_given                   false
% 15.95/2.49  --inst_activity_threshold               500
% 15.95/2.49  --inst_out_proof                        true
% 15.95/2.49  
% 15.95/2.49  ------ Resolution Options
% 15.95/2.49  
% 15.95/2.49  --resolution_flag                       false
% 15.95/2.49  --res_lit_sel                           adaptive
% 15.95/2.49  --res_lit_sel_side                      none
% 15.95/2.49  --res_ordering                          kbo
% 15.95/2.49  --res_to_prop_solver                    active
% 15.95/2.49  --res_prop_simpl_new                    false
% 15.95/2.49  --res_prop_simpl_given                  true
% 15.95/2.49  --res_passive_queue_type                priority_queues
% 15.95/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.95/2.49  --res_passive_queues_freq               [15;5]
% 15.95/2.49  --res_forward_subs                      full
% 15.95/2.49  --res_backward_subs                     full
% 15.95/2.49  --res_forward_subs_resolution           true
% 15.95/2.49  --res_backward_subs_resolution          true
% 15.95/2.49  --res_orphan_elimination                true
% 15.95/2.49  --res_time_limit                        2.
% 15.95/2.49  --res_out_proof                         true
% 15.95/2.49  
% 15.95/2.49  ------ Superposition Options
% 15.95/2.49  
% 15.95/2.49  --superposition_flag                    true
% 15.95/2.49  --sup_passive_queue_type                priority_queues
% 15.95/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.95/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.95/2.49  --demod_completeness_check              fast
% 15.95/2.49  --demod_use_ground                      true
% 15.95/2.49  --sup_to_prop_solver                    passive
% 15.95/2.49  --sup_prop_simpl_new                    true
% 15.95/2.49  --sup_prop_simpl_given                  true
% 15.95/2.49  --sup_fun_splitting                     true
% 15.95/2.49  --sup_smt_interval                      50000
% 15.95/2.49  
% 15.95/2.49  ------ Superposition Simplification Setup
% 15.95/2.49  
% 15.95/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.95/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.95/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.95/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.95/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.95/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.95/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.95/2.49  --sup_immed_triv                        [TrivRules]
% 15.95/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.95/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.95/2.49  --sup_immed_bw_main                     []
% 15.95/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.95/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.95/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.95/2.49  --sup_input_bw                          []
% 15.95/2.49  
% 15.95/2.49  ------ Combination Options
% 15.95/2.49  
% 15.95/2.49  --comb_res_mult                         3
% 15.95/2.49  --comb_sup_mult                         2
% 15.95/2.49  --comb_inst_mult                        10
% 15.95/2.49  
% 15.95/2.49  ------ Debug Options
% 15.95/2.49  
% 15.95/2.49  --dbg_backtrace                         false
% 15.95/2.49  --dbg_dump_prop_clauses                 false
% 15.95/2.49  --dbg_dump_prop_clauses_file            -
% 15.95/2.49  --dbg_out_stat                          false
% 15.95/2.49  
% 15.95/2.49  
% 15.95/2.49  
% 15.95/2.49  
% 15.95/2.49  ------ Proving...
% 15.95/2.49  
% 15.95/2.49  
% 15.95/2.49  % SZS status Theorem for theBenchmark.p
% 15.95/2.49  
% 15.95/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.95/2.49  
% 15.95/2.49  fof(f2,axiom,(
% 15.95/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.95/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.95/2.49  
% 15.95/2.49  fof(f29,plain,(
% 15.95/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.95/2.49    inference(cnf_transformation,[],[f2])).
% 15.95/2.49  
% 15.95/2.49  fof(f12,axiom,(
% 15.95/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.95/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.95/2.49  
% 15.95/2.49  fof(f40,plain,(
% 15.95/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.95/2.49    inference(cnf_transformation,[],[f12])).
% 15.95/2.49  
% 15.95/2.49  fof(f48,plain,(
% 15.95/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 15.95/2.49    inference(definition_unfolding,[],[f29,f40,f40])).
% 15.95/2.49  
% 15.95/2.49  fof(f3,axiom,(
% 15.95/2.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.95/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.95/2.49  
% 15.95/2.49  fof(f25,plain,(
% 15.95/2.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 15.95/2.49    inference(nnf_transformation,[],[f3])).
% 15.95/2.49  
% 15.95/2.49  fof(f30,plain,(
% 15.95/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 15.95/2.49    inference(cnf_transformation,[],[f25])).
% 15.95/2.49  
% 15.95/2.49  fof(f50,plain,(
% 15.95/2.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 15.95/2.49    inference(definition_unfolding,[],[f30,f40])).
% 15.95/2.49  
% 15.95/2.49  fof(f16,conjecture,(
% 15.95/2.49    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 15.95/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.95/2.49  
% 15.95/2.49  fof(f17,negated_conjecture,(
% 15.95/2.49    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 15.95/2.49    inference(negated_conjecture,[],[f16])).
% 15.95/2.49  
% 15.95/2.49  fof(f23,plain,(
% 15.95/2.49    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 15.95/2.49    inference(ennf_transformation,[],[f17])).
% 15.95/2.49  
% 15.95/2.49  fof(f24,plain,(
% 15.95/2.49    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 15.95/2.49    inference(flattening,[],[f23])).
% 15.95/2.49  
% 15.95/2.49  fof(f26,plain,(
% 15.95/2.49    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 15.95/2.49    introduced(choice_axiom,[])).
% 15.95/2.49  
% 15.95/2.49  fof(f27,plain,(
% 15.95/2.49    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 15.95/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f26])).
% 15.95/2.49  
% 15.95/2.49  fof(f46,plain,(
% 15.95/2.49    r1_xboole_0(sK3,sK1)),
% 15.95/2.49    inference(cnf_transformation,[],[f27])).
% 15.95/2.49  
% 15.95/2.49  fof(f11,axiom,(
% 15.95/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.95/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.95/2.49  
% 15.95/2.49  fof(f39,plain,(
% 15.95/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.95/2.49    inference(cnf_transformation,[],[f11])).
% 15.95/2.49  
% 15.95/2.49  fof(f53,plain,(
% 15.95/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 15.95/2.49    inference(definition_unfolding,[],[f39,f40])).
% 15.95/2.49  
% 15.95/2.49  fof(f13,axiom,(
% 15.95/2.49    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 15.95/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.95/2.49  
% 15.95/2.49  fof(f41,plain,(
% 15.95/2.49    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 15.95/2.49    inference(cnf_transformation,[],[f13])).
% 15.95/2.49  
% 15.95/2.49  fof(f54,plain,(
% 15.95/2.49    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 15.95/2.49    inference(definition_unfolding,[],[f41,f40])).
% 15.95/2.49  
% 15.95/2.49  fof(f4,axiom,(
% 15.95/2.49    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 15.95/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.95/2.49  
% 15.95/2.49  fof(f18,plain,(
% 15.95/2.49    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 15.95/2.49    inference(rectify,[],[f4])).
% 15.95/2.49  
% 15.95/2.49  fof(f32,plain,(
% 15.95/2.49    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 15.95/2.49    inference(cnf_transformation,[],[f18])).
% 15.95/2.49  
% 15.95/2.49  fof(f10,axiom,(
% 15.95/2.49    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 15.95/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.95/2.49  
% 15.95/2.49  fof(f38,plain,(
% 15.95/2.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 15.95/2.49    inference(cnf_transformation,[],[f10])).
% 15.95/2.49  
% 15.95/2.49  fof(f8,axiom,(
% 15.95/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 15.95/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.95/2.49  
% 15.95/2.49  fof(f36,plain,(
% 15.95/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 15.95/2.49    inference(cnf_transformation,[],[f8])).
% 15.95/2.49  
% 15.95/2.49  fof(f1,axiom,(
% 15.95/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.95/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.95/2.49  
% 15.95/2.49  fof(f28,plain,(
% 15.95/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.95/2.49    inference(cnf_transformation,[],[f1])).
% 15.95/2.49  
% 15.95/2.49  fof(f44,plain,(
% 15.95/2.49    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 15.95/2.49    inference(cnf_transformation,[],[f27])).
% 15.95/2.49  
% 15.95/2.49  fof(f7,axiom,(
% 15.95/2.49    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 15.95/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.95/2.49  
% 15.95/2.49  fof(f35,plain,(
% 15.95/2.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 15.95/2.49    inference(cnf_transformation,[],[f7])).
% 15.95/2.49  
% 15.95/2.49  fof(f52,plain,(
% 15.95/2.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2))) )),
% 15.95/2.49    inference(definition_unfolding,[],[f35,f40,f40])).
% 15.95/2.49  
% 15.95/2.49  fof(f9,axiom,(
% 15.95/2.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 15.95/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.95/2.49  
% 15.95/2.49  fof(f20,plain,(
% 15.95/2.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 15.95/2.49    inference(ennf_transformation,[],[f9])).
% 15.95/2.49  
% 15.95/2.49  fof(f37,plain,(
% 15.95/2.49    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 15.95/2.49    inference(cnf_transformation,[],[f20])).
% 15.95/2.49  
% 15.95/2.49  fof(f15,axiom,(
% 15.95/2.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 15.95/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.95/2.49  
% 15.95/2.49  fof(f43,plain,(
% 15.95/2.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 15.95/2.49    inference(cnf_transformation,[],[f15])).
% 15.95/2.49  
% 15.95/2.49  fof(f5,axiom,(
% 15.95/2.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.95/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.95/2.49  
% 15.95/2.49  fof(f19,plain,(
% 15.95/2.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.95/2.49    inference(ennf_transformation,[],[f5])).
% 15.95/2.49  
% 15.95/2.49  fof(f33,plain,(
% 15.95/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.95/2.49    inference(cnf_transformation,[],[f19])).
% 15.95/2.49  
% 15.95/2.49  fof(f45,plain,(
% 15.95/2.49    r1_xboole_0(sK2,sK0)),
% 15.95/2.49    inference(cnf_transformation,[],[f27])).
% 15.95/2.49  
% 15.95/2.49  fof(f47,plain,(
% 15.95/2.49    sK1 != sK2),
% 15.95/2.49    inference(cnf_transformation,[],[f27])).
% 15.95/2.49  
% 15.95/2.49  cnf(c_240,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_394,plain,
% 15.95/2.49      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_240]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1504,plain,
% 15.95/2.49      ( X0 != k2_xboole_0(X1,sK2)
% 15.95/2.49      | sK2 = X0
% 15.95/2.49      | sK2 != k2_xboole_0(X1,sK2) ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_394]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_2016,plain,
% 15.95/2.49      ( k2_xboole_0(sK2,X0) != k2_xboole_0(X0,sK2)
% 15.95/2.49      | sK2 != k2_xboole_0(X0,sK2)
% 15.95/2.49      | sK2 = k2_xboole_0(sK2,X0) ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_1504]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_73202,plain,
% 15.95/2.49      ( k2_xboole_0(sK2,sK1) != k2_xboole_0(sK1,sK2)
% 15.95/2.49      | sK2 = k2_xboole_0(sK2,sK1)
% 15.95/2.49      | sK2 != k2_xboole_0(sK1,sK2) ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_2016]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1,plain,
% 15.95/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 15.95/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_3,plain,
% 15.95/2.49      ( ~ r1_xboole_0(X0,X1)
% 15.95/2.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.95/2.49      inference(cnf_transformation,[],[f50]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_98,plain,
% 15.95/2.49      ( ~ r1_xboole_0(X0,X1)
% 15.95/2.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.95/2.49      inference(prop_impl,[status(thm)],[c_3]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_16,negated_conjecture,
% 15.95/2.49      ( r1_xboole_0(sK3,sK1) ),
% 15.95/2.49      inference(cnf_transformation,[],[f46]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_183,plain,
% 15.95/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 15.95/2.49      | sK3 != X0
% 15.95/2.49      | sK1 != X1 ),
% 15.95/2.49      inference(resolution_lifted,[status(thm)],[c_98,c_16]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_184,plain,
% 15.95/2.49      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 15.95/2.49      inference(unflattening,[status(thm)],[c_183]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_707,plain,
% 15.95/2.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_1,c_184]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_11,plain,
% 15.95/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 15.95/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_884,plain,
% 15.95/2.49      ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,sK3) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_707,c_11]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_12,plain,
% 15.95/2.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 15.95/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1566,plain,
% 15.95/2.49      ( k2_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0))) = k4_xboole_0(sK1,k4_xboole_0(X0,sK3)) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_884,c_12]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_887,plain,
% 15.95/2.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) = k1_xboole_0 ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_884,c_707]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1567,plain,
% 15.95/2.49      ( k4_xboole_0(sK1,k4_xboole_0(X0,sK3)) = k2_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0) ),
% 15.95/2.49      inference(light_normalisation,[status(thm)],[c_1566,c_887]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_4,plain,
% 15.95/2.49      ( k2_xboole_0(X0,X0) = X0 ),
% 15.95/2.49      inference(cnf_transformation,[],[f32]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_10,plain,
% 15.95/2.49      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.95/2.49      inference(cnf_transformation,[],[f38]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_630,plain,
% 15.95/2.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_4,c_10]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_8,plain,
% 15.95/2.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 15.95/2.49      inference(cnf_transformation,[],[f36]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1385,plain,
% 15.95/2.49      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_630,c_8]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1387,plain,
% 15.95/2.49      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.95/2.49      inference(light_normalisation,[status(thm)],[c_1385,c_4]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1568,plain,
% 15.95/2.49      ( k4_xboole_0(sK1,k4_xboole_0(X0,sK3)) = k4_xboole_0(sK1,X0) ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_1567,c_1387]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_0,plain,
% 15.95/2.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.95/2.49      inference(cnf_transformation,[],[f28]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_18,negated_conjecture,
% 15.95/2.49      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 15.95/2.49      inference(cnf_transformation,[],[f44]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_574,plain,
% 15.95/2.49      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_0,c_18]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_7,plain,
% 15.95/2.49      ( r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) ),
% 15.95/2.49      inference(cnf_transformation,[],[f52]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_375,plain,
% 15.95/2.49      ( r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) = iProver_top ),
% 15.95/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_378,plain,
% 15.95/2.49      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)),k2_xboole_0(X1,X2)) = iProver_top ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_375,c_12]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_3483,plain,
% 15.95/2.49      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,sK2),sK3)),k2_xboole_0(sK1,sK0)) = iProver_top ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_574,c_378]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_696,plain,
% 15.95/2.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_10,c_8]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_4793,plain,
% 15.95/2.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_696,c_1387]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_4796,plain,
% 15.95/2.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_0,c_4793]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_5010,plain,
% 15.95/2.49      ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(sK3,sK2) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_574,c_4796]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_628,plain,
% 15.95/2.49      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_0,c_10]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_2242,plain,
% 15.95/2.49      ( k4_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_574,c_628]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_2336,plain,
% 15.95/2.49      ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(k2_xboole_0(sK1,sK0),k1_xboole_0) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_2242,c_8]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_2339,plain,
% 15.95/2.49      ( k2_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k2_xboole_0(sK1,sK0) ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_2336,c_1387]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_5045,plain,
% 15.95/2.49      ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK1,sK0) ),
% 15.95/2.49      inference(light_normalisation,[status(thm)],[c_5010,c_2339]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_9,plain,
% 15.95/2.49      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 15.95/2.49      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 15.95/2.49      inference(cnf_transformation,[],[f37]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_374,plain,
% 15.95/2.49      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 15.95/2.49      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 15.95/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_5498,plain,
% 15.95/2.49      ( r1_tarski(X0,k2_xboole_0(sK1,sK0)) != iProver_top
% 15.95/2.49      | r1_tarski(k4_xboole_0(X0,sK3),sK2) = iProver_top ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_5045,c_374]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_73017,plain,
% 15.95/2.49      ( r1_tarski(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,sK2),sK3)),sK3),sK2) = iProver_top ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_3483,c_5498]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_73111,plain,
% 15.95/2.49      ( r1_tarski(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3),sK2) = iProver_top ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_1568,c_73017]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1563,plain,
% 15.95/2.49      ( k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(sK1,k4_xboole_0(sK3,X0)) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_884,c_12]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1571,plain,
% 15.95/2.49      ( k4_xboole_0(sK1,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK3,X0)) ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_1563,c_12]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1395,plain,
% 15.95/2.49      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_1387,c_0]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1943,plain,
% 15.95/2.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_1395,c_10]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_11068,plain,
% 15.95/2.49      ( k4_xboole_0(sK1,k4_xboole_0(sK3,X0)) = k4_xboole_0(sK1,k1_xboole_0) ),
% 15.95/2.49      inference(light_normalisation,[status(thm)],[c_1571,c_1571,c_1943]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1948,plain,
% 15.95/2.49      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_1395,c_8]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1949,plain,
% 15.95/2.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_1948,c_1395]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_11069,plain,
% 15.95/2.49      ( k4_xboole_0(sK1,k4_xboole_0(sK3,X0)) = sK1 ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_11068,c_1571,c_1949]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_11082,plain,
% 15.95/2.49      ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_2242,c_11069]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_797,plain,
% 15.95/2.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_1,c_11]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_11104,plain,
% 15.95/2.49      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_11069,c_797]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_14,plain,
% 15.95/2.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 15.95/2.49      inference(cnf_transformation,[],[f43]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_373,plain,
% 15.95/2.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 15.95/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1110,plain,
% 15.95/2.49      ( r1_tarski(X0,k2_xboole_0(sK1,sK0)) != iProver_top
% 15.95/2.49      | r1_tarski(k4_xboole_0(X0,sK2),sK3) = iProver_top ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_574,c_374]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1556,plain,
% 15.95/2.49      ( r1_tarski(k4_xboole_0(sK1,sK2),sK3) = iProver_top ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_373,c_1110]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_5,plain,
% 15.95/2.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 15.95/2.49      inference(cnf_transformation,[],[f33]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_377,plain,
% 15.95/2.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 15.95/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_2701,plain,
% 15.95/2.49      ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK3) = sK3 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_1556,c_377]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_2240,plain,
% 15.95/2.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_8,c_628]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_3799,plain,
% 15.95/2.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_0,c_2240]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_4170,plain,
% 15.95/2.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_8,c_3799]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_20798,plain,
% 15.95/2.49      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK3,k4_xboole_0(sK1,sK2))),sK3) = k1_xboole_0 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_2701,c_4170]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_799,plain,
% 15.95/2.49      ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK1) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_184,c_11]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1222,plain,
% 15.95/2.49      ( k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) = k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_799,c_12]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1248,plain,
% 15.95/2.49      ( k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_1222,c_12]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_9853,plain,
% 15.95/2.49      ( k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK3,k1_xboole_0) ),
% 15.95/2.49      inference(light_normalisation,[status(thm)],[c_1248,c_1248,c_1943]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_9854,plain,
% 15.95/2.49      ( k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) = sK3 ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_9853,c_1248,c_1949]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_9881,plain,
% 15.95/2.49      ( k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK3,sK3)) = k4_xboole_0(k4_xboole_0(sK1,X0),sK3) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_9854,c_797]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_9892,plain,
% 15.95/2.49      ( k4_xboole_0(k4_xboole_0(sK1,X0),sK3) = k4_xboole_0(sK1,X0) ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_9881,c_630,c_1949]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_20838,plain,
% 15.95/2.49      ( k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_20798,c_9854,c_9892]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_73161,plain,
% 15.95/2.49      ( r1_tarski(sK1,sK2) = iProver_top ),
% 15.95/2.49      inference(light_normalisation,
% 15.95/2.49                [status(thm)],
% 15.95/2.49                [c_73111,c_11082,c_11104,c_20838]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_73165,plain,
% 15.95/2.49      ( k2_xboole_0(sK1,sK2) = sK2 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_73161,c_377]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_391,plain,
% 15.95/2.49      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_240]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_13317,plain,
% 15.95/2.49      ( sK2 != k2_xboole_0(sK2,X0)
% 15.95/2.49      | sK1 != k2_xboole_0(sK2,X0)
% 15.95/2.49      | sK1 = sK2 ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_391]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_39585,plain,
% 15.95/2.49      ( sK2 != k2_xboole_0(sK2,sK1)
% 15.95/2.49      | sK1 != k2_xboole_0(sK2,sK1)
% 15.95/2.49      | sK1 = sK2 ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_13317]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_612,plain,
% 15.95/2.49      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_240]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_685,plain,
% 15.95/2.49      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_612]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_954,plain,
% 15.95/2.49      ( k2_xboole_0(X0,sK1) != sK1
% 15.95/2.49      | sK1 = k2_xboole_0(X0,sK1)
% 15.95/2.49      | sK1 != sK1 ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_685]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_39584,plain,
% 15.95/2.49      ( k2_xboole_0(sK2,sK1) != sK1
% 15.95/2.49      | sK1 = k2_xboole_0(sK2,sK1)
% 15.95/2.49      | sK1 != sK1 ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_954]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_4850,plain,
% 15.95/2.49      ( k2_xboole_0(sK2,X0) = k2_xboole_0(X0,sK2) ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_0]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_25220,plain,
% 15.95/2.49      ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK1,sK2) ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_4850]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_395,plain,
% 15.95/2.49      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_394]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_411,plain,
% 15.95/2.49      ( k2_xboole_0(X0,sK2) != sK2
% 15.95/2.49      | sK2 = k2_xboole_0(X0,sK2)
% 15.95/2.49      | sK2 != sK2 ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_395]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_25198,plain,
% 15.95/2.49      ( k2_xboole_0(sK1,sK2) != sK2
% 15.95/2.49      | sK2 = k2_xboole_0(sK1,sK2)
% 15.95/2.49      | sK2 != sK2 ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_411]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_814,plain,
% 15.95/2.49      ( r1_tarski(sK2,k2_xboole_0(sK1,sK0)) = iProver_top ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_574,c_373]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1106,plain,
% 15.95/2.49      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 15.95/2.49      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_0,c_374]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_10873,plain,
% 15.95/2.49      ( r1_tarski(k4_xboole_0(sK2,sK0),sK1) = iProver_top ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_814,c_1106]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_813,plain,
% 15.95/2.49      ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_574,c_10]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1234,plain,
% 15.95/2.49      ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k1_xboole_0)) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_813,c_12]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1386,plain,
% 15.95/2.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_630,c_12]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_7352,plain,
% 15.95/2.49      ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(sK2,k4_xboole_0(X0,sK2)) ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_1234,c_1386]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_7383,plain,
% 15.95/2.49      ( k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_7352,c_12]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_7393,plain,
% 15.95/2.49      ( k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(X0,sK2)) ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_7383,c_7352]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1241,plain,
% 15.95/2.49      ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_12,c_8]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_1242,plain,
% 15.95/2.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k1_xboole_0) ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_1241,c_630]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_7394,plain,
% 15.95/2.49      ( k4_xboole_0(sK2,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK2,k1_xboole_0) ),
% 15.95/2.49      inference(demodulation,
% 15.95/2.49                [status(thm)],
% 15.95/2.49                [c_7393,c_12,c_630,c_1242,c_1949]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_7395,plain,
% 15.95/2.49      ( k4_xboole_0(sK2,k4_xboole_0(X0,sK2)) = sK2 ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_7394,c_1949]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_7396,plain,
% 15.95/2.49      ( k4_xboole_0(sK2,k4_xboole_0(X0,k2_xboole_0(sK1,sK0))) = sK2 ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_7395,c_7352]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_7436,plain,
% 15.95/2.49      ( k2_xboole_0(k4_xboole_0(sK2,X0),k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))) = sK2 ),
% 15.95/2.49      inference(light_normalisation,[status(thm)],[c_7383,c_7396]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_7437,plain,
% 15.95/2.49      ( k4_xboole_0(sK2,k1_xboole_0) = sK2 ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_7436,c_12,c_1242,c_7395]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_17,negated_conjecture,
% 15.95/2.49      ( r1_xboole_0(sK2,sK0) ),
% 15.95/2.49      inference(cnf_transformation,[],[f45]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_188,plain,
% 15.95/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 15.95/2.49      | sK0 != X1
% 15.95/2.49      | sK2 != X0 ),
% 15.95/2.49      inference(resolution_lifted,[status(thm)],[c_98,c_17]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_189,plain,
% 15.95/2.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 15.95/2.49      inference(unflattening,[status(thm)],[c_188]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_800,plain,
% 15.95/2.49      ( k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK0) ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_189,c_11]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_7674,plain,
% 15.95/2.49      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 15.95/2.49      inference(demodulation,[status(thm)],[c_7437,c_800]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_10903,plain,
% 15.95/2.49      ( r1_tarski(sK2,sK1) = iProver_top ),
% 15.95/2.49      inference(light_normalisation,[status(thm)],[c_10873,c_7674]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_19094,plain,
% 15.95/2.49      ( k2_xboole_0(sK2,sK1) = sK1 ),
% 15.95/2.49      inference(superposition,[status(thm)],[c_10903,c_377]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_239,plain,( X0 = X0 ),theory(equality) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_657,plain,
% 15.95/2.49      ( sK1 = sK1 ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_239]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_398,plain,
% 15.95/2.49      ( sK2 = sK2 ),
% 15.95/2.49      inference(instantiation,[status(thm)],[c_239]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(c_15,negated_conjecture,
% 15.95/2.49      ( sK1 != sK2 ),
% 15.95/2.49      inference(cnf_transformation,[],[f47]) ).
% 15.95/2.49  
% 15.95/2.49  cnf(contradiction,plain,
% 15.95/2.49      ( $false ),
% 15.95/2.49      inference(minisat,
% 15.95/2.49                [status(thm)],
% 15.95/2.49                [c_73202,c_73165,c_39585,c_39584,c_25220,c_25198,c_19094,
% 15.95/2.49                 c_657,c_398,c_15]) ).
% 15.95/2.49  
% 15.95/2.49  
% 15.95/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.95/2.49  
% 15.95/2.49  ------                               Statistics
% 15.95/2.49  
% 15.95/2.49  ------ General
% 15.95/2.49  
% 15.95/2.49  abstr_ref_over_cycles:                  0
% 15.95/2.49  abstr_ref_under_cycles:                 0
% 15.95/2.49  gc_basic_clause_elim:                   0
% 15.95/2.49  forced_gc_time:                         0
% 15.95/2.49  parsing_time:                           0.006
% 15.95/2.49  unif_index_cands_time:                  0.
% 15.95/2.49  unif_index_add_time:                    0.
% 15.95/2.49  orderings_time:                         0.
% 15.95/2.49  out_proof_time:                         0.01
% 15.95/2.49  total_time:                             1.857
% 15.95/2.49  num_of_symbols:                         40
% 15.95/2.49  num_of_terms:                           80732
% 15.95/2.49  
% 15.95/2.49  ------ Preprocessing
% 15.95/2.49  
% 15.95/2.49  num_of_splits:                          0
% 15.95/2.49  num_of_split_atoms:                     0
% 15.95/2.49  num_of_reused_defs:                     0
% 15.95/2.49  num_eq_ax_congr_red:                    1
% 15.95/2.49  num_of_sem_filtered_clauses:            1
% 15.95/2.49  num_of_subtypes:                        0
% 15.95/2.49  monotx_restored_types:                  0
% 15.95/2.49  sat_num_of_epr_types:                   0
% 15.95/2.49  sat_num_of_non_cyclic_types:            0
% 15.95/2.49  sat_guarded_non_collapsed_types:        0
% 15.95/2.49  num_pure_diseq_elim:                    0
% 15.95/2.49  simp_replaced_by:                       0
% 15.95/2.49  res_preprocessed:                       68
% 15.95/2.49  prep_upred:                             0
% 15.95/2.49  prep_unflattend:                        10
% 15.95/2.49  smt_new_axioms:                         0
% 15.95/2.49  pred_elim_cands:                        2
% 15.95/2.49  pred_elim:                              1
% 15.95/2.49  pred_elim_cl:                           0
% 15.95/2.49  pred_elim_cycles:                       2
% 15.95/2.49  merged_defs:                            2
% 15.95/2.49  merged_defs_ncl:                        0
% 15.95/2.49  bin_hyper_res:                          2
% 15.95/2.49  prep_cycles:                            3
% 15.95/2.49  pred_elim_time:                         0.001
% 15.95/2.49  splitting_time:                         0.
% 15.95/2.49  sem_filter_time:                        0.
% 15.95/2.49  monotx_time:                            0.
% 15.95/2.49  subtype_inf_time:                       0.
% 15.95/2.49  
% 15.95/2.49  ------ Problem properties
% 15.95/2.49  
% 15.95/2.49  clauses:                                19
% 15.95/2.49  conjectures:                            2
% 15.95/2.49  epr:                                    3
% 15.95/2.49  horn:                                   19
% 15.95/2.49  ground:                                 4
% 15.95/2.49  unary:                                  14
% 15.95/2.49  binary:                                 2
% 15.95/2.49  lits:                                   28
% 15.95/2.49  lits_eq:                                16
% 15.95/2.49  fd_pure:                                0
% 15.95/2.49  fd_pseudo:                              0
% 15.95/2.49  fd_cond:                                3
% 15.95/2.49  fd_pseudo_cond:                         0
% 15.95/2.49  ac_symbols:                             0
% 15.95/2.49  
% 15.95/2.49  ------ Propositional Solver
% 15.95/2.49  
% 15.95/2.49  prop_solver_calls:                      34
% 15.95/2.49  prop_fast_solver_calls:                 855
% 15.95/2.49  smt_solver_calls:                       0
% 15.95/2.49  smt_fast_solver_calls:                  0
% 15.95/2.49  prop_num_of_clauses:                    21552
% 15.95/2.49  prop_preprocess_simplified:             27310
% 15.95/2.49  prop_fo_subsumed:                       5
% 15.95/2.49  prop_solver_time:                       0.
% 15.95/2.49  smt_solver_time:                        0.
% 15.95/2.49  smt_fast_solver_time:                   0.
% 15.95/2.49  prop_fast_solver_time:                  0.
% 15.95/2.49  prop_unsat_core_time:                   0.002
% 15.95/2.49  
% 15.95/2.49  ------ QBF
% 15.95/2.49  
% 15.95/2.49  qbf_q_res:                              0
% 15.95/2.49  qbf_num_tautologies:                    0
% 15.95/2.49  qbf_prep_cycles:                        0
% 15.95/2.49  
% 15.95/2.49  ------ BMC1
% 15.95/2.49  
% 15.95/2.49  bmc1_current_bound:                     -1
% 15.95/2.49  bmc1_last_solved_bound:                 -1
% 15.95/2.49  bmc1_unsat_core_size:                   -1
% 15.95/2.49  bmc1_unsat_core_parents_size:           -1
% 15.95/2.49  bmc1_merge_next_fun:                    0
% 15.95/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.95/2.49  
% 15.95/2.49  ------ Instantiation
% 15.95/2.49  
% 15.95/2.49  inst_num_of_clauses:                    5273
% 15.95/2.49  inst_num_in_passive:                    3473
% 15.95/2.49  inst_num_in_active:                     1403
% 15.95/2.49  inst_num_in_unprocessed:                396
% 15.95/2.49  inst_num_of_loops:                      2162
% 15.95/2.49  inst_num_of_learning_restarts:          0
% 15.95/2.49  inst_num_moves_active_passive:          750
% 15.95/2.49  inst_lit_activity:                      0
% 15.95/2.49  inst_lit_activity_moves:                1
% 15.95/2.49  inst_num_tautologies:                   0
% 15.95/2.49  inst_num_prop_implied:                  0
% 15.95/2.49  inst_num_existing_simplified:           0
% 15.95/2.49  inst_num_eq_res_simplified:             0
% 15.95/2.49  inst_num_child_elim:                    0
% 15.95/2.49  inst_num_of_dismatching_blockings:      6107
% 15.95/2.49  inst_num_of_non_proper_insts:           6988
% 15.95/2.49  inst_num_of_duplicates:                 0
% 15.95/2.49  inst_inst_num_from_inst_to_res:         0
% 15.95/2.49  inst_dismatching_checking_time:         0.
% 15.95/2.49  
% 15.95/2.49  ------ Resolution
% 15.95/2.49  
% 15.95/2.49  res_num_of_clauses:                     0
% 15.95/2.49  res_num_in_passive:                     0
% 15.95/2.49  res_num_in_active:                      0
% 15.95/2.49  res_num_of_loops:                       71
% 15.95/2.49  res_forward_subset_subsumed:            895
% 15.95/2.49  res_backward_subset_subsumed:           6
% 15.95/2.49  res_forward_subsumed:                   0
% 15.95/2.49  res_backward_subsumed:                  0
% 15.95/2.49  res_forward_subsumption_resolution:     0
% 15.95/2.49  res_backward_subsumption_resolution:    0
% 15.95/2.49  res_clause_to_clause_subsumption:       38380
% 15.95/2.49  res_orphan_elimination:                 0
% 15.95/2.49  res_tautology_del:                      476
% 15.95/2.49  res_num_eq_res_simplified:              0
% 15.95/2.49  res_num_sel_changes:                    0
% 15.95/2.49  res_moves_from_active_to_pass:          0
% 15.95/2.49  
% 15.95/2.49  ------ Superposition
% 15.95/2.49  
% 15.95/2.49  sup_time_total:                         0.
% 15.95/2.49  sup_time_generating:                    0.
% 15.95/2.49  sup_time_sim_full:                      0.
% 15.95/2.49  sup_time_sim_immed:                     0.
% 15.95/2.49  
% 15.95/2.49  sup_num_of_clauses:                     3489
% 15.95/2.49  sup_num_in_active:                      318
% 15.95/2.49  sup_num_in_passive:                     3171
% 15.95/2.49  sup_num_of_loops:                       432
% 15.95/2.49  sup_fw_superposition:                   8887
% 15.95/2.49  sup_bw_superposition:                   8791
% 15.95/2.49  sup_immediate_simplified:               10898
% 15.95/2.49  sup_given_eliminated:                   69
% 15.95/2.49  comparisons_done:                       0
% 15.95/2.49  comparisons_avoided:                    0
% 15.95/2.49  
% 15.95/2.49  ------ Simplifications
% 15.95/2.49  
% 15.95/2.49  
% 15.95/2.49  sim_fw_subset_subsumed:                 37
% 15.95/2.49  sim_bw_subset_subsumed:                 12
% 15.95/2.49  sim_fw_subsumed:                        1668
% 15.95/2.49  sim_bw_subsumed:                        131
% 15.95/2.49  sim_fw_subsumption_res:                 0
% 15.95/2.49  sim_bw_subsumption_res:                 0
% 15.95/2.49  sim_tautology_del:                      27
% 15.95/2.49  sim_eq_tautology_del:                   3177
% 15.95/2.49  sim_eq_res_simp:                        0
% 15.95/2.49  sim_fw_demodulated:                     7852
% 15.95/2.49  sim_bw_demodulated:                     228
% 15.95/2.49  sim_light_normalised:                   5604
% 15.95/2.49  sim_joinable_taut:                      0
% 15.95/2.49  sim_joinable_simp:                      0
% 15.95/2.49  sim_ac_normalised:                      0
% 15.95/2.49  sim_smt_subsumption:                    0
% 15.95/2.49  
%------------------------------------------------------------------------------
