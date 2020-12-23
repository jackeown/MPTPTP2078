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
% DateTime   : Thu Dec  3 11:24:33 EST 2020

% Result     : Theorem 11.85s
% Output     : CNFRefutation 11.85s
% Verified   : 
% Statistics : Number of formulae       :  106 (1138 expanded)
%              Number of clauses        :   69 ( 347 expanded)
%              Number of leaves         :   12 ( 328 expanded)
%              Depth                    :   23
%              Number of atoms          :  129 (1274 expanded)
%              Number of equality atoms :  101 (1105 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f27,f25,f25,f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f19,f25])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).

fof(f30,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f29,f25])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f26,f25,f25])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f31,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_48,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_91,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | k4_xboole_0(sK1,sK2) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_48,c_12])).

cnf(c_92,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_91])).

cnf(c_10,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_400,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_92,c_10])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_117,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_5])).

cnf(c_9,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_298,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_117,c_9])).

cnf(c_301,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_298,c_5])).

cnf(c_421,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_400,c_301])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_405,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_117,c_10])).

cnf(c_413,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_405,c_5])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_408,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_10,c_4])).

cnf(c_412,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_408,c_5,c_117])).

cnf(c_2249,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_413,c_412,c_413])).

cnf(c_2254,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_2249])).

cnf(c_4054,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,X0)))) = k4_xboole_0(X0,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_421,c_2254])).

cnf(c_4865,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X1)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_8,c_4054])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_348,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_1902,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_421,c_348])).

cnf(c_2006,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_1902,c_6])).

cnf(c_5015,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X1)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X1,X0))))) = k4_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_4865,c_2006])).

cnf(c_492,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_6,c_8])).

cnf(c_580,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_492,c_348])).

cnf(c_5016,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_5015,c_8,c_580])).

cnf(c_762,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_421])).

cnf(c_12435,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK2))) ),
    inference(superposition,[status(thm)],[c_5016,c_762])).

cnf(c_398,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_10])).

cnf(c_1948,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X3))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),X3)) ),
    inference(superposition,[status(thm)],[c_348,c_10])).

cnf(c_12474,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))) = sK0 ),
    inference(demodulation,[status(thm)],[c_12435,c_9,c_398,c_1948])).

cnf(c_364,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_7,c_4])).

cnf(c_15345,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),sK1),k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_12474,c_364])).

cnf(c_15351,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) = k4_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_15345,c_6,c_117,c_301,c_412])).

cnf(c_2617,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))))) ),
    inference(superposition,[status(thm)],[c_8,c_364])).

cnf(c_1947,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X3)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X2),X3)) ),
    inference(superposition,[status(thm)],[c_348,c_8])).

cnf(c_1961,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X2),X3)) ),
    inference(demodulation,[status(thm)],[c_1947,c_1948])).

cnf(c_2664,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ),
    inference(demodulation,[status(thm)],[c_2617,c_8,c_10,c_1961])).

cnf(c_2287,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_2249,c_10])).

cnf(c_2313,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2287,c_117])).

cnf(c_2314,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2313,c_301])).

cnf(c_2665,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_2664,c_7,c_10,c_2314])).

cnf(c_25219,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(sK0,sK2))) ),
    inference(superposition,[status(thm)],[c_15351,c_2665])).

cnf(c_4873,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_762,c_4054])).

cnf(c_5005,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))))) = k4_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_4873,c_421,c_2006])).

cnf(c_5006,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),X0) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_5005,c_6,c_580])).

cnf(c_5289,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),X1),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0))) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5006,c_10])).

cnf(c_5337,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X1,X0)) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_5289,c_117,c_301])).

cnf(c_25550,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,sK2),sK0))) = k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(sK0,sK2))) ),
    inference(demodulation,[status(thm)],[c_25219,c_5337])).

cnf(c_509,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_117,c_8])).

cnf(c_544,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_509,c_5,c_413])).

cnf(c_545,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_544,c_7,c_117,c_412])).

cnf(c_1437,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_545])).

cnf(c_25551,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_25550,c_5,c_1437])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_46,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_11,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_86,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | k4_xboole_0(sK0,sK2) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_46,c_11])).

cnf(c_87,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_86])).

cnf(c_26413,plain,
    ( k4_xboole_0(sK1,sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_25551,c_87])).

cnf(c_26414,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_26413,c_117])).

cnf(c_26415,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_26414])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:42:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.85/2.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.85/2.03  
% 11.85/2.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.85/2.03  
% 11.85/2.03  ------  iProver source info
% 11.85/2.03  
% 11.85/2.03  git: date: 2020-06-30 10:37:57 +0100
% 11.85/2.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.85/2.03  git: non_committed_changes: false
% 11.85/2.03  git: last_make_outside_of_git: false
% 11.85/2.03  
% 11.85/2.03  ------ 
% 11.85/2.03  
% 11.85/2.03  ------ Input Options
% 11.85/2.03  
% 11.85/2.03  --out_options                           all
% 11.85/2.03  --tptp_safe_out                         true
% 11.85/2.03  --problem_path                          ""
% 11.85/2.03  --include_path                          ""
% 11.85/2.03  --clausifier                            res/vclausify_rel
% 11.85/2.03  --clausifier_options                    ""
% 11.85/2.03  --stdin                                 false
% 11.85/2.03  --stats_out                             all
% 11.85/2.03  
% 11.85/2.03  ------ General Options
% 11.85/2.03  
% 11.85/2.03  --fof                                   false
% 11.85/2.03  --time_out_real                         305.
% 11.85/2.03  --time_out_virtual                      -1.
% 11.85/2.03  --symbol_type_check                     false
% 11.85/2.03  --clausify_out                          false
% 11.85/2.03  --sig_cnt_out                           false
% 11.85/2.03  --trig_cnt_out                          false
% 11.85/2.03  --trig_cnt_out_tolerance                1.
% 11.85/2.03  --trig_cnt_out_sk_spl                   false
% 11.85/2.03  --abstr_cl_out                          false
% 11.85/2.03  
% 11.85/2.03  ------ Global Options
% 11.85/2.03  
% 11.85/2.03  --schedule                              default
% 11.85/2.03  --add_important_lit                     false
% 11.85/2.03  --prop_solver_per_cl                    1000
% 11.85/2.03  --min_unsat_core                        false
% 11.85/2.03  --soft_assumptions                      false
% 11.85/2.03  --soft_lemma_size                       3
% 11.85/2.03  --prop_impl_unit_size                   0
% 11.85/2.03  --prop_impl_unit                        []
% 11.85/2.03  --share_sel_clauses                     true
% 11.85/2.03  --reset_solvers                         false
% 11.85/2.03  --bc_imp_inh                            [conj_cone]
% 11.85/2.03  --conj_cone_tolerance                   3.
% 11.85/2.03  --extra_neg_conj                        none
% 11.85/2.03  --large_theory_mode                     true
% 11.85/2.03  --prolific_symb_bound                   200
% 11.85/2.03  --lt_threshold                          2000
% 11.85/2.03  --clause_weak_htbl                      true
% 11.85/2.03  --gc_record_bc_elim                     false
% 11.85/2.03  
% 11.85/2.03  ------ Preprocessing Options
% 11.85/2.03  
% 11.85/2.03  --preprocessing_flag                    true
% 11.85/2.03  --time_out_prep_mult                    0.1
% 11.85/2.03  --splitting_mode                        input
% 11.85/2.03  --splitting_grd                         true
% 11.85/2.03  --splitting_cvd                         false
% 11.85/2.03  --splitting_cvd_svl                     false
% 11.85/2.03  --splitting_nvd                         32
% 11.85/2.03  --sub_typing                            true
% 11.85/2.03  --prep_gs_sim                           true
% 11.85/2.03  --prep_unflatten                        true
% 11.85/2.03  --prep_res_sim                          true
% 11.85/2.03  --prep_upred                            true
% 11.85/2.03  --prep_sem_filter                       exhaustive
% 11.85/2.03  --prep_sem_filter_out                   false
% 11.85/2.03  --pred_elim                             true
% 11.85/2.03  --res_sim_input                         true
% 11.85/2.03  --eq_ax_congr_red                       true
% 11.85/2.03  --pure_diseq_elim                       true
% 11.85/2.03  --brand_transform                       false
% 11.85/2.03  --non_eq_to_eq                          false
% 11.85/2.03  --prep_def_merge                        true
% 11.85/2.03  --prep_def_merge_prop_impl              false
% 11.85/2.03  --prep_def_merge_mbd                    true
% 11.85/2.03  --prep_def_merge_tr_red                 false
% 11.85/2.03  --prep_def_merge_tr_cl                  false
% 11.85/2.03  --smt_preprocessing                     true
% 11.85/2.03  --smt_ac_axioms                         fast
% 11.85/2.03  --preprocessed_out                      false
% 11.85/2.03  --preprocessed_stats                    false
% 11.85/2.03  
% 11.85/2.03  ------ Abstraction refinement Options
% 11.85/2.03  
% 11.85/2.03  --abstr_ref                             []
% 11.85/2.03  --abstr_ref_prep                        false
% 11.85/2.03  --abstr_ref_until_sat                   false
% 11.85/2.03  --abstr_ref_sig_restrict                funpre
% 11.85/2.03  --abstr_ref_af_restrict_to_split_sk     false
% 11.85/2.03  --abstr_ref_under                       []
% 11.85/2.03  
% 11.85/2.03  ------ SAT Options
% 11.85/2.03  
% 11.85/2.03  --sat_mode                              false
% 11.85/2.03  --sat_fm_restart_options                ""
% 11.85/2.03  --sat_gr_def                            false
% 11.85/2.03  --sat_epr_types                         true
% 11.85/2.03  --sat_non_cyclic_types                  false
% 11.85/2.03  --sat_finite_models                     false
% 11.85/2.03  --sat_fm_lemmas                         false
% 11.85/2.03  --sat_fm_prep                           false
% 11.85/2.03  --sat_fm_uc_incr                        true
% 11.85/2.03  --sat_out_model                         small
% 11.85/2.03  --sat_out_clauses                       false
% 11.85/2.03  
% 11.85/2.03  ------ QBF Options
% 11.85/2.03  
% 11.85/2.03  --qbf_mode                              false
% 11.85/2.03  --qbf_elim_univ                         false
% 11.85/2.03  --qbf_dom_inst                          none
% 11.85/2.03  --qbf_dom_pre_inst                      false
% 11.85/2.03  --qbf_sk_in                             false
% 11.85/2.03  --qbf_pred_elim                         true
% 11.85/2.03  --qbf_split                             512
% 11.85/2.03  
% 11.85/2.03  ------ BMC1 Options
% 11.85/2.03  
% 11.85/2.03  --bmc1_incremental                      false
% 11.85/2.03  --bmc1_axioms                           reachable_all
% 11.85/2.03  --bmc1_min_bound                        0
% 11.85/2.03  --bmc1_max_bound                        -1
% 11.85/2.03  --bmc1_max_bound_default                -1
% 11.85/2.03  --bmc1_symbol_reachability              true
% 11.85/2.03  --bmc1_property_lemmas                  false
% 11.85/2.03  --bmc1_k_induction                      false
% 11.85/2.03  --bmc1_non_equiv_states                 false
% 11.85/2.03  --bmc1_deadlock                         false
% 11.85/2.03  --bmc1_ucm                              false
% 11.85/2.03  --bmc1_add_unsat_core                   none
% 11.85/2.03  --bmc1_unsat_core_children              false
% 11.85/2.03  --bmc1_unsat_core_extrapolate_axioms    false
% 11.85/2.03  --bmc1_out_stat                         full
% 11.85/2.03  --bmc1_ground_init                      false
% 11.85/2.03  --bmc1_pre_inst_next_state              false
% 11.85/2.03  --bmc1_pre_inst_state                   false
% 11.85/2.03  --bmc1_pre_inst_reach_state             false
% 11.85/2.03  --bmc1_out_unsat_core                   false
% 11.85/2.03  --bmc1_aig_witness_out                  false
% 11.85/2.03  --bmc1_verbose                          false
% 11.85/2.03  --bmc1_dump_clauses_tptp                false
% 11.85/2.03  --bmc1_dump_unsat_core_tptp             false
% 11.85/2.03  --bmc1_dump_file                        -
% 11.85/2.03  --bmc1_ucm_expand_uc_limit              128
% 11.85/2.03  --bmc1_ucm_n_expand_iterations          6
% 11.85/2.03  --bmc1_ucm_extend_mode                  1
% 11.85/2.03  --bmc1_ucm_init_mode                    2
% 11.85/2.03  --bmc1_ucm_cone_mode                    none
% 11.85/2.03  --bmc1_ucm_reduced_relation_type        0
% 11.85/2.03  --bmc1_ucm_relax_model                  4
% 11.85/2.03  --bmc1_ucm_full_tr_after_sat            true
% 11.85/2.03  --bmc1_ucm_expand_neg_assumptions       false
% 11.85/2.03  --bmc1_ucm_layered_model                none
% 11.85/2.03  --bmc1_ucm_max_lemma_size               10
% 11.85/2.03  
% 11.85/2.03  ------ AIG Options
% 11.85/2.03  
% 11.85/2.03  --aig_mode                              false
% 11.85/2.03  
% 11.85/2.03  ------ Instantiation Options
% 11.85/2.03  
% 11.85/2.03  --instantiation_flag                    true
% 11.85/2.03  --inst_sos_flag                         true
% 11.85/2.03  --inst_sos_phase                        true
% 11.85/2.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.85/2.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.85/2.03  --inst_lit_sel_side                     num_symb
% 11.85/2.03  --inst_solver_per_active                1400
% 11.85/2.03  --inst_solver_calls_frac                1.
% 11.85/2.03  --inst_passive_queue_type               priority_queues
% 11.85/2.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.85/2.03  --inst_passive_queues_freq              [25;2]
% 11.85/2.03  --inst_dismatching                      true
% 11.85/2.03  --inst_eager_unprocessed_to_passive     true
% 11.85/2.03  --inst_prop_sim_given                   true
% 11.85/2.03  --inst_prop_sim_new                     false
% 11.85/2.03  --inst_subs_new                         false
% 11.85/2.03  --inst_eq_res_simp                      false
% 11.85/2.03  --inst_subs_given                       false
% 11.85/2.03  --inst_orphan_elimination               true
% 11.85/2.03  --inst_learning_loop_flag               true
% 11.85/2.03  --inst_learning_start                   3000
% 11.85/2.03  --inst_learning_factor                  2
% 11.85/2.03  --inst_start_prop_sim_after_learn       3
% 11.85/2.03  --inst_sel_renew                        solver
% 11.85/2.03  --inst_lit_activity_flag                true
% 11.85/2.03  --inst_restr_to_given                   false
% 11.85/2.03  --inst_activity_threshold               500
% 11.85/2.03  --inst_out_proof                        true
% 11.85/2.03  
% 11.85/2.03  ------ Resolution Options
% 11.85/2.03  
% 11.85/2.03  --resolution_flag                       true
% 11.85/2.03  --res_lit_sel                           adaptive
% 11.85/2.03  --res_lit_sel_side                      none
% 11.85/2.03  --res_ordering                          kbo
% 11.85/2.03  --res_to_prop_solver                    active
% 11.85/2.03  --res_prop_simpl_new                    false
% 11.85/2.03  --res_prop_simpl_given                  true
% 11.85/2.03  --res_passive_queue_type                priority_queues
% 11.85/2.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.85/2.03  --res_passive_queues_freq               [15;5]
% 11.85/2.03  --res_forward_subs                      full
% 11.85/2.03  --res_backward_subs                     full
% 11.85/2.03  --res_forward_subs_resolution           true
% 11.85/2.03  --res_backward_subs_resolution          true
% 11.85/2.03  --res_orphan_elimination                true
% 11.85/2.03  --res_time_limit                        2.
% 11.85/2.03  --res_out_proof                         true
% 11.85/2.03  
% 11.85/2.03  ------ Superposition Options
% 11.85/2.03  
% 11.85/2.03  --superposition_flag                    true
% 11.85/2.03  --sup_passive_queue_type                priority_queues
% 11.85/2.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.85/2.03  --sup_passive_queues_freq               [8;1;4]
% 11.85/2.03  --demod_completeness_check              fast
% 11.85/2.03  --demod_use_ground                      true
% 11.85/2.03  --sup_to_prop_solver                    passive
% 11.85/2.03  --sup_prop_simpl_new                    true
% 11.85/2.03  --sup_prop_simpl_given                  true
% 11.85/2.03  --sup_fun_splitting                     true
% 11.85/2.03  --sup_smt_interval                      50000
% 11.85/2.03  
% 11.85/2.03  ------ Superposition Simplification Setup
% 11.85/2.03  
% 11.85/2.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.85/2.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.85/2.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.85/2.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.85/2.03  --sup_full_triv                         [TrivRules;PropSubs]
% 11.85/2.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.85/2.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.85/2.03  --sup_immed_triv                        [TrivRules]
% 11.85/2.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/2.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/2.03  --sup_immed_bw_main                     []
% 11.85/2.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.85/2.03  --sup_input_triv                        [Unflattening;TrivRules]
% 11.85/2.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/2.03  --sup_input_bw                          []
% 11.85/2.03  
% 11.85/2.03  ------ Combination Options
% 11.85/2.03  
% 11.85/2.03  --comb_res_mult                         3
% 11.85/2.03  --comb_sup_mult                         2
% 11.85/2.03  --comb_inst_mult                        10
% 11.85/2.03  
% 11.85/2.03  ------ Debug Options
% 11.85/2.03  
% 11.85/2.03  --dbg_backtrace                         false
% 11.85/2.03  --dbg_dump_prop_clauses                 false
% 11.85/2.03  --dbg_dump_prop_clauses_file            -
% 11.85/2.03  --dbg_out_stat                          false
% 11.85/2.03  ------ Parsing...
% 11.85/2.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.85/2.03  
% 11.85/2.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.85/2.03  
% 11.85/2.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.85/2.03  
% 11.85/2.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.85/2.03  ------ Proving...
% 11.85/2.03  ------ Problem Properties 
% 11.85/2.03  
% 11.85/2.03  
% 11.85/2.03  clauses                                 12
% 11.85/2.03  conjectures                             0
% 11.85/2.03  EPR                                     0
% 11.85/2.03  Horn                                    12
% 11.85/2.03  unary                                   11
% 11.85/2.03  binary                                  1
% 11.85/2.03  lits                                    13
% 11.85/2.03  lits eq                                 13
% 11.85/2.03  fd_pure                                 0
% 11.85/2.03  fd_pseudo                               0
% 11.85/2.03  fd_cond                                 0
% 11.85/2.03  fd_pseudo_cond                          0
% 11.85/2.03  AC symbols                              0
% 11.85/2.03  
% 11.85/2.03  ------ Schedule dynamic 5 is on 
% 11.85/2.03  
% 11.85/2.03  ------ no conjectures: strip conj schedule 
% 11.85/2.03  
% 11.85/2.03  ------ pure equality problem: resolution off 
% 11.85/2.03  
% 11.85/2.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 11.85/2.03  
% 11.85/2.03  
% 11.85/2.03  ------ 
% 11.85/2.03  Current options:
% 11.85/2.03  ------ 
% 11.85/2.03  
% 11.85/2.03  ------ Input Options
% 11.85/2.03  
% 11.85/2.03  --out_options                           all
% 11.85/2.03  --tptp_safe_out                         true
% 11.85/2.03  --problem_path                          ""
% 11.85/2.03  --include_path                          ""
% 11.85/2.03  --clausifier                            res/vclausify_rel
% 11.85/2.03  --clausifier_options                    ""
% 11.85/2.03  --stdin                                 false
% 11.85/2.03  --stats_out                             all
% 11.85/2.03  
% 11.85/2.03  ------ General Options
% 11.85/2.03  
% 11.85/2.03  --fof                                   false
% 11.85/2.03  --time_out_real                         305.
% 11.85/2.03  --time_out_virtual                      -1.
% 11.85/2.03  --symbol_type_check                     false
% 11.85/2.03  --clausify_out                          false
% 11.85/2.03  --sig_cnt_out                           false
% 11.85/2.03  --trig_cnt_out                          false
% 11.85/2.03  --trig_cnt_out_tolerance                1.
% 11.85/2.03  --trig_cnt_out_sk_spl                   false
% 11.85/2.03  --abstr_cl_out                          false
% 11.85/2.03  
% 11.85/2.03  ------ Global Options
% 11.85/2.03  
% 11.85/2.03  --schedule                              default
% 11.85/2.03  --add_important_lit                     false
% 11.85/2.03  --prop_solver_per_cl                    1000
% 11.85/2.03  --min_unsat_core                        false
% 11.85/2.03  --soft_assumptions                      false
% 11.85/2.03  --soft_lemma_size                       3
% 11.85/2.03  --prop_impl_unit_size                   0
% 11.85/2.03  --prop_impl_unit                        []
% 11.85/2.03  --share_sel_clauses                     true
% 11.85/2.03  --reset_solvers                         false
% 11.85/2.03  --bc_imp_inh                            [conj_cone]
% 11.85/2.03  --conj_cone_tolerance                   3.
% 11.85/2.03  --extra_neg_conj                        none
% 11.85/2.03  --large_theory_mode                     true
% 11.85/2.03  --prolific_symb_bound                   200
% 11.85/2.03  --lt_threshold                          2000
% 11.85/2.03  --clause_weak_htbl                      true
% 11.85/2.03  --gc_record_bc_elim                     false
% 11.85/2.03  
% 11.85/2.03  ------ Preprocessing Options
% 11.85/2.03  
% 11.85/2.03  --preprocessing_flag                    true
% 11.85/2.03  --time_out_prep_mult                    0.1
% 11.85/2.03  --splitting_mode                        input
% 11.85/2.03  --splitting_grd                         true
% 11.85/2.03  --splitting_cvd                         false
% 11.85/2.03  --splitting_cvd_svl                     false
% 11.85/2.03  --splitting_nvd                         32
% 11.85/2.03  --sub_typing                            true
% 11.85/2.03  --prep_gs_sim                           true
% 11.85/2.03  --prep_unflatten                        true
% 11.85/2.03  --prep_res_sim                          true
% 11.85/2.03  --prep_upred                            true
% 11.85/2.03  --prep_sem_filter                       exhaustive
% 11.85/2.03  --prep_sem_filter_out                   false
% 11.85/2.03  --pred_elim                             true
% 11.85/2.03  --res_sim_input                         true
% 11.85/2.03  --eq_ax_congr_red                       true
% 11.85/2.03  --pure_diseq_elim                       true
% 11.85/2.03  --brand_transform                       false
% 11.85/2.03  --non_eq_to_eq                          false
% 11.85/2.03  --prep_def_merge                        true
% 11.85/2.03  --prep_def_merge_prop_impl              false
% 11.85/2.03  --prep_def_merge_mbd                    true
% 11.85/2.03  --prep_def_merge_tr_red                 false
% 11.85/2.03  --prep_def_merge_tr_cl                  false
% 11.85/2.03  --smt_preprocessing                     true
% 11.85/2.03  --smt_ac_axioms                         fast
% 11.85/2.03  --preprocessed_out                      false
% 11.85/2.03  --preprocessed_stats                    false
% 11.85/2.03  
% 11.85/2.03  ------ Abstraction refinement Options
% 11.85/2.03  
% 11.85/2.03  --abstr_ref                             []
% 11.85/2.03  --abstr_ref_prep                        false
% 11.85/2.03  --abstr_ref_until_sat                   false
% 11.85/2.03  --abstr_ref_sig_restrict                funpre
% 11.85/2.03  --abstr_ref_af_restrict_to_split_sk     false
% 11.85/2.03  --abstr_ref_under                       []
% 11.85/2.03  
% 11.85/2.03  ------ SAT Options
% 11.85/2.03  
% 11.85/2.03  --sat_mode                              false
% 11.85/2.03  --sat_fm_restart_options                ""
% 11.85/2.03  --sat_gr_def                            false
% 11.85/2.03  --sat_epr_types                         true
% 11.85/2.03  --sat_non_cyclic_types                  false
% 11.85/2.03  --sat_finite_models                     false
% 11.85/2.03  --sat_fm_lemmas                         false
% 11.85/2.03  --sat_fm_prep                           false
% 11.85/2.03  --sat_fm_uc_incr                        true
% 11.85/2.03  --sat_out_model                         small
% 11.85/2.03  --sat_out_clauses                       false
% 11.85/2.03  
% 11.85/2.03  ------ QBF Options
% 11.85/2.03  
% 11.85/2.03  --qbf_mode                              false
% 11.85/2.03  --qbf_elim_univ                         false
% 11.85/2.03  --qbf_dom_inst                          none
% 11.85/2.03  --qbf_dom_pre_inst                      false
% 11.85/2.03  --qbf_sk_in                             false
% 11.85/2.03  --qbf_pred_elim                         true
% 11.85/2.03  --qbf_split                             512
% 11.85/2.03  
% 11.85/2.03  ------ BMC1 Options
% 11.85/2.03  
% 11.85/2.03  --bmc1_incremental                      false
% 11.85/2.03  --bmc1_axioms                           reachable_all
% 11.85/2.03  --bmc1_min_bound                        0
% 11.85/2.03  --bmc1_max_bound                        -1
% 11.85/2.03  --bmc1_max_bound_default                -1
% 11.85/2.03  --bmc1_symbol_reachability              true
% 11.85/2.03  --bmc1_property_lemmas                  false
% 11.85/2.03  --bmc1_k_induction                      false
% 11.85/2.03  --bmc1_non_equiv_states                 false
% 11.85/2.03  --bmc1_deadlock                         false
% 11.85/2.03  --bmc1_ucm                              false
% 11.85/2.03  --bmc1_add_unsat_core                   none
% 11.85/2.03  --bmc1_unsat_core_children              false
% 11.85/2.03  --bmc1_unsat_core_extrapolate_axioms    false
% 11.85/2.03  --bmc1_out_stat                         full
% 11.85/2.03  --bmc1_ground_init                      false
% 11.85/2.03  --bmc1_pre_inst_next_state              false
% 11.85/2.03  --bmc1_pre_inst_state                   false
% 11.85/2.03  --bmc1_pre_inst_reach_state             false
% 11.85/2.03  --bmc1_out_unsat_core                   false
% 11.85/2.03  --bmc1_aig_witness_out                  false
% 11.85/2.03  --bmc1_verbose                          false
% 11.85/2.03  --bmc1_dump_clauses_tptp                false
% 11.85/2.03  --bmc1_dump_unsat_core_tptp             false
% 11.85/2.03  --bmc1_dump_file                        -
% 11.85/2.03  --bmc1_ucm_expand_uc_limit              128
% 11.85/2.03  --bmc1_ucm_n_expand_iterations          6
% 11.85/2.03  --bmc1_ucm_extend_mode                  1
% 11.85/2.03  --bmc1_ucm_init_mode                    2
% 11.85/2.03  --bmc1_ucm_cone_mode                    none
% 11.85/2.03  --bmc1_ucm_reduced_relation_type        0
% 11.85/2.03  --bmc1_ucm_relax_model                  4
% 11.85/2.03  --bmc1_ucm_full_tr_after_sat            true
% 11.85/2.03  --bmc1_ucm_expand_neg_assumptions       false
% 11.85/2.03  --bmc1_ucm_layered_model                none
% 11.85/2.03  --bmc1_ucm_max_lemma_size               10
% 11.85/2.03  
% 11.85/2.03  ------ AIG Options
% 11.85/2.03  
% 11.85/2.03  --aig_mode                              false
% 11.85/2.03  
% 11.85/2.03  ------ Instantiation Options
% 11.85/2.03  
% 11.85/2.03  --instantiation_flag                    true
% 11.85/2.03  --inst_sos_flag                         true
% 11.85/2.03  --inst_sos_phase                        true
% 11.85/2.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.85/2.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.85/2.03  --inst_lit_sel_side                     none
% 11.85/2.03  --inst_solver_per_active                1400
% 11.85/2.03  --inst_solver_calls_frac                1.
% 11.85/2.03  --inst_passive_queue_type               priority_queues
% 11.85/2.03  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 11.85/2.03  --inst_passive_queues_freq              [25;2]
% 11.85/2.03  --inst_dismatching                      true
% 11.85/2.03  --inst_eager_unprocessed_to_passive     true
% 11.85/2.03  --inst_prop_sim_given                   true
% 11.85/2.03  --inst_prop_sim_new                     false
% 11.85/2.03  --inst_subs_new                         false
% 11.85/2.03  --inst_eq_res_simp                      false
% 11.85/2.03  --inst_subs_given                       false
% 11.85/2.03  --inst_orphan_elimination               true
% 11.85/2.03  --inst_learning_loop_flag               true
% 11.85/2.03  --inst_learning_start                   3000
% 11.85/2.03  --inst_learning_factor                  2
% 11.85/2.03  --inst_start_prop_sim_after_learn       3
% 11.85/2.03  --inst_sel_renew                        solver
% 11.85/2.03  --inst_lit_activity_flag                true
% 11.85/2.03  --inst_restr_to_given                   false
% 11.85/2.03  --inst_activity_threshold               500
% 11.85/2.03  --inst_out_proof                        true
% 11.85/2.03  
% 11.85/2.03  ------ Resolution Options
% 11.85/2.03  
% 11.85/2.03  --resolution_flag                       false
% 11.85/2.03  --res_lit_sel                           adaptive
% 11.85/2.03  --res_lit_sel_side                      none
% 11.85/2.03  --res_ordering                          kbo
% 11.85/2.03  --res_to_prop_solver                    active
% 11.85/2.03  --res_prop_simpl_new                    false
% 11.85/2.03  --res_prop_simpl_given                  true
% 11.85/2.03  --res_passive_queue_type                priority_queues
% 11.85/2.03  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 11.85/2.03  --res_passive_queues_freq               [15;5]
% 11.85/2.03  --res_forward_subs                      full
% 11.85/2.03  --res_backward_subs                     full
% 11.85/2.03  --res_forward_subs_resolution           true
% 11.85/2.03  --res_backward_subs_resolution          true
% 11.85/2.03  --res_orphan_elimination                true
% 11.85/2.03  --res_time_limit                        2.
% 11.85/2.03  --res_out_proof                         true
% 11.85/2.03  
% 11.85/2.03  ------ Superposition Options
% 11.85/2.03  
% 11.85/2.03  --superposition_flag                    true
% 11.85/2.03  --sup_passive_queue_type                priority_queues
% 11.85/2.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.85/2.03  --sup_passive_queues_freq               [8;1;4]
% 11.85/2.03  --demod_completeness_check              fast
% 11.85/2.03  --demod_use_ground                      true
% 11.85/2.03  --sup_to_prop_solver                    passive
% 11.85/2.03  --sup_prop_simpl_new                    true
% 11.85/2.03  --sup_prop_simpl_given                  true
% 11.85/2.03  --sup_fun_splitting                     true
% 11.85/2.03  --sup_smt_interval                      50000
% 11.85/2.03  
% 11.85/2.03  ------ Superposition Simplification Setup
% 11.85/2.03  
% 11.85/2.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.85/2.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.85/2.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.85/2.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.85/2.03  --sup_full_triv                         [TrivRules;PropSubs]
% 11.85/2.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.85/2.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.85/2.03  --sup_immed_triv                        [TrivRules]
% 11.85/2.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/2.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/2.03  --sup_immed_bw_main                     []
% 11.85/2.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.85/2.03  --sup_input_triv                        [Unflattening;TrivRules]
% 11.85/2.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.85/2.03  --sup_input_bw                          []
% 11.85/2.03  
% 11.85/2.03  ------ Combination Options
% 11.85/2.03  
% 11.85/2.03  --comb_res_mult                         3
% 11.85/2.03  --comb_sup_mult                         2
% 11.85/2.03  --comb_inst_mult                        10
% 11.85/2.03  
% 11.85/2.03  ------ Debug Options
% 11.85/2.03  
% 11.85/2.03  --dbg_backtrace                         false
% 11.85/2.03  --dbg_dump_prop_clauses                 false
% 11.85/2.03  --dbg_dump_prop_clauses_file            -
% 11.85/2.03  --dbg_out_stat                          false
% 11.85/2.03  
% 11.85/2.03  
% 11.85/2.03  
% 11.85/2.03  
% 11.85/2.03  ------ Proving...
% 11.85/2.03  
% 11.85/2.03  
% 11.85/2.03  % SZS status Theorem for theBenchmark.p
% 11.85/2.03  
% 11.85/2.03   Resolution empty clause
% 11.85/2.03  
% 11.85/2.03  % SZS output start CNFRefutation for theBenchmark.p
% 11.85/2.03  
% 11.85/2.03  fof(f9,axiom,(
% 11.85/2.03    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 11.85/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.03  
% 11.85/2.03  fof(f27,plain,(
% 11.85/2.03    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 11.85/2.03    inference(cnf_transformation,[],[f9])).
% 11.85/2.03  
% 11.85/2.03  fof(f7,axiom,(
% 11.85/2.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.85/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.03  
% 11.85/2.03  fof(f25,plain,(
% 11.85/2.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.85/2.03    inference(cnf_transformation,[],[f7])).
% 11.85/2.03  
% 11.85/2.03  fof(f37,plain,(
% 11.85/2.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 11.85/2.03    inference(definition_unfolding,[],[f27,f25,f25,f25])).
% 11.85/2.03  
% 11.85/2.03  fof(f2,axiom,(
% 11.85/2.03    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.85/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.03  
% 11.85/2.03  fof(f15,plain,(
% 11.85/2.03    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.85/2.03    inference(nnf_transformation,[],[f2])).
% 11.85/2.03  
% 11.85/2.03  fof(f19,plain,(
% 11.85/2.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.85/2.03    inference(cnf_transformation,[],[f15])).
% 11.85/2.03  
% 11.85/2.03  fof(f33,plain,(
% 11.85/2.03    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 11.85/2.03    inference(definition_unfolding,[],[f19,f25])).
% 11.85/2.03  
% 11.85/2.03  fof(f12,conjecture,(
% 11.85/2.03    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 11.85/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.03  
% 11.85/2.03  fof(f13,negated_conjecture,(
% 11.85/2.03    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 11.85/2.03    inference(negated_conjecture,[],[f12])).
% 11.85/2.03  
% 11.85/2.03  fof(f14,plain,(
% 11.85/2.03    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 11.85/2.03    inference(ennf_transformation,[],[f13])).
% 11.85/2.03  
% 11.85/2.03  fof(f16,plain,(
% 11.85/2.03    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 11.85/2.03    introduced(choice_axiom,[])).
% 11.85/2.03  
% 11.85/2.03  fof(f17,plain,(
% 11.85/2.03    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 11.85/2.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).
% 11.85/2.03  
% 11.85/2.03  fof(f30,plain,(
% 11.85/2.03    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 11.85/2.03    inference(cnf_transformation,[],[f17])).
% 11.85/2.03  
% 11.85/2.03  fof(f11,axiom,(
% 11.85/2.03    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 11.85/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.03  
% 11.85/2.03  fof(f29,plain,(
% 11.85/2.03    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 11.85/2.03    inference(cnf_transformation,[],[f11])).
% 11.85/2.03  
% 11.85/2.03  fof(f39,plain,(
% 11.85/2.03    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 11.85/2.03    inference(definition_unfolding,[],[f29,f25])).
% 11.85/2.03  
% 11.85/2.03  fof(f3,axiom,(
% 11.85/2.03    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 11.85/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.03  
% 11.85/2.03  fof(f21,plain,(
% 11.85/2.03    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 11.85/2.03    inference(cnf_transformation,[],[f3])).
% 11.85/2.03  
% 11.85/2.03  fof(f34,plain,(
% 11.85/2.03    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 11.85/2.03    inference(definition_unfolding,[],[f21,f25])).
% 11.85/2.03  
% 11.85/2.03  fof(f5,axiom,(
% 11.85/2.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.85/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.03  
% 11.85/2.03  fof(f23,plain,(
% 11.85/2.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.85/2.03    inference(cnf_transformation,[],[f5])).
% 11.85/2.03  
% 11.85/2.03  fof(f10,axiom,(
% 11.85/2.03    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 11.85/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.03  
% 11.85/2.03  fof(f28,plain,(
% 11.85/2.03    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 11.85/2.03    inference(cnf_transformation,[],[f10])).
% 11.85/2.03  
% 11.85/2.03  fof(f38,plain,(
% 11.85/2.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 11.85/2.03    inference(definition_unfolding,[],[f28,f25])).
% 11.85/2.03  
% 11.85/2.03  fof(f8,axiom,(
% 11.85/2.03    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 11.85/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.03  
% 11.85/2.03  fof(f26,plain,(
% 11.85/2.03    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 11.85/2.03    inference(cnf_transformation,[],[f8])).
% 11.85/2.03  
% 11.85/2.03  fof(f36,plain,(
% 11.85/2.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 11.85/2.03    inference(definition_unfolding,[],[f26,f25,f25])).
% 11.85/2.03  
% 11.85/2.03  fof(f4,axiom,(
% 11.85/2.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.85/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.03  
% 11.85/2.03  fof(f22,plain,(
% 11.85/2.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.85/2.03    inference(cnf_transformation,[],[f4])).
% 11.85/2.03  
% 11.85/2.03  fof(f6,axiom,(
% 11.85/2.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.85/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.85/2.03  
% 11.85/2.03  fof(f24,plain,(
% 11.85/2.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.85/2.03    inference(cnf_transformation,[],[f6])).
% 11.85/2.03  
% 11.85/2.03  fof(f35,plain,(
% 11.85/2.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.85/2.03    inference(definition_unfolding,[],[f24,f25])).
% 11.85/2.03  
% 11.85/2.03  fof(f20,plain,(
% 11.85/2.03    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.85/2.03    inference(cnf_transformation,[],[f15])).
% 11.85/2.03  
% 11.85/2.03  fof(f32,plain,(
% 11.85/2.03    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.85/2.03    inference(definition_unfolding,[],[f20,f25])).
% 11.85/2.03  
% 11.85/2.03  fof(f31,plain,(
% 11.85/2.03    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 11.85/2.03    inference(cnf_transformation,[],[f17])).
% 11.85/2.03  
% 11.85/2.03  cnf(c_8,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 11.85/2.03      inference(cnf_transformation,[],[f37]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_2,plain,
% 11.85/2.03      ( ~ r1_xboole_0(X0,X1)
% 11.85/2.03      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.85/2.03      inference(cnf_transformation,[],[f33]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_48,plain,
% 11.85/2.03      ( ~ r1_xboole_0(X0,X1)
% 11.85/2.03      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.85/2.03      inference(prop_impl,[status(thm)],[c_2]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_12,negated_conjecture,
% 11.85/2.03      ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 11.85/2.03      inference(cnf_transformation,[],[f30]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_91,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 11.85/2.03      | k4_xboole_0(sK1,sK2) != X1
% 11.85/2.03      | sK0 != X0 ),
% 11.85/2.03      inference(resolution_lifted,[status(thm)],[c_48,c_12]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_92,plain,
% 11.85/2.03      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 11.85/2.03      inference(unflattening,[status(thm)],[c_91]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_10,plain,
% 11.85/2.03      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 11.85/2.03      inference(cnf_transformation,[],[f39]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_400,plain,
% 11.85/2.03      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_92,c_10]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_3,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.85/2.03      inference(cnf_transformation,[],[f34]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_5,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.85/2.03      inference(cnf_transformation,[],[f23]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_117,plain,
% 11.85/2.03      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.85/2.03      inference(light_normalisation,[status(thm)],[c_3,c_5]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_9,plain,
% 11.85/2.03      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 11.85/2.03      inference(cnf_transformation,[],[f38]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_298,plain,
% 11.85/2.03      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_117,c_9]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_301,plain,
% 11.85/2.03      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.85/2.03      inference(light_normalisation,[status(thm)],[c_298,c_5]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_421,plain,
% 11.85/2.03      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X0) ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_400,c_301]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_7,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 11.85/2.03      inference(cnf_transformation,[],[f36]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_405,plain,
% 11.85/2.03      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_117,c_10]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_413,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.85/2.03      inference(light_normalisation,[status(thm)],[c_405,c_5]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_4,plain,
% 11.85/2.03      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.85/2.03      inference(cnf_transformation,[],[f22]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_408,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_10,c_4]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_412,plain,
% 11.85/2.03      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_408,c_5,c_117]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_2249,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 11.85/2.03      inference(light_normalisation,[status(thm)],[c_413,c_412,c_413]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_2254,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_7,c_2249]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_4054,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK0,X0)))) = k4_xboole_0(X0,k4_xboole_0(sK1,sK2)) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_421,c_2254]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_4865,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X1)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X1,X0))))) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,sK2)) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_8,c_4054]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_6,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.85/2.03      inference(cnf_transformation,[],[f35]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_348,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_1902,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_421,c_348]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_2006,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,X0) ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_1902,c_6]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_5015,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X1)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X1,X0))))) = k4_xboole_0(sK0,X0) ),
% 11.85/2.03      inference(light_normalisation,[status(thm)],[c_4865,c_2006]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_492,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_6,c_8]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_580,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 11.85/2.03      inference(light_normalisation,[status(thm)],[c_492,c_348]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_5016,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(sK0,X0) ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_5015,c_8,c_580]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_762,plain,
% 11.85/2.03      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_7,c_421]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_12435,plain,
% 11.85/2.03      ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK2))) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_5016,c_762]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_398,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_6,c_10]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_1948,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X3))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),X3)) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_348,c_10]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_12474,plain,
% 11.85/2.03      ( k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))) = sK0 ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_12435,c_9,c_398,c_1948]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_364,plain,
% 11.85/2.03      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_7,c_4]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_15345,plain,
% 11.85/2.03      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK2),sK1),k4_xboole_0(sK0,sK0)) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_12474,c_364]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_15351,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) = k4_xboole_0(sK0,sK2) ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_15345,c_6,c_117,c_301,c_412]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_2617,plain,
% 11.85/2.03      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))))) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_8,c_364]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_1947,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X3)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X2),X3)) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_348,c_8]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_1961,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,X2),X3)) ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_1947,c_1948]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_2664,plain,
% 11.85/2.03      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_2617,c_8,c_10,c_1961]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_2287,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_2249,c_10]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_2313,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
% 11.85/2.03      inference(light_normalisation,[status(thm)],[c_2287,c_117]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_2314,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X0))) = k4_xboole_0(X0,X1) ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_2313,c_301]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_2665,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_2664,c_7,c_10,c_2314]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_25219,plain,
% 11.85/2.03      ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(sK0,sK2))) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_15351,c_2665]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_4873,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2)) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_762,c_4054]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_5005,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))))) = k4_xboole_0(sK0,X0) ),
% 11.85/2.03      inference(light_normalisation,[status(thm)],[c_4873,c_421,c_2006]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_5006,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(sK0,X0),X0) = k4_xboole_0(sK0,X0) ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_5005,c_6,c_580]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_5289,plain,
% 11.85/2.03      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X0),X1),k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,X0))) = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X1,X0)) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_5006,c_10]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_5337,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X1,X0)) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_5289,c_117,c_301]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_25550,plain,
% 11.85/2.03      ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK0,sK2),sK0))) = k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(sK0,sK2))) ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_25219,c_5337]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_509,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_117,c_8]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_544,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 11.85/2.03      inference(light_normalisation,[status(thm)],[c_509,c_5,c_413]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_545,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_544,c_7,c_117,c_412]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_1437,plain,
% 11.85/2.03      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 11.85/2.03      inference(superposition,[status(thm)],[c_6,c_545]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_25551,plain,
% 11.85/2.03      ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK1,X0) ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_25550,c_5,c_1437]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_1,plain,
% 11.85/2.03      ( r1_xboole_0(X0,X1)
% 11.85/2.03      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 11.85/2.03      inference(cnf_transformation,[],[f32]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_46,plain,
% 11.85/2.03      ( r1_xboole_0(X0,X1)
% 11.85/2.03      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 11.85/2.03      inference(prop_impl,[status(thm)],[c_1]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_11,negated_conjecture,
% 11.85/2.03      ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
% 11.85/2.03      inference(cnf_transformation,[],[f31]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_86,plain,
% 11.85/2.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 11.85/2.03      | k4_xboole_0(sK0,sK2) != X1
% 11.85/2.03      | sK1 != X0 ),
% 11.85/2.03      inference(resolution_lifted,[status(thm)],[c_46,c_11]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_87,plain,
% 11.85/2.03      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != k1_xboole_0 ),
% 11.85/2.03      inference(unflattening,[status(thm)],[c_86]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_26413,plain,
% 11.85/2.03      ( k4_xboole_0(sK1,sK1) != k1_xboole_0 ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_25551,c_87]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_26414,plain,
% 11.85/2.03      ( k1_xboole_0 != k1_xboole_0 ),
% 11.85/2.03      inference(demodulation,[status(thm)],[c_26413,c_117]) ).
% 11.85/2.03  
% 11.85/2.03  cnf(c_26415,plain,
% 11.85/2.03      ( $false ),
% 11.85/2.03      inference(equality_resolution_simp,[status(thm)],[c_26414]) ).
% 11.85/2.03  
% 11.85/2.03  
% 11.85/2.03  % SZS output end CNFRefutation for theBenchmark.p
% 11.85/2.03  
% 11.85/2.03  ------                               Statistics
% 11.85/2.03  
% 11.85/2.03  ------ General
% 11.85/2.03  
% 11.85/2.03  abstr_ref_over_cycles:                  0
% 11.85/2.03  abstr_ref_under_cycles:                 0
% 11.85/2.03  gc_basic_clause_elim:                   0
% 11.85/2.03  forced_gc_time:                         0
% 11.85/2.03  parsing_time:                           0.009
% 11.85/2.03  unif_index_cands_time:                  0.
% 11.85/2.03  unif_index_add_time:                    0.
% 11.85/2.03  orderings_time:                         0.
% 11.85/2.03  out_proof_time:                         0.011
% 11.85/2.03  total_time:                             1.332
% 11.85/2.03  num_of_symbols:                         38
% 11.85/2.03  num_of_terms:                           42030
% 11.85/2.03  
% 11.85/2.03  ------ Preprocessing
% 11.85/2.03  
% 11.85/2.03  num_of_splits:                          0
% 11.85/2.03  num_of_split_atoms:                     0
% 11.85/2.03  num_of_reused_defs:                     0
% 11.85/2.03  num_eq_ax_congr_red:                    0
% 11.85/2.03  num_of_sem_filtered_clauses:            0
% 11.85/2.03  num_of_subtypes:                        0
% 11.85/2.03  monotx_restored_types:                  0
% 11.85/2.03  sat_num_of_epr_types:                   0
% 11.85/2.03  sat_num_of_non_cyclic_types:            0
% 11.85/2.03  sat_guarded_non_collapsed_types:        0
% 11.85/2.03  num_pure_diseq_elim:                    0
% 11.85/2.03  simp_replaced_by:                       0
% 11.85/2.03  res_preprocessed:                       41
% 11.85/2.03  prep_upred:                             0
% 11.85/2.03  prep_unflattend:                        4
% 11.85/2.03  smt_new_axioms:                         0
% 11.85/2.03  pred_elim_cands:                        0
% 11.85/2.03  pred_elim:                              1
% 11.85/2.03  pred_elim_cl:                           1
% 11.85/2.03  pred_elim_cycles:                       2
% 11.85/2.03  merged_defs:                            2
% 11.85/2.03  merged_defs_ncl:                        0
% 11.85/2.03  bin_hyper_res:                          2
% 11.85/2.03  prep_cycles:                            3
% 11.85/2.03  pred_elim_time:                         0.
% 11.85/2.03  splitting_time:                         0.
% 11.85/2.03  sem_filter_time:                        0.
% 11.85/2.03  monotx_time:                            0.
% 11.85/2.03  subtype_inf_time:                       0.
% 11.85/2.03  
% 11.85/2.03  ------ Problem properties
% 11.85/2.03  
% 11.85/2.03  clauses:                                12
% 11.85/2.03  conjectures:                            0
% 11.85/2.03  epr:                                    0
% 11.85/2.03  horn:                                   12
% 11.85/2.03  ground:                                 3
% 11.85/2.03  unary:                                  11
% 11.85/2.03  binary:                                 1
% 11.85/2.03  lits:                                   13
% 11.85/2.03  lits_eq:                                13
% 11.85/2.03  fd_pure:                                0
% 11.85/2.03  fd_pseudo:                              0
% 11.85/2.03  fd_cond:                                0
% 11.85/2.03  fd_pseudo_cond:                         0
% 11.85/2.03  ac_symbols:                             0
% 11.85/2.03  
% 11.85/2.03  ------ Propositional Solver
% 11.85/2.03  
% 11.85/2.03  prop_solver_calls:                      29
% 11.85/2.03  prop_fast_solver_calls:                 282
% 11.85/2.03  smt_solver_calls:                       0
% 11.85/2.03  smt_fast_solver_calls:                  0
% 11.85/2.03  prop_num_of_clauses:                    4969
% 11.85/2.03  prop_preprocess_simplified:             5034
% 11.85/2.03  prop_fo_subsumed:                       0
% 11.85/2.03  prop_solver_time:                       0.
% 11.85/2.03  smt_solver_time:                        0.
% 11.85/2.03  smt_fast_solver_time:                   0.
% 11.85/2.03  prop_fast_solver_time:                  0.
% 11.85/2.03  prop_unsat_core_time:                   0.
% 11.85/2.03  
% 11.85/2.03  ------ QBF
% 11.85/2.03  
% 11.85/2.03  qbf_q_res:                              0
% 11.85/2.03  qbf_num_tautologies:                    0
% 11.85/2.03  qbf_prep_cycles:                        0
% 11.85/2.03  
% 11.85/2.03  ------ BMC1
% 11.85/2.03  
% 11.85/2.03  bmc1_current_bound:                     -1
% 11.85/2.03  bmc1_last_solved_bound:                 -1
% 11.85/2.03  bmc1_unsat_core_size:                   -1
% 11.85/2.03  bmc1_unsat_core_parents_size:           -1
% 11.85/2.03  bmc1_merge_next_fun:                    0
% 11.85/2.03  bmc1_unsat_core_clauses_time:           0.
% 11.85/2.03  
% 11.85/2.03  ------ Instantiation
% 11.85/2.03  
% 11.85/2.03  inst_num_of_clauses:                    1583
% 11.85/2.03  inst_num_in_passive:                    785
% 11.85/2.03  inst_num_in_active:                     594
% 11.85/2.03  inst_num_in_unprocessed:                204
% 11.85/2.03  inst_num_of_loops:                      710
% 11.85/2.03  inst_num_of_learning_restarts:          0
% 11.85/2.03  inst_num_moves_active_passive:          111
% 11.85/2.03  inst_lit_activity:                      0
% 11.85/2.03  inst_lit_activity_moves:                0
% 11.85/2.03  inst_num_tautologies:                   0
% 11.85/2.03  inst_num_prop_implied:                  0
% 11.85/2.03  inst_num_existing_simplified:           0
% 11.85/2.03  inst_num_eq_res_simplified:             0
% 11.85/2.03  inst_num_child_elim:                    0
% 11.85/2.03  inst_num_of_dismatching_blockings:      676
% 11.85/2.03  inst_num_of_non_proper_insts:           1899
% 11.85/2.03  inst_num_of_duplicates:                 0
% 11.85/2.03  inst_inst_num_from_inst_to_res:         0
% 11.85/2.03  inst_dismatching_checking_time:         0.
% 11.85/2.03  
% 11.85/2.03  ------ Resolution
% 11.85/2.03  
% 11.85/2.03  res_num_of_clauses:                     0
% 11.85/2.03  res_num_in_passive:                     0
% 11.85/2.03  res_num_in_active:                      0
% 11.85/2.03  res_num_of_loops:                       44
% 11.85/2.03  res_forward_subset_subsumed:            443
% 11.85/2.03  res_backward_subset_subsumed:           4
% 11.85/2.03  res_forward_subsumed:                   0
% 11.85/2.03  res_backward_subsumed:                  0
% 11.85/2.03  res_forward_subsumption_resolution:     0
% 11.85/2.03  res_backward_subsumption_resolution:    0
% 11.85/2.03  res_clause_to_clause_subsumption:       31345
% 11.85/2.03  res_orphan_elimination:                 0
% 11.85/2.03  res_tautology_del:                      140
% 11.85/2.03  res_num_eq_res_simplified:              0
% 11.85/2.03  res_num_sel_changes:                    0
% 11.85/2.03  res_moves_from_active_to_pass:          0
% 11.85/2.03  
% 11.85/2.03  ------ Superposition
% 11.85/2.03  
% 11.85/2.03  sup_time_total:                         0.
% 11.85/2.03  sup_time_generating:                    0.
% 11.85/2.03  sup_time_sim_full:                      0.
% 11.85/2.03  sup_time_sim_immed:                     0.
% 11.85/2.03  
% 11.85/2.03  sup_num_of_clauses:                     1540
% 11.85/2.03  sup_num_in_active:                      120
% 11.85/2.03  sup_num_in_passive:                     1420
% 11.85/2.03  sup_num_of_loops:                       141
% 11.85/2.03  sup_fw_superposition:                   7012
% 11.85/2.03  sup_bw_superposition:                   5565
% 11.85/2.03  sup_immediate_simplified:               6902
% 11.85/2.03  sup_given_eliminated:                   8
% 11.85/2.03  comparisons_done:                       0
% 11.85/2.03  comparisons_avoided:                    0
% 11.85/2.03  
% 11.85/2.03  ------ Simplifications
% 11.85/2.03  
% 11.85/2.03  
% 11.85/2.03  sim_fw_subset_subsumed:                 0
% 11.85/2.03  sim_bw_subset_subsumed:                 0
% 11.85/2.03  sim_fw_subsumed:                        1181
% 11.85/2.03  sim_bw_subsumed:                        41
% 11.85/2.03  sim_fw_subsumption_res:                 0
% 11.85/2.03  sim_bw_subsumption_res:                 0
% 11.85/2.03  sim_tautology_del:                      0
% 11.85/2.03  sim_eq_tautology_del:                   3356
% 11.85/2.03  sim_eq_res_simp:                        0
% 11.85/2.03  sim_fw_demodulated:                     5694
% 11.85/2.03  sim_bw_demodulated:                     109
% 11.85/2.03  sim_light_normalised:                   2294
% 11.85/2.03  sim_joinable_taut:                      0
% 11.85/2.03  sim_joinable_simp:                      0
% 11.85/2.03  sim_ac_normalised:                      0
% 11.85/2.03  sim_smt_subsumption:                    0
% 11.85/2.03  
%------------------------------------------------------------------------------
