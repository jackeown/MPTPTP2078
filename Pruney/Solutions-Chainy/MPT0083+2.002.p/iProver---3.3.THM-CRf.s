%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:08 EST 2020

% Result     : Theorem 55.89s
% Output     : CNFRefutation 55.89s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 299 expanded)
%              Number of clauses        :   55 ( 111 expanded)
%              Number of leaves         :   12 (  80 expanded)
%              Depth                    :   19
%              Number of atoms          :  114 ( 350 expanded)
%              Number of equality atoms :   85 ( 285 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f20,f26])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f29,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f29,f26,f26])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f26,f26])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f21,f26])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f19,f26])).

fof(f28,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f26])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_338,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_7,c_5])).

cnf(c_4352,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_338])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_44,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_83,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != X1
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_10])).

cnf(c_84,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_83])).

cnf(c_115,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_84,c_7])).

cnf(c_145439,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4352,c_115])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_9,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_114,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_6])).

cnf(c_341,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_114])).

cnf(c_342,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_341,c_5])).

cnf(c_953,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_342])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_46,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_88,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_46,c_11])).

cnf(c_89,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_88])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_402,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_89,c_8])).

cnf(c_422,plain,
    ( k4_xboole_0(sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_402,c_6])).

cnf(c_507,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_422,c_7])).

cnf(c_700,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_507])).

cnf(c_708,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_700,c_507])).

cnf(c_1355,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_953,c_708])).

cnf(c_1356,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = sK0 ),
    inference(demodulation,[status(thm)],[c_1355,c_6])).

cnf(c_1438,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) = sK0 ),
    inference(superposition,[status(thm)],[c_1,c_1356])).

cnf(c_339,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_343,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_339,c_7])).

cnf(c_5429,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_343,c_4352])).

cnf(c_5484,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0))) = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_1438,c_5429])).

cnf(c_5793,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5484,c_114])).

cnf(c_410,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_8,c_5])).

cnf(c_414,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_410,c_9])).

cnf(c_2456,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_414])).

cnf(c_6004,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_342,c_2456])).

cnf(c_6036,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_6004,c_6])).

cnf(c_11270,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_6036])).

cnf(c_409,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_8,c_7])).

cnf(c_415,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_409,c_7])).

cnf(c_15811,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_11270,c_415])).

cnf(c_6019,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_2456,c_0])).

cnf(c_334,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_7,c_7])).

cnf(c_344,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_334,c_7])).

cnf(c_8643,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3))) = k4_xboole_0(X0,k2_xboole_0(X1,X3)) ),
    inference(superposition,[status(thm)],[c_6019,c_344])).

cnf(c_16043,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_15811,c_8643])).

cnf(c_145440,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_145439,c_5793,c_16043])).

cnf(c_145441,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_145440])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 55.89/7.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.89/7.51  
% 55.89/7.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.89/7.51  
% 55.89/7.51  ------  iProver source info
% 55.89/7.51  
% 55.89/7.51  git: date: 2020-06-30 10:37:57 +0100
% 55.89/7.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.89/7.51  git: non_committed_changes: false
% 55.89/7.51  git: last_make_outside_of_git: false
% 55.89/7.51  
% 55.89/7.51  ------ 
% 55.89/7.51  
% 55.89/7.51  ------ Input Options
% 55.89/7.51  
% 55.89/7.51  --out_options                           all
% 55.89/7.51  --tptp_safe_out                         true
% 55.89/7.51  --problem_path                          ""
% 55.89/7.51  --include_path                          ""
% 55.89/7.51  --clausifier                            res/vclausify_rel
% 55.89/7.51  --clausifier_options                    ""
% 55.89/7.51  --stdin                                 false
% 55.89/7.51  --stats_out                             all
% 55.89/7.51  
% 55.89/7.51  ------ General Options
% 55.89/7.51  
% 55.89/7.51  --fof                                   false
% 55.89/7.51  --time_out_real                         305.
% 55.89/7.51  --time_out_virtual                      -1.
% 55.89/7.51  --symbol_type_check                     false
% 55.89/7.51  --clausify_out                          false
% 55.89/7.51  --sig_cnt_out                           false
% 55.89/7.51  --trig_cnt_out                          false
% 55.89/7.51  --trig_cnt_out_tolerance                1.
% 55.89/7.51  --trig_cnt_out_sk_spl                   false
% 55.89/7.51  --abstr_cl_out                          false
% 55.89/7.51  
% 55.89/7.51  ------ Global Options
% 55.89/7.51  
% 55.89/7.51  --schedule                              default
% 55.89/7.51  --add_important_lit                     false
% 55.89/7.51  --prop_solver_per_cl                    1000
% 55.89/7.51  --min_unsat_core                        false
% 55.89/7.51  --soft_assumptions                      false
% 55.89/7.51  --soft_lemma_size                       3
% 55.89/7.51  --prop_impl_unit_size                   0
% 55.89/7.51  --prop_impl_unit                        []
% 55.89/7.51  --share_sel_clauses                     true
% 55.89/7.51  --reset_solvers                         false
% 55.89/7.51  --bc_imp_inh                            [conj_cone]
% 55.89/7.51  --conj_cone_tolerance                   3.
% 55.89/7.51  --extra_neg_conj                        none
% 55.89/7.51  --large_theory_mode                     true
% 55.89/7.51  --prolific_symb_bound                   200
% 55.89/7.51  --lt_threshold                          2000
% 55.89/7.51  --clause_weak_htbl                      true
% 55.89/7.51  --gc_record_bc_elim                     false
% 55.89/7.51  
% 55.89/7.51  ------ Preprocessing Options
% 55.89/7.51  
% 55.89/7.51  --preprocessing_flag                    true
% 55.89/7.51  --time_out_prep_mult                    0.1
% 55.89/7.51  --splitting_mode                        input
% 55.89/7.51  --splitting_grd                         true
% 55.89/7.51  --splitting_cvd                         false
% 55.89/7.51  --splitting_cvd_svl                     false
% 55.89/7.51  --splitting_nvd                         32
% 55.89/7.51  --sub_typing                            true
% 55.89/7.51  --prep_gs_sim                           true
% 55.89/7.51  --prep_unflatten                        true
% 55.89/7.51  --prep_res_sim                          true
% 55.89/7.51  --prep_upred                            true
% 55.89/7.51  --prep_sem_filter                       exhaustive
% 55.89/7.51  --prep_sem_filter_out                   false
% 55.89/7.51  --pred_elim                             true
% 55.89/7.51  --res_sim_input                         true
% 55.89/7.51  --eq_ax_congr_red                       true
% 55.89/7.51  --pure_diseq_elim                       true
% 55.89/7.51  --brand_transform                       false
% 55.89/7.51  --non_eq_to_eq                          false
% 55.89/7.51  --prep_def_merge                        true
% 55.89/7.51  --prep_def_merge_prop_impl              false
% 55.89/7.51  --prep_def_merge_mbd                    true
% 55.89/7.51  --prep_def_merge_tr_red                 false
% 55.89/7.51  --prep_def_merge_tr_cl                  false
% 55.89/7.51  --smt_preprocessing                     true
% 55.89/7.51  --smt_ac_axioms                         fast
% 55.89/7.51  --preprocessed_out                      false
% 55.89/7.51  --preprocessed_stats                    false
% 55.89/7.51  
% 55.89/7.51  ------ Abstraction refinement Options
% 55.89/7.51  
% 55.89/7.51  --abstr_ref                             []
% 55.89/7.51  --abstr_ref_prep                        false
% 55.89/7.51  --abstr_ref_until_sat                   false
% 55.89/7.51  --abstr_ref_sig_restrict                funpre
% 55.89/7.51  --abstr_ref_af_restrict_to_split_sk     false
% 55.89/7.51  --abstr_ref_under                       []
% 55.89/7.51  
% 55.89/7.51  ------ SAT Options
% 55.89/7.51  
% 55.89/7.51  --sat_mode                              false
% 55.89/7.51  --sat_fm_restart_options                ""
% 55.89/7.51  --sat_gr_def                            false
% 55.89/7.51  --sat_epr_types                         true
% 55.89/7.51  --sat_non_cyclic_types                  false
% 55.89/7.51  --sat_finite_models                     false
% 55.89/7.51  --sat_fm_lemmas                         false
% 55.89/7.51  --sat_fm_prep                           false
% 55.89/7.51  --sat_fm_uc_incr                        true
% 55.89/7.51  --sat_out_model                         small
% 55.89/7.51  --sat_out_clauses                       false
% 55.89/7.51  
% 55.89/7.51  ------ QBF Options
% 55.89/7.51  
% 55.89/7.51  --qbf_mode                              false
% 55.89/7.51  --qbf_elim_univ                         false
% 55.89/7.51  --qbf_dom_inst                          none
% 55.89/7.51  --qbf_dom_pre_inst                      false
% 55.89/7.51  --qbf_sk_in                             false
% 55.89/7.51  --qbf_pred_elim                         true
% 55.89/7.51  --qbf_split                             512
% 55.89/7.51  
% 55.89/7.51  ------ BMC1 Options
% 55.89/7.51  
% 55.89/7.51  --bmc1_incremental                      false
% 55.89/7.51  --bmc1_axioms                           reachable_all
% 55.89/7.51  --bmc1_min_bound                        0
% 55.89/7.51  --bmc1_max_bound                        -1
% 55.89/7.51  --bmc1_max_bound_default                -1
% 55.89/7.51  --bmc1_symbol_reachability              true
% 55.89/7.51  --bmc1_property_lemmas                  false
% 55.89/7.51  --bmc1_k_induction                      false
% 55.89/7.51  --bmc1_non_equiv_states                 false
% 55.89/7.51  --bmc1_deadlock                         false
% 55.89/7.51  --bmc1_ucm                              false
% 55.89/7.51  --bmc1_add_unsat_core                   none
% 55.89/7.51  --bmc1_unsat_core_children              false
% 55.89/7.51  --bmc1_unsat_core_extrapolate_axioms    false
% 55.89/7.51  --bmc1_out_stat                         full
% 55.89/7.51  --bmc1_ground_init                      false
% 55.89/7.51  --bmc1_pre_inst_next_state              false
% 55.89/7.51  --bmc1_pre_inst_state                   false
% 55.89/7.51  --bmc1_pre_inst_reach_state             false
% 55.89/7.51  --bmc1_out_unsat_core                   false
% 55.89/7.51  --bmc1_aig_witness_out                  false
% 55.89/7.51  --bmc1_verbose                          false
% 55.89/7.51  --bmc1_dump_clauses_tptp                false
% 55.89/7.51  --bmc1_dump_unsat_core_tptp             false
% 55.89/7.51  --bmc1_dump_file                        -
% 55.89/7.51  --bmc1_ucm_expand_uc_limit              128
% 55.89/7.51  --bmc1_ucm_n_expand_iterations          6
% 55.89/7.51  --bmc1_ucm_extend_mode                  1
% 55.89/7.51  --bmc1_ucm_init_mode                    2
% 55.89/7.51  --bmc1_ucm_cone_mode                    none
% 55.89/7.51  --bmc1_ucm_reduced_relation_type        0
% 55.89/7.51  --bmc1_ucm_relax_model                  4
% 55.89/7.51  --bmc1_ucm_full_tr_after_sat            true
% 55.89/7.51  --bmc1_ucm_expand_neg_assumptions       false
% 55.89/7.51  --bmc1_ucm_layered_model                none
% 55.89/7.51  --bmc1_ucm_max_lemma_size               10
% 55.89/7.51  
% 55.89/7.51  ------ AIG Options
% 55.89/7.51  
% 55.89/7.51  --aig_mode                              false
% 55.89/7.51  
% 55.89/7.51  ------ Instantiation Options
% 55.89/7.51  
% 55.89/7.51  --instantiation_flag                    true
% 55.89/7.51  --inst_sos_flag                         true
% 55.89/7.51  --inst_sos_phase                        true
% 55.89/7.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.89/7.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.89/7.51  --inst_lit_sel_side                     num_symb
% 55.89/7.51  --inst_solver_per_active                1400
% 55.89/7.51  --inst_solver_calls_frac                1.
% 55.89/7.51  --inst_passive_queue_type               priority_queues
% 55.89/7.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.89/7.51  --inst_passive_queues_freq              [25;2]
% 55.89/7.51  --inst_dismatching                      true
% 55.89/7.51  --inst_eager_unprocessed_to_passive     true
% 55.89/7.51  --inst_prop_sim_given                   true
% 55.89/7.51  --inst_prop_sim_new                     false
% 55.89/7.51  --inst_subs_new                         false
% 55.89/7.51  --inst_eq_res_simp                      false
% 55.89/7.51  --inst_subs_given                       false
% 55.89/7.51  --inst_orphan_elimination               true
% 55.89/7.51  --inst_learning_loop_flag               true
% 55.89/7.51  --inst_learning_start                   3000
% 55.89/7.51  --inst_learning_factor                  2
% 55.89/7.51  --inst_start_prop_sim_after_learn       3
% 55.89/7.51  --inst_sel_renew                        solver
% 55.89/7.51  --inst_lit_activity_flag                true
% 55.89/7.51  --inst_restr_to_given                   false
% 55.89/7.51  --inst_activity_threshold               500
% 55.89/7.51  --inst_out_proof                        true
% 55.89/7.51  
% 55.89/7.51  ------ Resolution Options
% 55.89/7.51  
% 55.89/7.51  --resolution_flag                       true
% 55.89/7.51  --res_lit_sel                           adaptive
% 55.89/7.51  --res_lit_sel_side                      none
% 55.89/7.51  --res_ordering                          kbo
% 55.89/7.51  --res_to_prop_solver                    active
% 55.89/7.51  --res_prop_simpl_new                    false
% 55.89/7.51  --res_prop_simpl_given                  true
% 55.89/7.51  --res_passive_queue_type                priority_queues
% 55.89/7.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.89/7.51  --res_passive_queues_freq               [15;5]
% 55.89/7.51  --res_forward_subs                      full
% 55.89/7.51  --res_backward_subs                     full
% 55.89/7.51  --res_forward_subs_resolution           true
% 55.89/7.51  --res_backward_subs_resolution          true
% 55.89/7.51  --res_orphan_elimination                true
% 55.89/7.51  --res_time_limit                        2.
% 55.89/7.51  --res_out_proof                         true
% 55.89/7.51  
% 55.89/7.51  ------ Superposition Options
% 55.89/7.51  
% 55.89/7.51  --superposition_flag                    true
% 55.89/7.51  --sup_passive_queue_type                priority_queues
% 55.89/7.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.89/7.51  --sup_passive_queues_freq               [8;1;4]
% 55.89/7.51  --demod_completeness_check              fast
% 55.89/7.51  --demod_use_ground                      true
% 55.89/7.51  --sup_to_prop_solver                    passive
% 55.89/7.51  --sup_prop_simpl_new                    true
% 55.89/7.51  --sup_prop_simpl_given                  true
% 55.89/7.51  --sup_fun_splitting                     true
% 55.89/7.51  --sup_smt_interval                      50000
% 55.89/7.51  
% 55.89/7.51  ------ Superposition Simplification Setup
% 55.89/7.51  
% 55.89/7.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.89/7.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.89/7.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.89/7.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.89/7.51  --sup_full_triv                         [TrivRules;PropSubs]
% 55.89/7.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.89/7.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.89/7.51  --sup_immed_triv                        [TrivRules]
% 55.89/7.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.89/7.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.89/7.51  --sup_immed_bw_main                     []
% 55.89/7.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.89/7.51  --sup_input_triv                        [Unflattening;TrivRules]
% 55.89/7.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.89/7.51  --sup_input_bw                          []
% 55.89/7.51  
% 55.89/7.51  ------ Combination Options
% 55.89/7.51  
% 55.89/7.51  --comb_res_mult                         3
% 55.89/7.51  --comb_sup_mult                         2
% 55.89/7.51  --comb_inst_mult                        10
% 55.89/7.51  
% 55.89/7.51  ------ Debug Options
% 55.89/7.51  
% 55.89/7.51  --dbg_backtrace                         false
% 55.89/7.51  --dbg_dump_prop_clauses                 false
% 55.89/7.51  --dbg_dump_prop_clauses_file            -
% 55.89/7.51  --dbg_out_stat                          false
% 55.89/7.51  ------ Parsing...
% 55.89/7.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.89/7.51  
% 55.89/7.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 55.89/7.51  
% 55.89/7.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.89/7.51  
% 55.89/7.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 55.89/7.51  ------ Proving...
% 55.89/7.51  ------ Problem Properties 
% 55.89/7.51  
% 55.89/7.51  
% 55.89/7.51  clauses                                 11
% 55.89/7.51  conjectures                             0
% 55.89/7.51  EPR                                     0
% 55.89/7.51  Horn                                    11
% 55.89/7.51  unary                                   10
% 55.89/7.51  binary                                  1
% 55.89/7.51  lits                                    12
% 55.89/7.51  lits eq                                 12
% 55.89/7.51  fd_pure                                 0
% 55.89/7.51  fd_pseudo                               0
% 55.89/7.51  fd_cond                                 0
% 55.89/7.51  fd_pseudo_cond                          0
% 55.89/7.51  AC symbols                              0
% 55.89/7.51  
% 55.89/7.51  ------ Schedule dynamic 5 is on 
% 55.89/7.51  
% 55.89/7.51  ------ no conjectures: strip conj schedule 
% 55.89/7.51  
% 55.89/7.51  ------ pure equality problem: resolution off 
% 55.89/7.51  
% 55.89/7.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 55.89/7.51  
% 55.89/7.51  
% 55.89/7.51  ------ 
% 55.89/7.51  Current options:
% 55.89/7.51  ------ 
% 55.89/7.51  
% 55.89/7.51  ------ Input Options
% 55.89/7.51  
% 55.89/7.51  --out_options                           all
% 55.89/7.51  --tptp_safe_out                         true
% 55.89/7.51  --problem_path                          ""
% 55.89/7.51  --include_path                          ""
% 55.89/7.51  --clausifier                            res/vclausify_rel
% 55.89/7.51  --clausifier_options                    ""
% 55.89/7.51  --stdin                                 false
% 55.89/7.51  --stats_out                             all
% 55.89/7.51  
% 55.89/7.51  ------ General Options
% 55.89/7.51  
% 55.89/7.51  --fof                                   false
% 55.89/7.51  --time_out_real                         305.
% 55.89/7.51  --time_out_virtual                      -1.
% 55.89/7.51  --symbol_type_check                     false
% 55.89/7.51  --clausify_out                          false
% 55.89/7.51  --sig_cnt_out                           false
% 55.89/7.51  --trig_cnt_out                          false
% 55.89/7.51  --trig_cnt_out_tolerance                1.
% 55.89/7.51  --trig_cnt_out_sk_spl                   false
% 55.89/7.51  --abstr_cl_out                          false
% 55.89/7.51  
% 55.89/7.51  ------ Global Options
% 55.89/7.51  
% 55.89/7.51  --schedule                              default
% 55.89/7.51  --add_important_lit                     false
% 55.89/7.51  --prop_solver_per_cl                    1000
% 55.89/7.51  --min_unsat_core                        false
% 55.89/7.51  --soft_assumptions                      false
% 55.89/7.51  --soft_lemma_size                       3
% 55.89/7.51  --prop_impl_unit_size                   0
% 55.89/7.51  --prop_impl_unit                        []
% 55.89/7.51  --share_sel_clauses                     true
% 55.89/7.51  --reset_solvers                         false
% 55.89/7.51  --bc_imp_inh                            [conj_cone]
% 55.89/7.51  --conj_cone_tolerance                   3.
% 55.89/7.51  --extra_neg_conj                        none
% 55.89/7.51  --large_theory_mode                     true
% 55.89/7.51  --prolific_symb_bound                   200
% 55.89/7.51  --lt_threshold                          2000
% 55.89/7.51  --clause_weak_htbl                      true
% 55.89/7.51  --gc_record_bc_elim                     false
% 55.89/7.51  
% 55.89/7.51  ------ Preprocessing Options
% 55.89/7.51  
% 55.89/7.51  --preprocessing_flag                    true
% 55.89/7.51  --time_out_prep_mult                    0.1
% 55.89/7.51  --splitting_mode                        input
% 55.89/7.51  --splitting_grd                         true
% 55.89/7.51  --splitting_cvd                         false
% 55.89/7.51  --splitting_cvd_svl                     false
% 55.89/7.51  --splitting_nvd                         32
% 55.89/7.51  --sub_typing                            true
% 55.89/7.51  --prep_gs_sim                           true
% 55.89/7.51  --prep_unflatten                        true
% 55.89/7.51  --prep_res_sim                          true
% 55.89/7.51  --prep_upred                            true
% 55.89/7.51  --prep_sem_filter                       exhaustive
% 55.89/7.51  --prep_sem_filter_out                   false
% 55.89/7.51  --pred_elim                             true
% 55.89/7.51  --res_sim_input                         true
% 55.89/7.51  --eq_ax_congr_red                       true
% 55.89/7.51  --pure_diseq_elim                       true
% 55.89/7.51  --brand_transform                       false
% 55.89/7.51  --non_eq_to_eq                          false
% 55.89/7.51  --prep_def_merge                        true
% 55.89/7.51  --prep_def_merge_prop_impl              false
% 55.89/7.51  --prep_def_merge_mbd                    true
% 55.89/7.51  --prep_def_merge_tr_red                 false
% 55.89/7.51  --prep_def_merge_tr_cl                  false
% 55.89/7.51  --smt_preprocessing                     true
% 55.89/7.51  --smt_ac_axioms                         fast
% 55.89/7.51  --preprocessed_out                      false
% 55.89/7.51  --preprocessed_stats                    false
% 55.89/7.51  
% 55.89/7.51  ------ Abstraction refinement Options
% 55.89/7.51  
% 55.89/7.51  --abstr_ref                             []
% 55.89/7.51  --abstr_ref_prep                        false
% 55.89/7.51  --abstr_ref_until_sat                   false
% 55.89/7.51  --abstr_ref_sig_restrict                funpre
% 55.89/7.51  --abstr_ref_af_restrict_to_split_sk     false
% 55.89/7.51  --abstr_ref_under                       []
% 55.89/7.51  
% 55.89/7.51  ------ SAT Options
% 55.89/7.51  
% 55.89/7.51  --sat_mode                              false
% 55.89/7.51  --sat_fm_restart_options                ""
% 55.89/7.51  --sat_gr_def                            false
% 55.89/7.51  --sat_epr_types                         true
% 55.89/7.51  --sat_non_cyclic_types                  false
% 55.89/7.51  --sat_finite_models                     false
% 55.89/7.51  --sat_fm_lemmas                         false
% 55.89/7.51  --sat_fm_prep                           false
% 55.89/7.51  --sat_fm_uc_incr                        true
% 55.89/7.51  --sat_out_model                         small
% 55.89/7.51  --sat_out_clauses                       false
% 55.89/7.51  
% 55.89/7.51  ------ QBF Options
% 55.89/7.51  
% 55.89/7.51  --qbf_mode                              false
% 55.89/7.51  --qbf_elim_univ                         false
% 55.89/7.51  --qbf_dom_inst                          none
% 55.89/7.51  --qbf_dom_pre_inst                      false
% 55.89/7.51  --qbf_sk_in                             false
% 55.89/7.51  --qbf_pred_elim                         true
% 55.89/7.51  --qbf_split                             512
% 55.89/7.51  
% 55.89/7.51  ------ BMC1 Options
% 55.89/7.51  
% 55.89/7.51  --bmc1_incremental                      false
% 55.89/7.51  --bmc1_axioms                           reachable_all
% 55.89/7.51  --bmc1_min_bound                        0
% 55.89/7.51  --bmc1_max_bound                        -1
% 55.89/7.51  --bmc1_max_bound_default                -1
% 55.89/7.51  --bmc1_symbol_reachability              true
% 55.89/7.51  --bmc1_property_lemmas                  false
% 55.89/7.51  --bmc1_k_induction                      false
% 55.89/7.51  --bmc1_non_equiv_states                 false
% 55.89/7.51  --bmc1_deadlock                         false
% 55.89/7.51  --bmc1_ucm                              false
% 55.89/7.51  --bmc1_add_unsat_core                   none
% 55.89/7.51  --bmc1_unsat_core_children              false
% 55.89/7.51  --bmc1_unsat_core_extrapolate_axioms    false
% 55.89/7.51  --bmc1_out_stat                         full
% 55.89/7.51  --bmc1_ground_init                      false
% 55.89/7.51  --bmc1_pre_inst_next_state              false
% 55.89/7.51  --bmc1_pre_inst_state                   false
% 55.89/7.51  --bmc1_pre_inst_reach_state             false
% 55.89/7.51  --bmc1_out_unsat_core                   false
% 55.89/7.51  --bmc1_aig_witness_out                  false
% 55.89/7.51  --bmc1_verbose                          false
% 55.89/7.51  --bmc1_dump_clauses_tptp                false
% 55.89/7.51  --bmc1_dump_unsat_core_tptp             false
% 55.89/7.51  --bmc1_dump_file                        -
% 55.89/7.51  --bmc1_ucm_expand_uc_limit              128
% 55.89/7.51  --bmc1_ucm_n_expand_iterations          6
% 55.89/7.51  --bmc1_ucm_extend_mode                  1
% 55.89/7.51  --bmc1_ucm_init_mode                    2
% 55.89/7.51  --bmc1_ucm_cone_mode                    none
% 55.89/7.51  --bmc1_ucm_reduced_relation_type        0
% 55.89/7.51  --bmc1_ucm_relax_model                  4
% 55.89/7.51  --bmc1_ucm_full_tr_after_sat            true
% 55.89/7.51  --bmc1_ucm_expand_neg_assumptions       false
% 55.89/7.51  --bmc1_ucm_layered_model                none
% 55.89/7.51  --bmc1_ucm_max_lemma_size               10
% 55.89/7.51  
% 55.89/7.51  ------ AIG Options
% 55.89/7.51  
% 55.89/7.51  --aig_mode                              false
% 55.89/7.51  
% 55.89/7.51  ------ Instantiation Options
% 55.89/7.51  
% 55.89/7.51  --instantiation_flag                    true
% 55.89/7.51  --inst_sos_flag                         true
% 55.89/7.51  --inst_sos_phase                        true
% 55.89/7.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.89/7.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.89/7.51  --inst_lit_sel_side                     none
% 55.89/7.51  --inst_solver_per_active                1400
% 55.89/7.51  --inst_solver_calls_frac                1.
% 55.89/7.51  --inst_passive_queue_type               priority_queues
% 55.89/7.51  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 55.89/7.51  --inst_passive_queues_freq              [25;2]
% 55.89/7.51  --inst_dismatching                      true
% 55.89/7.51  --inst_eager_unprocessed_to_passive     true
% 55.89/7.51  --inst_prop_sim_given                   true
% 55.89/7.51  --inst_prop_sim_new                     false
% 55.89/7.51  --inst_subs_new                         false
% 55.89/7.51  --inst_eq_res_simp                      false
% 55.89/7.51  --inst_subs_given                       false
% 55.89/7.51  --inst_orphan_elimination               true
% 55.89/7.51  --inst_learning_loop_flag               true
% 55.89/7.51  --inst_learning_start                   3000
% 55.89/7.51  --inst_learning_factor                  2
% 55.89/7.51  --inst_start_prop_sim_after_learn       3
% 55.89/7.51  --inst_sel_renew                        solver
% 55.89/7.51  --inst_lit_activity_flag                true
% 55.89/7.51  --inst_restr_to_given                   false
% 55.89/7.51  --inst_activity_threshold               500
% 55.89/7.51  --inst_out_proof                        true
% 55.89/7.51  
% 55.89/7.51  ------ Resolution Options
% 55.89/7.51  
% 55.89/7.51  --resolution_flag                       false
% 55.89/7.51  --res_lit_sel                           adaptive
% 55.89/7.51  --res_lit_sel_side                      none
% 55.89/7.51  --res_ordering                          kbo
% 55.89/7.51  --res_to_prop_solver                    active
% 55.89/7.51  --res_prop_simpl_new                    false
% 55.89/7.51  --res_prop_simpl_given                  true
% 55.89/7.51  --res_passive_queue_type                priority_queues
% 55.89/7.51  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 55.89/7.51  --res_passive_queues_freq               [15;5]
% 55.89/7.51  --res_forward_subs                      full
% 55.89/7.51  --res_backward_subs                     full
% 55.89/7.51  --res_forward_subs_resolution           true
% 55.89/7.51  --res_backward_subs_resolution          true
% 55.89/7.51  --res_orphan_elimination                true
% 55.89/7.51  --res_time_limit                        2.
% 55.89/7.51  --res_out_proof                         true
% 55.89/7.51  
% 55.89/7.51  ------ Superposition Options
% 55.89/7.51  
% 55.89/7.51  --superposition_flag                    true
% 55.89/7.51  --sup_passive_queue_type                priority_queues
% 55.89/7.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.89/7.51  --sup_passive_queues_freq               [8;1;4]
% 55.89/7.51  --demod_completeness_check              fast
% 55.89/7.51  --demod_use_ground                      true
% 55.89/7.51  --sup_to_prop_solver                    passive
% 55.89/7.51  --sup_prop_simpl_new                    true
% 55.89/7.51  --sup_prop_simpl_given                  true
% 55.89/7.51  --sup_fun_splitting                     true
% 55.89/7.51  --sup_smt_interval                      50000
% 55.89/7.51  
% 55.89/7.51  ------ Superposition Simplification Setup
% 55.89/7.51  
% 55.89/7.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.89/7.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.89/7.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.89/7.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.89/7.51  --sup_full_triv                         [TrivRules;PropSubs]
% 55.89/7.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.89/7.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.89/7.51  --sup_immed_triv                        [TrivRules]
% 55.89/7.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.89/7.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.89/7.51  --sup_immed_bw_main                     []
% 55.89/7.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.89/7.51  --sup_input_triv                        [Unflattening;TrivRules]
% 55.89/7.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.89/7.51  --sup_input_bw                          []
% 55.89/7.51  
% 55.89/7.51  ------ Combination Options
% 55.89/7.51  
% 55.89/7.51  --comb_res_mult                         3
% 55.89/7.51  --comb_sup_mult                         2
% 55.89/7.51  --comb_inst_mult                        10
% 55.89/7.51  
% 55.89/7.51  ------ Debug Options
% 55.89/7.51  
% 55.89/7.51  --dbg_backtrace                         false
% 55.89/7.51  --dbg_dump_prop_clauses                 false
% 55.89/7.51  --dbg_dump_prop_clauses_file            -
% 55.89/7.51  --dbg_out_stat                          false
% 55.89/7.51  
% 55.89/7.51  
% 55.89/7.51  
% 55.89/7.51  
% 55.89/7.51  ------ Proving...
% 55.89/7.51  
% 55.89/7.51  
% 55.89/7.51  % SZS status Theorem for theBenchmark.p
% 55.89/7.51  
% 55.89/7.51   Resolution empty clause
% 55.89/7.51  
% 55.89/7.51  % SZS output start CNFRefutation for theBenchmark.p
% 55.89/7.51  
% 55.89/7.51  fof(f1,axiom,(
% 55.89/7.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 55.89/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.89/7.51  
% 55.89/7.51  fof(f17,plain,(
% 55.89/7.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 55.89/7.51    inference(cnf_transformation,[],[f1])).
% 55.89/7.51  
% 55.89/7.51  fof(f7,axiom,(
% 55.89/7.51    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 55.89/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.89/7.51  
% 55.89/7.51  fof(f24,plain,(
% 55.89/7.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 55.89/7.51    inference(cnf_transformation,[],[f7])).
% 55.89/7.51  
% 55.89/7.51  fof(f5,axiom,(
% 55.89/7.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 55.89/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.89/7.51  
% 55.89/7.51  fof(f22,plain,(
% 55.89/7.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 55.89/7.51    inference(cnf_transformation,[],[f5])).
% 55.89/7.51  
% 55.89/7.51  fof(f3,axiom,(
% 55.89/7.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 55.89/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.89/7.51  
% 55.89/7.51  fof(f14,plain,(
% 55.89/7.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 55.89/7.51    inference(nnf_transformation,[],[f3])).
% 55.89/7.51  
% 55.89/7.51  fof(f20,plain,(
% 55.89/7.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 55.89/7.51    inference(cnf_transformation,[],[f14])).
% 55.89/7.51  
% 55.89/7.51  fof(f9,axiom,(
% 55.89/7.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 55.89/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.89/7.51  
% 55.89/7.51  fof(f26,plain,(
% 55.89/7.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 55.89/7.51    inference(cnf_transformation,[],[f9])).
% 55.89/7.51  
% 55.89/7.51  fof(f31,plain,(
% 55.89/7.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 55.89/7.51    inference(definition_unfolding,[],[f20,f26])).
% 55.89/7.51  
% 55.89/7.51  fof(f11,conjecture,(
% 55.89/7.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 55.89/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.89/7.51  
% 55.89/7.51  fof(f12,negated_conjecture,(
% 55.89/7.51    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 55.89/7.51    inference(negated_conjecture,[],[f11])).
% 55.89/7.51  
% 55.89/7.51  fof(f13,plain,(
% 55.89/7.51    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 55.89/7.51    inference(ennf_transformation,[],[f12])).
% 55.89/7.51  
% 55.89/7.51  fof(f15,plain,(
% 55.89/7.51    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1))),
% 55.89/7.51    introduced(choice_axiom,[])).
% 55.89/7.51  
% 55.89/7.51  fof(f16,plain,(
% 55.89/7.51    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1)),
% 55.89/7.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 55.89/7.51  
% 55.89/7.51  fof(f29,plain,(
% 55.89/7.51    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 55.89/7.51    inference(cnf_transformation,[],[f16])).
% 55.89/7.51  
% 55.89/7.51  fof(f36,plain,(
% 55.89/7.51    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))),
% 55.89/7.51    inference(definition_unfolding,[],[f29,f26,f26])).
% 55.89/7.51  
% 55.89/7.51  fof(f2,axiom,(
% 55.89/7.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 55.89/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.89/7.51  
% 55.89/7.51  fof(f18,plain,(
% 55.89/7.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 55.89/7.51    inference(cnf_transformation,[],[f2])).
% 55.89/7.51  
% 55.89/7.51  fof(f30,plain,(
% 55.89/7.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 55.89/7.51    inference(definition_unfolding,[],[f18,f26,f26])).
% 55.89/7.51  
% 55.89/7.51  fof(f10,axiom,(
% 55.89/7.51    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 55.89/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.89/7.51  
% 55.89/7.51  fof(f27,plain,(
% 55.89/7.51    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 55.89/7.51    inference(cnf_transformation,[],[f10])).
% 55.89/7.51  
% 55.89/7.51  fof(f35,plain,(
% 55.89/7.51    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 55.89/7.51    inference(definition_unfolding,[],[f27,f26])).
% 55.89/7.51  
% 55.89/7.51  fof(f4,axiom,(
% 55.89/7.51    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 55.89/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.89/7.51  
% 55.89/7.51  fof(f21,plain,(
% 55.89/7.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 55.89/7.51    inference(cnf_transformation,[],[f4])).
% 55.89/7.51  
% 55.89/7.51  fof(f33,plain,(
% 55.89/7.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 55.89/7.51    inference(definition_unfolding,[],[f21,f26])).
% 55.89/7.51  
% 55.89/7.51  fof(f6,axiom,(
% 55.89/7.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 55.89/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.89/7.51  
% 55.89/7.51  fof(f23,plain,(
% 55.89/7.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 55.89/7.51    inference(cnf_transformation,[],[f6])).
% 55.89/7.51  
% 55.89/7.51  fof(f19,plain,(
% 55.89/7.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 55.89/7.51    inference(cnf_transformation,[],[f14])).
% 55.89/7.51  
% 55.89/7.51  fof(f32,plain,(
% 55.89/7.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 55.89/7.51    inference(definition_unfolding,[],[f19,f26])).
% 55.89/7.51  
% 55.89/7.51  fof(f28,plain,(
% 55.89/7.51    r1_xboole_0(sK0,sK1)),
% 55.89/7.51    inference(cnf_transformation,[],[f16])).
% 55.89/7.51  
% 55.89/7.51  fof(f8,axiom,(
% 55.89/7.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 55.89/7.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.89/7.51  
% 55.89/7.51  fof(f25,plain,(
% 55.89/7.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 55.89/7.51    inference(cnf_transformation,[],[f8])).
% 55.89/7.51  
% 55.89/7.51  fof(f34,plain,(
% 55.89/7.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 55.89/7.51    inference(definition_unfolding,[],[f25,f26])).
% 55.89/7.51  
% 55.89/7.51  cnf(c_0,plain,
% 55.89/7.51      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 55.89/7.51      inference(cnf_transformation,[],[f17]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_7,plain,
% 55.89/7.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.89/7.51      inference(cnf_transformation,[],[f24]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_5,plain,
% 55.89/7.51      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 55.89/7.51      inference(cnf_transformation,[],[f22]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_338,plain,
% 55.89/7.51      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_7,c_5]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_4352,plain,
% 55.89/7.51      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_0,c_338]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_2,plain,
% 55.89/7.51      ( r1_xboole_0(X0,X1)
% 55.89/7.51      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 55.89/7.51      inference(cnf_transformation,[],[f31]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_44,plain,
% 55.89/7.51      ( r1_xboole_0(X0,X1)
% 55.89/7.51      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 55.89/7.51      inference(prop_impl,[status(thm)],[c_2]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_10,negated_conjecture,
% 55.89/7.51      ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
% 55.89/7.51      inference(cnf_transformation,[],[f36]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_83,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 55.89/7.51      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) != X1
% 55.89/7.51      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) != X0 ),
% 55.89/7.51      inference(resolution_lifted,[status(thm)],[c_44,c_10]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_84,plain,
% 55.89/7.51      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))) != k1_xboole_0 ),
% 55.89/7.51      inference(unflattening,[status(thm)],[c_83]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_115,plain,
% 55.89/7.51      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))))) != k1_xboole_0 ),
% 55.89/7.51      inference(demodulation,[status(thm)],[c_84,c_7]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_145439,plain,
% 55.89/7.51      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))))) != k1_xboole_0 ),
% 55.89/7.51      inference(demodulation,[status(thm)],[c_4352,c_115]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_1,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 55.89/7.51      inference(cnf_transformation,[],[f30]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_9,plain,
% 55.89/7.51      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 55.89/7.51      inference(cnf_transformation,[],[f35]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_4,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 55.89/7.51      inference(cnf_transformation,[],[f33]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_6,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.89/7.51      inference(cnf_transformation,[],[f23]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_114,plain,
% 55.89/7.51      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 55.89/7.51      inference(light_normalisation,[status(thm)],[c_4,c_6]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_341,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_7,c_114]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_342,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 55.89/7.51      inference(demodulation,[status(thm)],[c_341,c_5]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_953,plain,
% 55.89/7.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_9,c_342]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_3,plain,
% 55.89/7.51      ( ~ r1_xboole_0(X0,X1)
% 55.89/7.51      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 55.89/7.51      inference(cnf_transformation,[],[f32]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_46,plain,
% 55.89/7.51      ( ~ r1_xboole_0(X0,X1)
% 55.89/7.51      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 55.89/7.51      inference(prop_impl,[status(thm)],[c_3]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_11,negated_conjecture,
% 55.89/7.51      ( r1_xboole_0(sK0,sK1) ),
% 55.89/7.51      inference(cnf_transformation,[],[f28]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_88,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 55.89/7.51      | sK1 != X1
% 55.89/7.51      | sK0 != X0 ),
% 55.89/7.51      inference(resolution_lifted,[status(thm)],[c_46,c_11]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_89,plain,
% 55.89/7.51      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 55.89/7.51      inference(unflattening,[status(thm)],[c_88]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_8,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 55.89/7.51      inference(cnf_transformation,[],[f34]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_402,plain,
% 55.89/7.51      ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK1) ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_89,c_8]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_422,plain,
% 55.89/7.51      ( k4_xboole_0(sK0,sK1) = sK0 ),
% 55.89/7.51      inference(demodulation,[status(thm)],[c_402,c_6]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_507,plain,
% 55.89/7.51      ( k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0) ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_422,c_7]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_700,plain,
% 55.89/7.51      ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_5,c_507]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_708,plain,
% 55.89/7.51      ( k4_xboole_0(sK0,k4_xboole_0(X0,sK1)) = k4_xboole_0(sK0,X0) ),
% 55.89/7.51      inference(demodulation,[status(thm)],[c_700,c_507]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_1355,plain,
% 55.89/7.51      ( k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_953,c_708]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_1356,plain,
% 55.89/7.51      ( k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = sK0 ),
% 55.89/7.51      inference(demodulation,[status(thm)],[c_1355,c_6]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_1438,plain,
% 55.89/7.51      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK1))) = sK0 ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_1,c_1356]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_339,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_343,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 55.89/7.51      inference(demodulation,[status(thm)],[c_339,c_7]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_5429,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 55.89/7.51      inference(demodulation,[status(thm)],[c_343,c_4352]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_5484,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0))) = k4_xboole_0(sK0,sK0) ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_1438,c_5429]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_5793,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0))) = k1_xboole_0 ),
% 55.89/7.51      inference(demodulation,[status(thm)],[c_5484,c_114]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_410,plain,
% 55.89/7.51      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_8,c_5]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_414,plain,
% 55.89/7.51      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
% 55.89/7.51      inference(light_normalisation,[status(thm)],[c_410,c_9]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_2456,plain,
% 55.89/7.51      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_1,c_414]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_6004,plain,
% 55.89/7.51      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_342,c_2456]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_6036,plain,
% 55.89/7.51      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 55.89/7.51      inference(light_normalisation,[status(thm)],[c_6004,c_6]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_11270,plain,
% 55.89/7.51      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_0,c_6036]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_409,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_8,c_7]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_415,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 55.89/7.51      inference(light_normalisation,[status(thm)],[c_409,c_7]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_15811,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) = k4_xboole_0(X0,k2_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_11270,c_415]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_6019,plain,
% 55.89/7.51      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_2456,c_0]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_334,plain,
% 55.89/7.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_7,c_7]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_344,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 55.89/7.51      inference(demodulation,[status(thm)],[c_334,c_7]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_8643,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X3))) = k4_xboole_0(X0,k2_xboole_0(X1,X3)) ),
% 55.89/7.51      inference(superposition,[status(thm)],[c_6019,c_344]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_16043,plain,
% 55.89/7.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 55.89/7.51      inference(demodulation,[status(thm)],[c_15811,c_8643]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_145440,plain,
% 55.89/7.51      ( k1_xboole_0 != k1_xboole_0 ),
% 55.89/7.51      inference(demodulation,[status(thm)],[c_145439,c_5793,c_16043]) ).
% 55.89/7.51  
% 55.89/7.51  cnf(c_145441,plain,
% 55.89/7.51      ( $false ),
% 55.89/7.51      inference(equality_resolution_simp,[status(thm)],[c_145440]) ).
% 55.89/7.51  
% 55.89/7.51  
% 55.89/7.51  % SZS output end CNFRefutation for theBenchmark.p
% 55.89/7.51  
% 55.89/7.51  ------                               Statistics
% 55.89/7.51  
% 55.89/7.51  ------ General
% 55.89/7.51  
% 55.89/7.51  abstr_ref_over_cycles:                  0
% 55.89/7.51  abstr_ref_under_cycles:                 0
% 55.89/7.51  gc_basic_clause_elim:                   0
% 55.89/7.51  forced_gc_time:                         0
% 55.89/7.51  parsing_time:                           0.009
% 55.89/7.51  unif_index_cands_time:                  0.
% 55.89/7.51  unif_index_add_time:                    0.
% 55.89/7.51  orderings_time:                         0.
% 55.89/7.51  out_proof_time:                         0.012
% 55.89/7.51  total_time:                             6.976
% 55.89/7.51  num_of_symbols:                         38
% 55.89/7.51  num_of_terms:                           349229
% 55.89/7.51  
% 55.89/7.51  ------ Preprocessing
% 55.89/7.51  
% 55.89/7.51  num_of_splits:                          0
% 55.89/7.51  num_of_split_atoms:                     0
% 55.89/7.51  num_of_reused_defs:                     0
% 55.89/7.51  num_eq_ax_congr_red:                    0
% 55.89/7.51  num_of_sem_filtered_clauses:            0
% 55.89/7.51  num_of_subtypes:                        0
% 55.89/7.51  monotx_restored_types:                  0
% 55.89/7.51  sat_num_of_epr_types:                   0
% 55.89/7.51  sat_num_of_non_cyclic_types:            0
% 55.89/7.51  sat_guarded_non_collapsed_types:        0
% 55.89/7.51  num_pure_diseq_elim:                    0
% 55.89/7.51  simp_replaced_by:                       0
% 55.89/7.51  res_preprocessed:                       38
% 55.89/7.51  prep_upred:                             0
% 55.89/7.51  prep_unflattend:                        4
% 55.89/7.51  smt_new_axioms:                         0
% 55.89/7.51  pred_elim_cands:                        0
% 55.89/7.51  pred_elim:                              1
% 55.89/7.51  pred_elim_cl:                           1
% 55.89/7.51  pred_elim_cycles:                       2
% 55.89/7.51  merged_defs:                            2
% 55.89/7.51  merged_defs_ncl:                        0
% 55.89/7.51  bin_hyper_res:                          2
% 55.89/7.51  prep_cycles:                            3
% 55.89/7.51  pred_elim_time:                         0.001
% 55.89/7.51  splitting_time:                         0.
% 55.89/7.51  sem_filter_time:                        0.
% 55.89/7.51  monotx_time:                            0.001
% 55.89/7.51  subtype_inf_time:                       0.
% 55.89/7.51  
% 55.89/7.51  ------ Problem properties
% 55.89/7.51  
% 55.89/7.51  clauses:                                11
% 55.89/7.51  conjectures:                            0
% 55.89/7.51  epr:                                    0
% 55.89/7.51  horn:                                   11
% 55.89/7.51  ground:                                 3
% 55.89/7.51  unary:                                  10
% 55.89/7.51  binary:                                 1
% 55.89/7.51  lits:                                   12
% 55.89/7.51  lits_eq:                                12
% 55.89/7.51  fd_pure:                                0
% 55.89/7.51  fd_pseudo:                              0
% 55.89/7.51  fd_cond:                                0
% 55.89/7.51  fd_pseudo_cond:                         0
% 55.89/7.51  ac_symbols:                             0
% 55.89/7.51  
% 55.89/7.51  ------ Propositional Solver
% 55.89/7.51  
% 55.89/7.51  prop_solver_calls:                      32
% 55.89/7.51  prop_fast_solver_calls:                 567
% 55.89/7.51  smt_solver_calls:                       0
% 55.89/7.51  smt_fast_solver_calls:                  0
% 55.89/7.51  prop_num_of_clauses:                    31796
% 55.89/7.51  prop_preprocess_simplified:             13075
% 55.89/7.51  prop_fo_subsumed:                       0
% 55.89/7.51  prop_solver_time:                       0.
% 55.89/7.51  smt_solver_time:                        0.
% 55.89/7.51  smt_fast_solver_time:                   0.
% 55.89/7.51  prop_fast_solver_time:                  0.
% 55.89/7.51  prop_unsat_core_time:                   0.
% 55.89/7.51  
% 55.89/7.51  ------ QBF
% 55.89/7.51  
% 55.89/7.51  qbf_q_res:                              0
% 55.89/7.51  qbf_num_tautologies:                    0
% 55.89/7.51  qbf_prep_cycles:                        0
% 55.89/7.51  
% 55.89/7.51  ------ BMC1
% 55.89/7.51  
% 55.89/7.51  bmc1_current_bound:                     -1
% 55.89/7.51  bmc1_last_solved_bound:                 -1
% 55.89/7.51  bmc1_unsat_core_size:                   -1
% 55.89/7.51  bmc1_unsat_core_parents_size:           -1
% 55.89/7.51  bmc1_merge_next_fun:                    0
% 55.89/7.51  bmc1_unsat_core_clauses_time:           0.
% 55.89/7.51  
% 55.89/7.51  ------ Instantiation
% 55.89/7.51  
% 55.89/7.51  inst_num_of_clauses:                    4006
% 55.89/7.51  inst_num_in_passive:                    1800
% 55.89/7.51  inst_num_in_active:                     1726
% 55.89/7.51  inst_num_in_unprocessed:                480
% 55.89/7.51  inst_num_of_loops:                      1950
% 55.89/7.51  inst_num_of_learning_restarts:          0
% 55.89/7.51  inst_num_moves_active_passive:          220
% 55.89/7.51  inst_lit_activity:                      0
% 55.89/7.51  inst_lit_activity_moves:                0
% 55.89/7.51  inst_num_tautologies:                   0
% 55.89/7.51  inst_num_prop_implied:                  0
% 55.89/7.51  inst_num_existing_simplified:           0
% 55.89/7.51  inst_num_eq_res_simplified:             0
% 55.89/7.51  inst_num_child_elim:                    0
% 55.89/7.51  inst_num_of_dismatching_blockings:      2847
% 55.89/7.51  inst_num_of_non_proper_insts:           6592
% 55.89/7.51  inst_num_of_duplicates:                 0
% 55.89/7.51  inst_inst_num_from_inst_to_res:         0
% 55.89/7.51  inst_dismatching_checking_time:         0.
% 55.89/7.51  
% 55.89/7.51  ------ Resolution
% 55.89/7.51  
% 55.89/7.51  res_num_of_clauses:                     0
% 55.89/7.51  res_num_in_passive:                     0
% 55.89/7.51  res_num_in_active:                      0
% 55.89/7.51  res_num_of_loops:                       41
% 55.89/7.51  res_forward_subset_subsumed:            1689
% 55.89/7.51  res_backward_subset_subsumed:           0
% 55.89/7.51  res_forward_subsumed:                   0
% 55.89/7.51  res_backward_subsumed:                  0
% 55.89/7.51  res_forward_subsumption_resolution:     0
% 55.89/7.51  res_backward_subsumption_resolution:    0
% 55.89/7.51  res_clause_to_clause_subsumption:       254508
% 55.89/7.51  res_orphan_elimination:                 0
% 55.89/7.51  res_tautology_del:                      313
% 55.89/7.51  res_num_eq_res_simplified:              0
% 55.89/7.51  res_num_sel_changes:                    0
% 55.89/7.51  res_moves_from_active_to_pass:          0
% 55.89/7.51  
% 55.89/7.51  ------ Superposition
% 55.89/7.51  
% 55.89/7.51  sup_time_total:                         0.
% 55.89/7.51  sup_time_generating:                    0.
% 55.89/7.51  sup_time_sim_full:                      0.
% 55.89/7.51  sup_time_sim_immed:                     0.
% 55.89/7.51  
% 55.89/7.51  sup_num_of_clauses:                     13626
% 55.89/7.51  sup_num_in_active:                      289
% 55.89/7.51  sup_num_in_passive:                     13337
% 55.89/7.51  sup_num_of_loops:                       389
% 55.89/7.51  sup_fw_superposition:                   37327
% 55.89/7.51  sup_bw_superposition:                   26041
% 55.89/7.51  sup_immediate_simplified:               42777
% 55.89/7.51  sup_given_eliminated:                   29
% 55.89/7.51  comparisons_done:                       0
% 55.89/7.51  comparisons_avoided:                    0
% 55.89/7.51  
% 55.89/7.51  ------ Simplifications
% 55.89/7.51  
% 55.89/7.51  
% 55.89/7.51  sim_fw_subset_subsumed:                 0
% 55.89/7.51  sim_bw_subset_subsumed:                 0
% 55.89/7.51  sim_fw_subsumed:                        4793
% 55.89/7.51  sim_bw_subsumed:                        650
% 55.89/7.51  sim_fw_subsumption_res:                 0
% 55.89/7.51  sim_bw_subsumption_res:                 0
% 55.89/7.51  sim_tautology_del:                      0
% 55.89/7.51  sim_eq_tautology_del:                   18653
% 55.89/7.51  sim_eq_res_simp:                        0
% 55.89/7.51  sim_fw_demodulated:                     41013
% 55.89/7.51  sim_bw_demodulated:                     480
% 55.89/7.51  sim_light_normalised:                   11774
% 55.89/7.51  sim_joinable_taut:                      0
% 55.89/7.51  sim_joinable_simp:                      0
% 55.89/7.51  sim_ac_normalised:                      0
% 55.89/7.51  sim_smt_subsumption:                    0
% 55.89/7.51  
%------------------------------------------------------------------------------
