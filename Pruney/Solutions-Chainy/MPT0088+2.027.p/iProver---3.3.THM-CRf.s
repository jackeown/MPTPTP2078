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
% DateTime   : Thu Dec  3 11:24:36 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :   87 (1055 expanded)
%              Number of clauses        :   60 ( 397 expanded)
%              Number of leaves         :   10 ( 275 expanded)
%              Depth                    :   25
%              Number of atoms          :  105 (1267 expanded)
%              Number of equality atoms :   78 ( 997 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f17,f21])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f15,f21])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f24,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_130,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2,c_4])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_48,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_97,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | k4_xboole_0(sK1,sK2) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_48,c_9])).

cnf(c_98,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_97])).

cnf(c_6,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_405,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_98,c_6])).

cnf(c_406,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_4,c_6])).

cnf(c_425,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_406,c_130])).

cnf(c_426,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_425,c_4])).

cnf(c_428,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_405,c_426])).

cnf(c_1064,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_130,c_428])).

cnf(c_1089,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_1064,c_4])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_365,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_5])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_373,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_130])).

cnf(c_375,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_373,c_3])).

cnf(c_559,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_375])).

cnf(c_2276,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_428,c_559])).

cnf(c_3458,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(sK1,sK2)),sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_365,c_2276])).

cnf(c_566,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_375,c_5])).

cnf(c_8701,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),k2_xboole_0(X1,k4_xboole_0(sK0,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_428,c_566])).

cnf(c_9433,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),k2_xboole_0(X0,sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_8701])).

cnf(c_371,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_3])).

cnf(c_14860,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK0),k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(k2_xboole_0(X0,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9433,c_371])).

cnf(c_14904,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK0),k4_xboole_0(sK0,X0)) = k2_xboole_0(k2_xboole_0(X0,sK0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_14860,c_428])).

cnf(c_409,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_130,c_6])).

cnf(c_415,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_409,c_4])).

cnf(c_410,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_3])).

cnf(c_412,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_410,c_4,c_130])).

cnf(c_5814,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_415,c_412])).

cnf(c_5820,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_5814])).

cnf(c_15312,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,sK0),k1_xboole_0))) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_14904,c_5820])).

cnf(c_369,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_5,c_5])).

cnf(c_383,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_369,c_5])).

cnf(c_15343,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK0,k1_xboole_0))))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_15312,c_5,c_383])).

cnf(c_297,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_98,c_3])).

cnf(c_823,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0) = sK0 ),
    inference(demodulation,[status(thm)],[c_297,c_412])).

cnf(c_1433,plain,
    ( k2_xboole_0(sK0,k1_xboole_0) = sK0 ),
    inference(demodulation,[status(thm)],[c_1089,c_823])).

cnf(c_15344,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,sK0)))) = k4_xboole_0(sK0,X0) ),
    inference(light_normalisation,[status(thm)],[c_15343,c_1433])).

cnf(c_24359,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(sK1,sK2)),k1_xboole_0)) = k4_xboole_0(sK0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_3458,c_15344])).

cnf(c_1067,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),X1)) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_428,c_5])).

cnf(c_1082,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),X1)) = k4_xboole_0(sK0,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1067,c_5])).

cnf(c_24361,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_24359,c_365,c_383,c_428,c_1082])).

cnf(c_24689,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(sK0,X0)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_24361,c_5820])).

cnf(c_25414,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),sK0) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1089,c_24689])).

cnf(c_25637,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) = k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_25414,c_5,c_426])).

cnf(c_27197,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_25637,c_15344])).

cnf(c_27199,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) = k4_xboole_0(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_27197,c_3])).

cnf(c_27264,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_27199,c_5820])).

cnf(c_7,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_8,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_102,plain,
    ( k4_xboole_0(X0,X1) != sK1
    | k4_xboole_0(sK0,sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_8])).

cnf(c_103,plain,
    ( k4_xboole_0(X0,k4_xboole_0(sK0,sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_102])).

cnf(c_10782,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != sK1 ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27264,c_10782])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.97/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/1.50  
% 7.97/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.97/1.50  
% 7.97/1.50  ------  iProver source info
% 7.97/1.50  
% 7.97/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.97/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.97/1.50  git: non_committed_changes: false
% 7.97/1.50  git: last_make_outside_of_git: false
% 7.97/1.50  
% 7.97/1.50  ------ 
% 7.97/1.50  ------ Parsing...
% 7.97/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.97/1.50  
% 7.97/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 7.97/1.50  
% 7.97/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.97/1.50  
% 7.97/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.97/1.50  ------ Proving...
% 7.97/1.50  ------ Problem Properties 
% 7.97/1.50  
% 7.97/1.50  
% 7.97/1.50  clauses                                 10
% 7.97/1.50  conjectures                             0
% 7.97/1.50  EPR                                     0
% 7.97/1.50  Horn                                    10
% 7.97/1.50  unary                                   9
% 7.97/1.50  binary                                  1
% 7.97/1.50  lits                                    11
% 7.97/1.50  lits eq                                 11
% 7.97/1.50  fd_pure                                 0
% 7.97/1.50  fd_pseudo                               0
% 7.97/1.50  fd_cond                                 0
% 7.97/1.50  fd_pseudo_cond                          0
% 7.97/1.50  AC symbols                              0
% 7.97/1.50  
% 7.97/1.50  ------ Input Options Time Limit: Unbounded
% 7.97/1.50  
% 7.97/1.50  
% 7.97/1.50  ------ 
% 7.97/1.50  Current options:
% 7.97/1.50  ------ 
% 7.97/1.50  
% 7.97/1.50  
% 7.97/1.50  
% 7.97/1.50  
% 7.97/1.50  ------ Proving...
% 7.97/1.50  
% 7.97/1.50  
% 7.97/1.50  % SZS status Theorem for theBenchmark.p
% 7.97/1.50  
% 7.97/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.97/1.50  
% 7.97/1.50  fof(f2,axiom,(
% 7.97/1.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.97/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.50  
% 7.97/1.50  fof(f17,plain,(
% 7.97/1.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.97/1.50    inference(cnf_transformation,[],[f2])).
% 7.97/1.50  
% 7.97/1.50  fof(f6,axiom,(
% 7.97/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.97/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.50  
% 7.97/1.50  fof(f21,plain,(
% 7.97/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.97/1.50    inference(cnf_transformation,[],[f6])).
% 7.97/1.50  
% 7.97/1.50  fof(f28,plain,(
% 7.97/1.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.97/1.50    inference(definition_unfolding,[],[f17,f21])).
% 7.97/1.50  
% 7.97/1.50  fof(f4,axiom,(
% 7.97/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.97/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.50  
% 7.97/1.50  fof(f19,plain,(
% 7.97/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.97/1.50    inference(cnf_transformation,[],[f4])).
% 7.97/1.50  
% 7.97/1.50  fof(f1,axiom,(
% 7.97/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.97/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.50  
% 7.97/1.50  fof(f12,plain,(
% 7.97/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.97/1.50    inference(nnf_transformation,[],[f1])).
% 7.97/1.50  
% 7.97/1.50  fof(f15,plain,(
% 7.97/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.97/1.50    inference(cnf_transformation,[],[f12])).
% 7.97/1.50  
% 7.97/1.50  fof(f27,plain,(
% 7.97/1.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.97/1.50    inference(definition_unfolding,[],[f15,f21])).
% 7.97/1.50  
% 7.97/1.50  fof(f9,conjecture,(
% 7.97/1.50    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 7.97/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.50  
% 7.97/1.50  fof(f10,negated_conjecture,(
% 7.97/1.50    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 7.97/1.50    inference(negated_conjecture,[],[f9])).
% 7.97/1.50  
% 7.97/1.50  fof(f11,plain,(
% 7.97/1.50    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 7.97/1.50    inference(ennf_transformation,[],[f10])).
% 7.97/1.50  
% 7.97/1.50  fof(f13,plain,(
% 7.97/1.50    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 7.97/1.50    introduced(choice_axiom,[])).
% 7.97/1.50  
% 7.97/1.50  fof(f14,plain,(
% 7.97/1.50    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 7.97/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 7.97/1.50  
% 7.97/1.50  fof(f24,plain,(
% 7.97/1.50    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 7.97/1.50    inference(cnf_transformation,[],[f14])).
% 7.97/1.50  
% 7.97/1.50  fof(f7,axiom,(
% 7.97/1.50    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 7.97/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.50  
% 7.97/1.50  fof(f22,plain,(
% 7.97/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 7.97/1.50    inference(cnf_transformation,[],[f7])).
% 7.97/1.50  
% 7.97/1.50  fof(f29,plain,(
% 7.97/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 7.97/1.50    inference(definition_unfolding,[],[f22,f21])).
% 7.97/1.50  
% 7.97/1.50  fof(f5,axiom,(
% 7.97/1.50    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.97/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.50  
% 7.97/1.50  fof(f20,plain,(
% 7.97/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.97/1.50    inference(cnf_transformation,[],[f5])).
% 7.97/1.50  
% 7.97/1.50  fof(f3,axiom,(
% 7.97/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.97/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.50  
% 7.97/1.50  fof(f18,plain,(
% 7.97/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.97/1.50    inference(cnf_transformation,[],[f3])).
% 7.97/1.50  
% 7.97/1.50  fof(f8,axiom,(
% 7.97/1.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.97/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.50  
% 7.97/1.50  fof(f23,plain,(
% 7.97/1.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.97/1.50    inference(cnf_transformation,[],[f8])).
% 7.97/1.50  
% 7.97/1.50  fof(f25,plain,(
% 7.97/1.50    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 7.97/1.50    inference(cnf_transformation,[],[f14])).
% 7.97/1.50  
% 7.97/1.50  cnf(c_2,plain,
% 7.97/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.97/1.50      inference(cnf_transformation,[],[f28]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_4,plain,
% 7.97/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.97/1.50      inference(cnf_transformation,[],[f19]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_130,plain,
% 7.97/1.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.97/1.50      inference(light_normalisation,[status(thm)],[c_2,c_4]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_1,plain,
% 7.97/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.97/1.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.97/1.50      inference(cnf_transformation,[],[f27]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_48,plain,
% 7.97/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.97/1.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.97/1.50      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_9,negated_conjecture,
% 7.97/1.50      ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 7.97/1.50      inference(cnf_transformation,[],[f24]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_97,plain,
% 7.97/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.97/1.50      | k4_xboole_0(sK1,sK2) != X1
% 7.97/1.50      | sK0 != X0 ),
% 7.97/1.50      inference(resolution_lifted,[status(thm)],[c_48,c_9]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_98,plain,
% 7.97/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 7.97/1.50      inference(unflattening,[status(thm)],[c_97]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_6,plain,
% 7.97/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.97/1.50      inference(cnf_transformation,[],[f29]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_405,plain,
% 7.97/1.50      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_98,c_6]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_406,plain,
% 7.97/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_4,c_6]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_425,plain,
% 7.97/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ),
% 7.97/1.50      inference(light_normalisation,[status(thm)],[c_406,c_130]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_426,plain,
% 7.97/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) = k4_xboole_0(X0,X1) ),
% 7.97/1.50      inference(demodulation,[status(thm)],[c_425,c_4]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_428,plain,
% 7.97/1.50      ( k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X0) ),
% 7.97/1.50      inference(demodulation,[status(thm)],[c_405,c_426]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_1064,plain,
% 7.97/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_130,c_428]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_1089,plain,
% 7.97/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = sK0 ),
% 7.97/1.50      inference(demodulation,[status(thm)],[c_1064,c_4]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_5,plain,
% 7.97/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.97/1.50      inference(cnf_transformation,[],[f20]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_365,plain,
% 7.97/1.50      ( k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(X0,X1) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_4,c_5]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_3,plain,
% 7.97/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.97/1.50      inference(cnf_transformation,[],[f18]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_373,plain,
% 7.97/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_5,c_130]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_375,plain,
% 7.97/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.97/1.50      inference(demodulation,[status(thm)],[c_373,c_3]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_559,plain,
% 7.97/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_3,c_375]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_2276,plain,
% 7.97/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),sK0)) = k1_xboole_0 ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_428,c_559]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_3458,plain,
% 7.97/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(sK1,sK2)),sK0)) = k1_xboole_0 ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_365,c_2276]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_566,plain,
% 7.97/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_375,c_5]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_8701,plain,
% 7.97/1.50      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),k2_xboole_0(X1,k4_xboole_0(sK0,X0)))) = k1_xboole_0 ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_428,c_566]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_9433,plain,
% 7.97/1.50      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),k2_xboole_0(X0,sK0))) = k1_xboole_0 ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_3,c_8701]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_371,plain,
% 7.97/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_5,c_3]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_14860,plain,
% 7.97/1.50      ( k2_xboole_0(k2_xboole_0(X0,sK0),k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) = k2_xboole_0(k2_xboole_0(X0,sK0),k1_xboole_0) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_9433,c_371]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_14904,plain,
% 7.97/1.50      ( k2_xboole_0(k2_xboole_0(X0,sK0),k4_xboole_0(sK0,X0)) = k2_xboole_0(k2_xboole_0(X0,sK0),k1_xboole_0) ),
% 7.97/1.50      inference(light_normalisation,[status(thm)],[c_14860,c_428]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_409,plain,
% 7.97/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_130,c_6]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_415,plain,
% 7.97/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.97/1.50      inference(light_normalisation,[status(thm)],[c_409,c_4]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_410,plain,
% 7.97/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X1)) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_6,c_3]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_412,plain,
% 7.97/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 7.97/1.50      inference(demodulation,[status(thm)],[c_410,c_4,c_130]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_5814,plain,
% 7.97/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.97/1.50      inference(light_normalisation,[status(thm)],[c_415,c_412]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_5820,plain,
% 7.97/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = X0 ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_5,c_5814]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_15312,plain,
% 7.97/1.50      ( k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X0,sK0),k1_xboole_0))) = k4_xboole_0(sK0,X0) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_14904,c_5820]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_369,plain,
% 7.97/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_5,c_5]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_383,plain,
% 7.97/1.50      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 7.97/1.50      inference(demodulation,[status(thm)],[c_369,c_5]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_15343,plain,
% 7.97/1.50      ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,k2_xboole_0(sK0,k1_xboole_0))))) = k4_xboole_0(sK0,X0) ),
% 7.97/1.50      inference(demodulation,[status(thm)],[c_15312,c_5,c_383]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_297,plain,
% 7.97/1.50      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_98,c_3]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_823,plain,
% 7.97/1.50      ( k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0) = sK0 ),
% 7.97/1.50      inference(demodulation,[status(thm)],[c_297,c_412]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_1433,plain,
% 7.97/1.50      ( k2_xboole_0(sK0,k1_xboole_0) = sK0 ),
% 7.97/1.50      inference(demodulation,[status(thm)],[c_1089,c_823]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_15344,plain,
% 7.97/1.50      ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,sK0)))) = k4_xboole_0(sK0,X0) ),
% 7.97/1.50      inference(light_normalisation,[status(thm)],[c_15343,c_1433]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_24359,plain,
% 7.97/1.50      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(sK1,sK2)),k1_xboole_0)) = k4_xboole_0(sK0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k4_xboole_0(sK1,sK2))) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_3458,c_15344]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_1067,plain,
% 7.97/1.50      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),X1)) = k4_xboole_0(k4_xboole_0(sK0,X0),X1) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_428,c_5]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_1082,plain,
% 7.97/1.50      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK1,sK2)),X1)) = k4_xboole_0(sK0,k2_xboole_0(X0,X1)) ),
% 7.97/1.50      inference(demodulation,[status(thm)],[c_1067,c_5]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_24361,plain,
% 7.97/1.50      ( k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0))) = k4_xboole_0(sK0,X0) ),
% 7.97/1.50      inference(demodulation,
% 7.97/1.50                [status(thm)],
% 7.97/1.50                [c_24359,c_365,c_383,c_428,c_1082]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_24689,plain,
% 7.97/1.50      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(sK0,X0)) = k2_xboole_0(X0,k1_xboole_0) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_24361,c_5820]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_25414,plain,
% 7.97/1.50      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0),sK0) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_1089,c_24689]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_25637,plain,
% 7.97/1.50      ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)) = k4_xboole_0(sK1,sK2) ),
% 7.97/1.50      inference(demodulation,[status(thm)],[c_25414,c_5,c_426]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_27197,plain,
% 7.97/1.50      ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,sK2) ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_25637,c_15344]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_27199,plain,
% 7.97/1.50      ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) = k4_xboole_0(sK0,sK2) ),
% 7.97/1.50      inference(demodulation,[status(thm)],[c_27197,c_3]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_27264,plain,
% 7.97/1.50      ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = sK1 ),
% 7.97/1.50      inference(superposition,[status(thm)],[c_27199,c_5820]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_7,plain,
% 7.97/1.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 7.97/1.50      inference(cnf_transformation,[],[f23]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_8,negated_conjecture,
% 7.97/1.50      ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
% 7.97/1.50      inference(cnf_transformation,[],[f25]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_102,plain,
% 7.97/1.50      ( k4_xboole_0(X0,X1) != sK1 | k4_xboole_0(sK0,sK2) != X1 ),
% 7.97/1.50      inference(resolution_lifted,[status(thm)],[c_7,c_8]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_103,plain,
% 7.97/1.50      ( k4_xboole_0(X0,k4_xboole_0(sK0,sK2)) != sK1 ),
% 7.97/1.50      inference(unflattening,[status(thm)],[c_102]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(c_10782,plain,
% 7.97/1.50      ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != sK1 ),
% 7.97/1.50      inference(instantiation,[status(thm)],[c_103]) ).
% 7.97/1.50  
% 7.97/1.50  cnf(contradiction,plain,
% 7.97/1.50      ( $false ),
% 7.97/1.50      inference(minisat,[status(thm)],[c_27264,c_10782]) ).
% 7.97/1.50  
% 7.97/1.50  
% 7.97/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.97/1.50  
% 7.97/1.50  ------                               Statistics
% 7.97/1.50  
% 7.97/1.50  ------ Selected
% 7.97/1.50  
% 7.97/1.50  total_time:                             0.912
% 7.97/1.50  
%------------------------------------------------------------------------------
