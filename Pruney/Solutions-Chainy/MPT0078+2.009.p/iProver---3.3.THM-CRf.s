%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:41 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  121 (1473 expanded)
%              Number of clauses        :   79 ( 578 expanded)
%              Number of leaves         :   17 ( 370 expanded)
%              Depth                    :   27
%              Number of atoms          :  176 (2522 expanded)
%              Number of equality atoms :  122 (1800 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f21])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f19])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f17])).

fof(f23,plain,
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

fof(f24,plain,
    ( sK2 != sK4
    & r1_xboole_0(sK4,sK3)
    & r1_xboole_0(sK2,sK3)
    & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f23])).

fof(f38,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f37,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f36,f36])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f40,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_234,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_100,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_101,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(unflattening,[status(thm)],[c_100])).

cnf(c_231,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101])).

cnf(c_8044,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_234,c_231])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_8219,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8044,c_7])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_8248,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),sK2) = k4_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_8219,c_5])).

cnf(c_14,negated_conjecture,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_9,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_536,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK3),sK3) = k4_xboole_0(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_14,c_9])).

cnf(c_548,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK4,sK3) ),
    inference(demodulation,[status(thm)],[c_536,c_9])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_91,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK3 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_12])).

cnf(c_92,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) ),
    inference(unflattening,[status(thm)],[c_91])).

cnf(c_232,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_92])).

cnf(c_659,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_548,c_232])).

cnf(c_8045,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_234,c_659])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_562,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_3524,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = k2_xboole_0(k4_xboole_0(sK3,sK4),sK3) ),
    inference(superposition,[status(thm)],[c_548,c_562])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_664,plain,
    ( k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) = k2_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_548,c_7])).

cnf(c_666,plain,
    ( k2_xboole_0(sK3,sK4) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_664,c_7])).

cnf(c_700,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) = k4_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_666,c_9])).

cnf(c_841,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK3),sK4) = k4_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_0,c_700])).

cnf(c_561,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_10,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_243,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6,c_8])).

cnf(c_625,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10,c_243])).

cnf(c_627,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_625,c_7])).

cnf(c_2346,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_561,c_8,c_627])).

cnf(c_2380,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,sK3),sK4),k4_xboole_0(sK3,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_841,c_2346])).

cnf(c_846,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,k4_xboole_0(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_700,c_7])).

cnf(c_848,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_846,c_7,c_14])).

cnf(c_920,plain,
    ( k2_xboole_0(sK4,k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_0,c_848])).

cnf(c_538,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_7])).

cnf(c_543,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_538,c_7])).

cnf(c_1185,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3)) = k2_xboole_0(k2_xboole_0(sK2,sK3),sK4) ),
    inference(superposition,[status(thm)],[c_920,c_543])).

cnf(c_506,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_243,c_7])).

cnf(c_511,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_506,c_5])).

cnf(c_1206,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK4) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_1185,c_511])).

cnf(c_535,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_9])).

cnf(c_1575,plain,
    ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),sK4)) ),
    inference(superposition,[status(thm)],[c_700,c_535])).

cnf(c_1606,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK4,k4_xboole_0(sK3,sK4)) ),
    inference(light_normalisation,[status(thm)],[c_1575,c_700,c_848])).

cnf(c_2432,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK3,sK4)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_2380,c_1206,c_1606])).

cnf(c_3190,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK3,sK4),X0)) = k4_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_2432,c_10])).

cnf(c_6603,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK3,sK4),sK3)) ),
    inference(superposition,[status(thm)],[c_3524,c_3190])).

cnf(c_6632,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = k4_xboole_0(sK4,sK3) ),
    inference(demodulation,[status(thm)],[c_6603,c_3190])).

cnf(c_6634,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = k4_xboole_0(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_6632,c_548])).

cnf(c_8374,plain,
    ( k4_xboole_0(sK4,k1_xboole_0) = k4_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_8045,c_6634])).

cnf(c_8381,plain,
    ( k4_xboole_0(sK2,sK3) = sK4 ),
    inference(demodulation,[status(thm)],[c_8374,c_8])).

cnf(c_12087,plain,
    ( k2_xboole_0(sK4,sK2) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_8248,c_8381])).

cnf(c_12105,plain,
    ( k2_xboole_0(sK2,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_12087,c_0])).

cnf(c_922,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_848,c_9])).

cnf(c_663,plain,
    ( k4_xboole_0(sK4,k2_xboole_0(sK3,X0)) = k4_xboole_0(k4_xboole_0(sK2,sK3),X0) ),
    inference(superposition,[status(thm)],[c_548,c_10])).

cnf(c_669,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK4,k2_xboole_0(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_663,c_10])).

cnf(c_924,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK2)) ),
    inference(demodulation,[status(thm)],[c_922,c_669])).

cnf(c_932,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_0,c_924])).

cnf(c_943,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_932,c_243])).

cnf(c_944,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_943,c_924])).

cnf(c_622,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_10,c_7])).

cnf(c_9165,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK2,sK3),sK3)) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_944,c_622])).

cnf(c_9384,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_9165,c_5,c_9])).

cnf(c_9857,plain,
    ( k2_xboole_0(sK2,sK4) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_9384,c_8381])).

cnf(c_12117,plain,
    ( sK4 = sK2 ),
    inference(light_normalisation,[status(thm)],[c_12105,c_9857])).

cnf(c_150,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_279,plain,
    ( sK4 != X0
    | sK2 != X0
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_1416,plain,
    ( sK4 != sK2
    | sK2 = sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_149,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_964,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_11,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12117,c_1416,c_964,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.48/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.48/0.99  
% 3.48/0.99  ------  iProver source info
% 3.48/0.99  
% 3.48/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.48/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.48/0.99  git: non_committed_changes: false
% 3.48/0.99  git: last_make_outside_of_git: false
% 3.48/0.99  
% 3.48/0.99  ------ 
% 3.48/0.99  
% 3.48/0.99  ------ Input Options
% 3.48/0.99  
% 3.48/0.99  --out_options                           all
% 3.48/0.99  --tptp_safe_out                         true
% 3.48/0.99  --problem_path                          ""
% 3.48/0.99  --include_path                          ""
% 3.48/0.99  --clausifier                            res/vclausify_rel
% 3.48/0.99  --clausifier_options                    --mode clausify
% 3.48/0.99  --stdin                                 false
% 3.48/0.99  --stats_out                             all
% 3.48/0.99  
% 3.48/0.99  ------ General Options
% 3.48/0.99  
% 3.48/0.99  --fof                                   false
% 3.48/0.99  --time_out_real                         305.
% 3.48/0.99  --time_out_virtual                      -1.
% 3.48/0.99  --symbol_type_check                     false
% 3.48/0.99  --clausify_out                          false
% 3.48/0.99  --sig_cnt_out                           false
% 3.48/0.99  --trig_cnt_out                          false
% 3.48/0.99  --trig_cnt_out_tolerance                1.
% 3.48/0.99  --trig_cnt_out_sk_spl                   false
% 3.48/0.99  --abstr_cl_out                          false
% 3.48/0.99  
% 3.48/0.99  ------ Global Options
% 3.48/0.99  
% 3.48/0.99  --schedule                              default
% 3.48/0.99  --add_important_lit                     false
% 3.48/0.99  --prop_solver_per_cl                    1000
% 3.48/0.99  --min_unsat_core                        false
% 3.48/0.99  --soft_assumptions                      false
% 3.48/0.99  --soft_lemma_size                       3
% 3.48/0.99  --prop_impl_unit_size                   0
% 3.48/0.99  --prop_impl_unit                        []
% 3.48/0.99  --share_sel_clauses                     true
% 3.48/0.99  --reset_solvers                         false
% 3.48/0.99  --bc_imp_inh                            [conj_cone]
% 3.48/0.99  --conj_cone_tolerance                   3.
% 3.48/0.99  --extra_neg_conj                        none
% 3.48/0.99  --large_theory_mode                     true
% 3.48/0.99  --prolific_symb_bound                   200
% 3.48/0.99  --lt_threshold                          2000
% 3.48/0.99  --clause_weak_htbl                      true
% 3.48/0.99  --gc_record_bc_elim                     false
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing Options
% 3.48/0.99  
% 3.48/0.99  --preprocessing_flag                    true
% 3.48/0.99  --time_out_prep_mult                    0.1
% 3.48/0.99  --splitting_mode                        input
% 3.48/0.99  --splitting_grd                         true
% 3.48/0.99  --splitting_cvd                         false
% 3.48/0.99  --splitting_cvd_svl                     false
% 3.48/0.99  --splitting_nvd                         32
% 3.48/0.99  --sub_typing                            true
% 3.48/0.99  --prep_gs_sim                           true
% 3.48/0.99  --prep_unflatten                        true
% 3.48/0.99  --prep_res_sim                          true
% 3.48/0.99  --prep_upred                            true
% 3.48/0.99  --prep_sem_filter                       exhaustive
% 3.48/0.99  --prep_sem_filter_out                   false
% 3.48/0.99  --pred_elim                             true
% 3.48/0.99  --res_sim_input                         true
% 3.48/0.99  --eq_ax_congr_red                       true
% 3.48/0.99  --pure_diseq_elim                       true
% 3.48/0.99  --brand_transform                       false
% 3.48/0.99  --non_eq_to_eq                          false
% 3.48/0.99  --prep_def_merge                        true
% 3.48/0.99  --prep_def_merge_prop_impl              false
% 3.48/0.99  --prep_def_merge_mbd                    true
% 3.48/0.99  --prep_def_merge_tr_red                 false
% 3.48/0.99  --prep_def_merge_tr_cl                  false
% 3.48/0.99  --smt_preprocessing                     true
% 3.48/0.99  --smt_ac_axioms                         fast
% 3.48/0.99  --preprocessed_out                      false
% 3.48/0.99  --preprocessed_stats                    false
% 3.48/0.99  
% 3.48/0.99  ------ Abstraction refinement Options
% 3.48/0.99  
% 3.48/0.99  --abstr_ref                             []
% 3.48/0.99  --abstr_ref_prep                        false
% 3.48/0.99  --abstr_ref_until_sat                   false
% 3.48/0.99  --abstr_ref_sig_restrict                funpre
% 3.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/0.99  --abstr_ref_under                       []
% 3.48/0.99  
% 3.48/0.99  ------ SAT Options
% 3.48/0.99  
% 3.48/0.99  --sat_mode                              false
% 3.48/0.99  --sat_fm_restart_options                ""
% 3.48/0.99  --sat_gr_def                            false
% 3.48/0.99  --sat_epr_types                         true
% 3.48/0.99  --sat_non_cyclic_types                  false
% 3.48/0.99  --sat_finite_models                     false
% 3.48/0.99  --sat_fm_lemmas                         false
% 3.48/0.99  --sat_fm_prep                           false
% 3.48/0.99  --sat_fm_uc_incr                        true
% 3.48/0.99  --sat_out_model                         small
% 3.48/0.99  --sat_out_clauses                       false
% 3.48/0.99  
% 3.48/0.99  ------ QBF Options
% 3.48/0.99  
% 3.48/0.99  --qbf_mode                              false
% 3.48/0.99  --qbf_elim_univ                         false
% 3.48/0.99  --qbf_dom_inst                          none
% 3.48/0.99  --qbf_dom_pre_inst                      false
% 3.48/0.99  --qbf_sk_in                             false
% 3.48/0.99  --qbf_pred_elim                         true
% 3.48/0.99  --qbf_split                             512
% 3.48/0.99  
% 3.48/0.99  ------ BMC1 Options
% 3.48/0.99  
% 3.48/0.99  --bmc1_incremental                      false
% 3.48/0.99  --bmc1_axioms                           reachable_all
% 3.48/0.99  --bmc1_min_bound                        0
% 3.48/0.99  --bmc1_max_bound                        -1
% 3.48/0.99  --bmc1_max_bound_default                -1
% 3.48/0.99  --bmc1_symbol_reachability              true
% 3.48/0.99  --bmc1_property_lemmas                  false
% 3.48/0.99  --bmc1_k_induction                      false
% 3.48/0.99  --bmc1_non_equiv_states                 false
% 3.48/0.99  --bmc1_deadlock                         false
% 3.48/0.99  --bmc1_ucm                              false
% 3.48/0.99  --bmc1_add_unsat_core                   none
% 3.48/0.99  --bmc1_unsat_core_children              false
% 3.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/0.99  --bmc1_out_stat                         full
% 3.48/0.99  --bmc1_ground_init                      false
% 3.48/0.99  --bmc1_pre_inst_next_state              false
% 3.48/0.99  --bmc1_pre_inst_state                   false
% 3.48/0.99  --bmc1_pre_inst_reach_state             false
% 3.48/0.99  --bmc1_out_unsat_core                   false
% 3.48/0.99  --bmc1_aig_witness_out                  false
% 3.48/0.99  --bmc1_verbose                          false
% 3.48/0.99  --bmc1_dump_clauses_tptp                false
% 3.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.48/0.99  --bmc1_dump_file                        -
% 3.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.48/0.99  --bmc1_ucm_extend_mode                  1
% 3.48/0.99  --bmc1_ucm_init_mode                    2
% 3.48/0.99  --bmc1_ucm_cone_mode                    none
% 3.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.48/0.99  --bmc1_ucm_relax_model                  4
% 3.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/0.99  --bmc1_ucm_layered_model                none
% 3.48/0.99  --bmc1_ucm_max_lemma_size               10
% 3.48/0.99  
% 3.48/0.99  ------ AIG Options
% 3.48/0.99  
% 3.48/0.99  --aig_mode                              false
% 3.48/0.99  
% 3.48/0.99  ------ Instantiation Options
% 3.48/0.99  
% 3.48/0.99  --instantiation_flag                    true
% 3.48/0.99  --inst_sos_flag                         false
% 3.48/0.99  --inst_sos_phase                        true
% 3.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel_side                     num_symb
% 3.48/0.99  --inst_solver_per_active                1400
% 3.48/0.99  --inst_solver_calls_frac                1.
% 3.48/0.99  --inst_passive_queue_type               priority_queues
% 3.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/0.99  --inst_passive_queues_freq              [25;2]
% 3.48/0.99  --inst_dismatching                      true
% 3.48/0.99  --inst_eager_unprocessed_to_passive     true
% 3.48/0.99  --inst_prop_sim_given                   true
% 3.48/0.99  --inst_prop_sim_new                     false
% 3.48/0.99  --inst_subs_new                         false
% 3.48/0.99  --inst_eq_res_simp                      false
% 3.48/0.99  --inst_subs_given                       false
% 3.48/0.99  --inst_orphan_elimination               true
% 3.48/0.99  --inst_learning_loop_flag               true
% 3.48/0.99  --inst_learning_start                   3000
% 3.48/0.99  --inst_learning_factor                  2
% 3.48/0.99  --inst_start_prop_sim_after_learn       3
% 3.48/0.99  --inst_sel_renew                        solver
% 3.48/0.99  --inst_lit_activity_flag                true
% 3.48/0.99  --inst_restr_to_given                   false
% 3.48/0.99  --inst_activity_threshold               500
% 3.48/0.99  --inst_out_proof                        true
% 3.48/0.99  
% 3.48/0.99  ------ Resolution Options
% 3.48/0.99  
% 3.48/0.99  --resolution_flag                       true
% 3.48/0.99  --res_lit_sel                           adaptive
% 3.48/0.99  --res_lit_sel_side                      none
% 3.48/0.99  --res_ordering                          kbo
% 3.48/0.99  --res_to_prop_solver                    active
% 3.48/0.99  --res_prop_simpl_new                    false
% 3.48/0.99  --res_prop_simpl_given                  true
% 3.48/0.99  --res_passive_queue_type                priority_queues
% 3.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/0.99  --res_passive_queues_freq               [15;5]
% 3.48/0.99  --res_forward_subs                      full
% 3.48/0.99  --res_backward_subs                     full
% 3.48/0.99  --res_forward_subs_resolution           true
% 3.48/0.99  --res_backward_subs_resolution          true
% 3.48/0.99  --res_orphan_elimination                true
% 3.48/0.99  --res_time_limit                        2.
% 3.48/0.99  --res_out_proof                         true
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Options
% 3.48/0.99  
% 3.48/0.99  --superposition_flag                    true
% 3.48/0.99  --sup_passive_queue_type                priority_queues
% 3.48/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.48/0.99  --demod_completeness_check              fast
% 3.48/0.99  --demod_use_ground                      true
% 3.48/0.99  --sup_to_prop_solver                    passive
% 3.48/0.99  --sup_prop_simpl_new                    true
% 3.48/0.99  --sup_prop_simpl_given                  true
% 3.48/0.99  --sup_fun_splitting                     false
% 3.48/0.99  --sup_smt_interval                      50000
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Simplification Setup
% 3.48/0.99  
% 3.48/0.99  --sup_indices_passive                   []
% 3.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_full_bw                           [BwDemod]
% 3.48/0.99  --sup_immed_triv                        [TrivRules]
% 3.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_immed_bw_main                     []
% 3.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  
% 3.48/0.99  ------ Combination Options
% 3.48/0.99  
% 3.48/0.99  --comb_res_mult                         3
% 3.48/0.99  --comb_sup_mult                         2
% 3.48/0.99  --comb_inst_mult                        10
% 3.48/0.99  
% 3.48/0.99  ------ Debug Options
% 3.48/0.99  
% 3.48/0.99  --dbg_backtrace                         false
% 3.48/0.99  --dbg_dump_prop_clauses                 false
% 3.48/0.99  --dbg_dump_prop_clauses_file            -
% 3.48/0.99  --dbg_out_stat                          false
% 3.48/0.99  ------ Parsing...
% 3.48/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.48/0.99  ------ Proving...
% 3.48/0.99  ------ Problem Properties 
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  clauses                                 14
% 3.48/0.99  conjectures                             2
% 3.48/0.99  EPR                                     1
% 3.48/0.99  Horn                                    13
% 3.48/0.99  unary                                   12
% 3.48/0.99  binary                                  2
% 3.48/0.99  lits                                    16
% 3.48/0.99  lits eq                                 11
% 3.48/0.99  fd_pure                                 0
% 3.48/0.99  fd_pseudo                               0
% 3.48/0.99  fd_cond                                 1
% 3.48/0.99  fd_pseudo_cond                          0
% 3.48/0.99  AC symbols                              0
% 3.48/0.99  
% 3.48/0.99  ------ Schedule dynamic 5 is on 
% 3.48/0.99  
% 3.48/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ 
% 3.48/0.99  Current options:
% 3.48/0.99  ------ 
% 3.48/0.99  
% 3.48/0.99  ------ Input Options
% 3.48/0.99  
% 3.48/0.99  --out_options                           all
% 3.48/0.99  --tptp_safe_out                         true
% 3.48/0.99  --problem_path                          ""
% 3.48/0.99  --include_path                          ""
% 3.48/0.99  --clausifier                            res/vclausify_rel
% 3.48/0.99  --clausifier_options                    --mode clausify
% 3.48/0.99  --stdin                                 false
% 3.48/0.99  --stats_out                             all
% 3.48/0.99  
% 3.48/0.99  ------ General Options
% 3.48/0.99  
% 3.48/0.99  --fof                                   false
% 3.48/0.99  --time_out_real                         305.
% 3.48/0.99  --time_out_virtual                      -1.
% 3.48/0.99  --symbol_type_check                     false
% 3.48/0.99  --clausify_out                          false
% 3.48/0.99  --sig_cnt_out                           false
% 3.48/0.99  --trig_cnt_out                          false
% 3.48/0.99  --trig_cnt_out_tolerance                1.
% 3.48/0.99  --trig_cnt_out_sk_spl                   false
% 3.48/0.99  --abstr_cl_out                          false
% 3.48/0.99  
% 3.48/0.99  ------ Global Options
% 3.48/0.99  
% 3.48/0.99  --schedule                              default
% 3.48/0.99  --add_important_lit                     false
% 3.48/0.99  --prop_solver_per_cl                    1000
% 3.48/0.99  --min_unsat_core                        false
% 3.48/0.99  --soft_assumptions                      false
% 3.48/0.99  --soft_lemma_size                       3
% 3.48/0.99  --prop_impl_unit_size                   0
% 3.48/0.99  --prop_impl_unit                        []
% 3.48/0.99  --share_sel_clauses                     true
% 3.48/0.99  --reset_solvers                         false
% 3.48/0.99  --bc_imp_inh                            [conj_cone]
% 3.48/0.99  --conj_cone_tolerance                   3.
% 3.48/0.99  --extra_neg_conj                        none
% 3.48/0.99  --large_theory_mode                     true
% 3.48/0.99  --prolific_symb_bound                   200
% 3.48/0.99  --lt_threshold                          2000
% 3.48/0.99  --clause_weak_htbl                      true
% 3.48/0.99  --gc_record_bc_elim                     false
% 3.48/0.99  
% 3.48/0.99  ------ Preprocessing Options
% 3.48/0.99  
% 3.48/0.99  --preprocessing_flag                    true
% 3.48/0.99  --time_out_prep_mult                    0.1
% 3.48/0.99  --splitting_mode                        input
% 3.48/0.99  --splitting_grd                         true
% 3.48/0.99  --splitting_cvd                         false
% 3.48/0.99  --splitting_cvd_svl                     false
% 3.48/0.99  --splitting_nvd                         32
% 3.48/0.99  --sub_typing                            true
% 3.48/0.99  --prep_gs_sim                           true
% 3.48/0.99  --prep_unflatten                        true
% 3.48/0.99  --prep_res_sim                          true
% 3.48/0.99  --prep_upred                            true
% 3.48/0.99  --prep_sem_filter                       exhaustive
% 3.48/0.99  --prep_sem_filter_out                   false
% 3.48/0.99  --pred_elim                             true
% 3.48/0.99  --res_sim_input                         true
% 3.48/0.99  --eq_ax_congr_red                       true
% 3.48/0.99  --pure_diseq_elim                       true
% 3.48/0.99  --brand_transform                       false
% 3.48/0.99  --non_eq_to_eq                          false
% 3.48/0.99  --prep_def_merge                        true
% 3.48/0.99  --prep_def_merge_prop_impl              false
% 3.48/0.99  --prep_def_merge_mbd                    true
% 3.48/0.99  --prep_def_merge_tr_red                 false
% 3.48/0.99  --prep_def_merge_tr_cl                  false
% 3.48/0.99  --smt_preprocessing                     true
% 3.48/0.99  --smt_ac_axioms                         fast
% 3.48/0.99  --preprocessed_out                      false
% 3.48/0.99  --preprocessed_stats                    false
% 3.48/0.99  
% 3.48/0.99  ------ Abstraction refinement Options
% 3.48/0.99  
% 3.48/0.99  --abstr_ref                             []
% 3.48/0.99  --abstr_ref_prep                        false
% 3.48/0.99  --abstr_ref_until_sat                   false
% 3.48/0.99  --abstr_ref_sig_restrict                funpre
% 3.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.48/0.99  --abstr_ref_under                       []
% 3.48/0.99  
% 3.48/0.99  ------ SAT Options
% 3.48/0.99  
% 3.48/0.99  --sat_mode                              false
% 3.48/0.99  --sat_fm_restart_options                ""
% 3.48/0.99  --sat_gr_def                            false
% 3.48/0.99  --sat_epr_types                         true
% 3.48/0.99  --sat_non_cyclic_types                  false
% 3.48/0.99  --sat_finite_models                     false
% 3.48/0.99  --sat_fm_lemmas                         false
% 3.48/0.99  --sat_fm_prep                           false
% 3.48/0.99  --sat_fm_uc_incr                        true
% 3.48/0.99  --sat_out_model                         small
% 3.48/0.99  --sat_out_clauses                       false
% 3.48/0.99  
% 3.48/0.99  ------ QBF Options
% 3.48/0.99  
% 3.48/0.99  --qbf_mode                              false
% 3.48/0.99  --qbf_elim_univ                         false
% 3.48/0.99  --qbf_dom_inst                          none
% 3.48/0.99  --qbf_dom_pre_inst                      false
% 3.48/0.99  --qbf_sk_in                             false
% 3.48/0.99  --qbf_pred_elim                         true
% 3.48/0.99  --qbf_split                             512
% 3.48/0.99  
% 3.48/0.99  ------ BMC1 Options
% 3.48/0.99  
% 3.48/0.99  --bmc1_incremental                      false
% 3.48/0.99  --bmc1_axioms                           reachable_all
% 3.48/0.99  --bmc1_min_bound                        0
% 3.48/0.99  --bmc1_max_bound                        -1
% 3.48/0.99  --bmc1_max_bound_default                -1
% 3.48/0.99  --bmc1_symbol_reachability              true
% 3.48/0.99  --bmc1_property_lemmas                  false
% 3.48/0.99  --bmc1_k_induction                      false
% 3.48/0.99  --bmc1_non_equiv_states                 false
% 3.48/0.99  --bmc1_deadlock                         false
% 3.48/0.99  --bmc1_ucm                              false
% 3.48/0.99  --bmc1_add_unsat_core                   none
% 3.48/0.99  --bmc1_unsat_core_children              false
% 3.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.48/0.99  --bmc1_out_stat                         full
% 3.48/0.99  --bmc1_ground_init                      false
% 3.48/0.99  --bmc1_pre_inst_next_state              false
% 3.48/0.99  --bmc1_pre_inst_state                   false
% 3.48/0.99  --bmc1_pre_inst_reach_state             false
% 3.48/0.99  --bmc1_out_unsat_core                   false
% 3.48/0.99  --bmc1_aig_witness_out                  false
% 3.48/0.99  --bmc1_verbose                          false
% 3.48/0.99  --bmc1_dump_clauses_tptp                false
% 3.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.48/0.99  --bmc1_dump_file                        -
% 3.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.48/0.99  --bmc1_ucm_extend_mode                  1
% 3.48/0.99  --bmc1_ucm_init_mode                    2
% 3.48/0.99  --bmc1_ucm_cone_mode                    none
% 3.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.48/0.99  --bmc1_ucm_relax_model                  4
% 3.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.48/0.99  --bmc1_ucm_layered_model                none
% 3.48/0.99  --bmc1_ucm_max_lemma_size               10
% 3.48/0.99  
% 3.48/0.99  ------ AIG Options
% 3.48/0.99  
% 3.48/0.99  --aig_mode                              false
% 3.48/0.99  
% 3.48/0.99  ------ Instantiation Options
% 3.48/0.99  
% 3.48/0.99  --instantiation_flag                    true
% 3.48/0.99  --inst_sos_flag                         false
% 3.48/0.99  --inst_sos_phase                        true
% 3.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.48/0.99  --inst_lit_sel_side                     none
% 3.48/0.99  --inst_solver_per_active                1400
% 3.48/0.99  --inst_solver_calls_frac                1.
% 3.48/0.99  --inst_passive_queue_type               priority_queues
% 3.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.48/0.99  --inst_passive_queues_freq              [25;2]
% 3.48/0.99  --inst_dismatching                      true
% 3.48/0.99  --inst_eager_unprocessed_to_passive     true
% 3.48/0.99  --inst_prop_sim_given                   true
% 3.48/0.99  --inst_prop_sim_new                     false
% 3.48/0.99  --inst_subs_new                         false
% 3.48/0.99  --inst_eq_res_simp                      false
% 3.48/0.99  --inst_subs_given                       false
% 3.48/0.99  --inst_orphan_elimination               true
% 3.48/0.99  --inst_learning_loop_flag               true
% 3.48/0.99  --inst_learning_start                   3000
% 3.48/0.99  --inst_learning_factor                  2
% 3.48/0.99  --inst_start_prop_sim_after_learn       3
% 3.48/0.99  --inst_sel_renew                        solver
% 3.48/0.99  --inst_lit_activity_flag                true
% 3.48/0.99  --inst_restr_to_given                   false
% 3.48/0.99  --inst_activity_threshold               500
% 3.48/0.99  --inst_out_proof                        true
% 3.48/0.99  
% 3.48/0.99  ------ Resolution Options
% 3.48/0.99  
% 3.48/0.99  --resolution_flag                       false
% 3.48/0.99  --res_lit_sel                           adaptive
% 3.48/0.99  --res_lit_sel_side                      none
% 3.48/0.99  --res_ordering                          kbo
% 3.48/0.99  --res_to_prop_solver                    active
% 3.48/0.99  --res_prop_simpl_new                    false
% 3.48/0.99  --res_prop_simpl_given                  true
% 3.48/0.99  --res_passive_queue_type                priority_queues
% 3.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.48/0.99  --res_passive_queues_freq               [15;5]
% 3.48/0.99  --res_forward_subs                      full
% 3.48/0.99  --res_backward_subs                     full
% 3.48/0.99  --res_forward_subs_resolution           true
% 3.48/0.99  --res_backward_subs_resolution          true
% 3.48/0.99  --res_orphan_elimination                true
% 3.48/0.99  --res_time_limit                        2.
% 3.48/0.99  --res_out_proof                         true
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Options
% 3.48/0.99  
% 3.48/0.99  --superposition_flag                    true
% 3.48/0.99  --sup_passive_queue_type                priority_queues
% 3.48/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.48/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.48/0.99  --demod_completeness_check              fast
% 3.48/0.99  --demod_use_ground                      true
% 3.48/0.99  --sup_to_prop_solver                    passive
% 3.48/0.99  --sup_prop_simpl_new                    true
% 3.48/0.99  --sup_prop_simpl_given                  true
% 3.48/0.99  --sup_fun_splitting                     false
% 3.48/0.99  --sup_smt_interval                      50000
% 3.48/0.99  
% 3.48/0.99  ------ Superposition Simplification Setup
% 3.48/0.99  
% 3.48/0.99  --sup_indices_passive                   []
% 3.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_full_bw                           [BwDemod]
% 3.48/0.99  --sup_immed_triv                        [TrivRules]
% 3.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_immed_bw_main                     []
% 3.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.48/0.99  
% 3.48/0.99  ------ Combination Options
% 3.48/0.99  
% 3.48/0.99  --comb_res_mult                         3
% 3.48/0.99  --comb_sup_mult                         2
% 3.48/0.99  --comb_inst_mult                        10
% 3.48/0.99  
% 3.48/0.99  ------ Debug Options
% 3.48/0.99  
% 3.48/0.99  --dbg_backtrace                         false
% 3.48/0.99  --dbg_dump_prop_clauses                 false
% 3.48/0.99  --dbg_dump_prop_clauses_file            -
% 3.48/0.99  --dbg_out_stat                          false
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  ------ Proving...
% 3.48/0.99  
% 3.48/0.99  
% 3.48/0.99  % SZS status Theorem for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.48/0.99  
% 3.48/0.99  fof(f4,axiom,(
% 3.48/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f16,plain,(
% 3.48/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 3.48/0.99    inference(ennf_transformation,[],[f4])).
% 3.48/0.99  
% 3.48/0.99  fof(f21,plain,(
% 3.48/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 3.48/0.99    introduced(choice_axiom,[])).
% 3.48/0.99  
% 3.48/0.99  fof(f22,plain,(
% 3.48/0.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 3.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f21])).
% 3.48/0.99  
% 3.48/0.99  fof(f29,plain,(
% 3.48/0.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.48/0.99    inference(cnf_transformation,[],[f22])).
% 3.48/0.99  
% 3.48/0.99  fof(f3,axiom,(
% 3.48/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f14,plain,(
% 3.48/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.48/0.99    inference(rectify,[],[f3])).
% 3.48/0.99  
% 3.48/0.99  fof(f15,plain,(
% 3.48/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.48/0.99    inference(ennf_transformation,[],[f14])).
% 3.48/0.99  
% 3.48/0.99  fof(f19,plain,(
% 3.48/0.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 3.48/0.99    introduced(choice_axiom,[])).
% 3.48/0.99  
% 3.48/0.99  fof(f20,plain,(
% 3.48/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f19])).
% 3.48/0.99  
% 3.48/0.99  fof(f28,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f20])).
% 3.48/0.99  
% 3.48/0.99  fof(f11,axiom,(
% 3.48/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f36,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f11])).
% 3.48/0.99  
% 3.48/0.99  fof(f42,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.48/0.99    inference(definition_unfolding,[],[f28,f36])).
% 3.48/0.99  
% 3.48/0.99  fof(f12,conjecture,(
% 3.48/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f13,negated_conjecture,(
% 3.48/0.99    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 3.48/0.99    inference(negated_conjecture,[],[f12])).
% 3.48/0.99  
% 3.48/0.99  fof(f17,plain,(
% 3.48/0.99    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 3.48/0.99    inference(ennf_transformation,[],[f13])).
% 3.48/0.99  
% 3.48/0.99  fof(f18,plain,(
% 3.48/0.99    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 3.48/0.99    inference(flattening,[],[f17])).
% 3.48/0.99  
% 3.48/0.99  fof(f23,plain,(
% 3.48/0.99    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK2 != sK4 & r1_xboole_0(sK4,sK3) & r1_xboole_0(sK2,sK3) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3))),
% 3.48/0.99    introduced(choice_axiom,[])).
% 3.48/0.99  
% 3.48/0.99  fof(f24,plain,(
% 3.48/0.99    sK2 != sK4 & r1_xboole_0(sK4,sK3) & r1_xboole_0(sK2,sK3) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3)),
% 3.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f23])).
% 3.48/0.99  
% 3.48/0.99  fof(f38,plain,(
% 3.48/0.99    r1_xboole_0(sK2,sK3)),
% 3.48/0.99    inference(cnf_transformation,[],[f24])).
% 3.48/0.99  
% 3.48/0.99  fof(f7,axiom,(
% 3.48/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f32,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.48/0.99    inference(cnf_transformation,[],[f7])).
% 3.48/0.99  
% 3.48/0.99  fof(f5,axiom,(
% 3.48/0.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f30,plain,(
% 3.48/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.48/0.99    inference(cnf_transformation,[],[f5])).
% 3.48/0.99  
% 3.48/0.99  fof(f37,plain,(
% 3.48/0.99    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3)),
% 3.48/0.99    inference(cnf_transformation,[],[f24])).
% 3.48/0.99  
% 3.48/0.99  fof(f9,axiom,(
% 3.48/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f34,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f9])).
% 3.48/0.99  
% 3.48/0.99  fof(f39,plain,(
% 3.48/0.99    r1_xboole_0(sK4,sK3)),
% 3.48/0.99    inference(cnf_transformation,[],[f24])).
% 3.48/0.99  
% 3.48/0.99  fof(f2,axiom,(
% 3.48/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f26,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f2])).
% 3.48/0.99  
% 3.48/0.99  fof(f41,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.48/0.99    inference(definition_unfolding,[],[f26,f36,f36])).
% 3.48/0.99  
% 3.48/0.99  fof(f1,axiom,(
% 3.48/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f25,plain,(
% 3.48/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f1])).
% 3.48/0.99  
% 3.48/0.99  fof(f8,axiom,(
% 3.48/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f33,plain,(
% 3.48/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.48/0.99    inference(cnf_transformation,[],[f8])).
% 3.48/0.99  
% 3.48/0.99  fof(f10,axiom,(
% 3.48/0.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f35,plain,(
% 3.48/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.48/0.99    inference(cnf_transformation,[],[f10])).
% 3.48/0.99  
% 3.48/0.99  fof(f6,axiom,(
% 3.48/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.48/0.99  
% 3.48/0.99  fof(f31,plain,(
% 3.48/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.48/0.99    inference(cnf_transformation,[],[f6])).
% 3.48/0.99  
% 3.48/0.99  fof(f44,plain,(
% 3.48/0.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.48/0.99    inference(definition_unfolding,[],[f31,f36])).
% 3.48/0.99  
% 3.48/0.99  fof(f40,plain,(
% 3.48/0.99    sK2 != sK4),
% 3.48/0.99    inference(cnf_transformation,[],[f24])).
% 3.48/0.99  
% 3.48/0.99  cnf(c_4,plain,
% 3.48/0.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_234,plain,
% 3.48/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2,plain,
% 3.48/0.99      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.48/0.99      | ~ r1_xboole_0(X1,X2) ),
% 3.48/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_13,negated_conjecture,
% 3.48/0.99      ( r1_xboole_0(sK2,sK3) ),
% 3.48/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_100,plain,
% 3.48/0.99      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.48/0.99      | sK3 != X2
% 3.48/0.99      | sK2 != X1 ),
% 3.48/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_13]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_101,plain,
% 3.48/0.99      ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 3.48/0.99      inference(unflattening,[status(thm)],[c_100]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_231,plain,
% 3.48/0.99      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_101]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_8044,plain,
% 3.48/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_234,c_231]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_7,plain,
% 3.48/0.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.48/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_8219,plain,
% 3.48/0.99      ( k2_xboole_0(k4_xboole_0(sK2,sK3),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_8044,c_7]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_5,plain,
% 3.48/0.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_8248,plain,
% 3.48/0.99      ( k2_xboole_0(k4_xboole_0(sK2,sK3),sK2) = k4_xboole_0(sK2,sK3) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_8219,c_5]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_14,negated_conjecture,
% 3.48/0.99      ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
% 3.48/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_9,plain,
% 3.48/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 3.48/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_536,plain,
% 3.48/0.99      ( k4_xboole_0(k2_xboole_0(sK2,sK3),sK3) = k4_xboole_0(sK4,sK3) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_14,c_9]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_548,plain,
% 3.48/0.99      ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK4,sK3) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_536,c_9]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_12,negated_conjecture,
% 3.48/0.99      ( r1_xboole_0(sK4,sK3) ),
% 3.48/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_91,plain,
% 3.48/0.99      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.48/0.99      | sK3 != X2
% 3.48/0.99      | sK4 != X1 ),
% 3.48/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_12]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_92,plain,
% 3.48/0.99      ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) ),
% 3.48/0.99      inference(unflattening,[status(thm)],[c_91]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_232,plain,
% 3.48/0.99      ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) != iProver_top ),
% 3.48/0.99      inference(predicate_to_equality,[status(thm)],[c_92]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_659,plain,
% 3.48/0.99      ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_548,c_232]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_8045,plain,
% 3.48/0.99      ( k4_xboole_0(sK4,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_234,c_659]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1,plain,
% 3.48/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.48/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_562,plain,
% 3.48/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3524,plain,
% 3.48/0.99      ( k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = k2_xboole_0(k4_xboole_0(sK3,sK4),sK3) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_548,c_562]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_0,plain,
% 3.48/0.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.48/0.99      inference(cnf_transformation,[],[f25]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_664,plain,
% 3.48/0.99      ( k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) = k2_xboole_0(sK3,sK4) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_548,c_7]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_666,plain,
% 3.48/0.99      ( k2_xboole_0(sK3,sK4) = k2_xboole_0(sK3,sK2) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_664,c_7]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_700,plain,
% 3.48/0.99      ( k4_xboole_0(k2_xboole_0(sK3,sK2),sK4) = k4_xboole_0(sK3,sK4) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_666,c_9]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_841,plain,
% 3.48/0.99      ( k4_xboole_0(k2_xboole_0(sK2,sK3),sK4) = k4_xboole_0(sK3,sK4) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_0,c_700]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_561,plain,
% 3.48/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_8,plain,
% 3.48/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_10,plain,
% 3.48/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.48/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6,plain,
% 3.48/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.48/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_243,plain,
% 3.48/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_6,c_8]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_625,plain,
% 3.48/0.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_10,c_243]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_627,plain,
% 3.48/0.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_625,c_7]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2346,plain,
% 3.48/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_561,c_8,c_627]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2380,plain,
% 3.48/0.99      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK2,sK3),sK4),k4_xboole_0(sK3,sK4)) = sK4 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_841,c_2346]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_846,plain,
% 3.48/0.99      ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK4,k4_xboole_0(sK3,sK4)) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_700,c_7]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_848,plain,
% 3.48/0.99      ( k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)) = k2_xboole_0(sK2,sK3) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_846,c_7,c_14]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_920,plain,
% 3.48/0.99      ( k2_xboole_0(sK4,k2_xboole_0(sK2,sK3)) = k2_xboole_0(sK2,sK3) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_0,c_848]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_538,plain,
% 3.48/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_9,c_7]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_543,plain,
% 3.48/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_538,c_7]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1185,plain,
% 3.48/0.99      ( k2_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3)) = k2_xboole_0(k2_xboole_0(sK2,sK3),sK4) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_920,c_543]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_506,plain,
% 3.48/0.99      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_243,c_7]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_511,plain,
% 3.48/0.99      ( k2_xboole_0(X0,X0) = X0 ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_506,c_5]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1206,plain,
% 3.48/0.99      ( k2_xboole_0(k2_xboole_0(sK2,sK3),sK4) = k2_xboole_0(sK2,sK3) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_1185,c_511]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_535,plain,
% 3.48/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_7,c_9]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1575,plain,
% 3.48/0.99      ( k4_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK3,sK2)),k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK4,k4_xboole_0(k2_xboole_0(sK3,sK2),sK4)) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_700,c_535]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1606,plain,
% 3.48/0.99      ( k4_xboole_0(k2_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK4,k4_xboole_0(sK3,sK4)) ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_1575,c_700,c_848]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_2432,plain,
% 3.48/0.99      ( k4_xboole_0(sK4,k4_xboole_0(sK3,sK4)) = sK4 ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_2380,c_1206,c_1606]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_3190,plain,
% 3.48/0.99      ( k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK3,sK4),X0)) = k4_xboole_0(sK4,X0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_2432,c_10]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6603,plain,
% 3.48/0.99      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = k4_xboole_0(sK4,k2_xboole_0(k4_xboole_0(sK3,sK4),sK3)) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_3524,c_3190]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6632,plain,
% 3.48/0.99      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = k4_xboole_0(sK4,sK3) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_6603,c_3190]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_6634,plain,
% 3.48/0.99      ( k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK2,sK3))) = k4_xboole_0(sK2,sK3) ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_6632,c_548]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_8374,plain,
% 3.48/0.99      ( k4_xboole_0(sK4,k1_xboole_0) = k4_xboole_0(sK2,sK3) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_8045,c_6634]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_8381,plain,
% 3.48/0.99      ( k4_xboole_0(sK2,sK3) = sK4 ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_8374,c_8]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_12087,plain,
% 3.48/0.99      ( k2_xboole_0(sK4,sK2) = sK4 ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_8248,c_8381]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_12105,plain,
% 3.48/0.99      ( k2_xboole_0(sK2,sK4) = sK4 ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_12087,c_0]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_922,plain,
% 3.48/0.99      ( k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK4,k2_xboole_0(sK3,sK2)) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_848,c_9]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_663,plain,
% 3.48/0.99      ( k4_xboole_0(sK4,k2_xboole_0(sK3,X0)) = k4_xboole_0(k4_xboole_0(sK2,sK3),X0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_548,c_10]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_669,plain,
% 3.48/0.99      ( k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK4,k2_xboole_0(sK3,X0)) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_663,c_10]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_924,plain,
% 3.48/0.99      ( k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK2)) ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_922,c_669]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_932,plain,
% 3.48/0.99      ( k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK2)) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_0,c_924]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_943,plain,
% 3.48/0.99      ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_932,c_243]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_944,plain,
% 3.48/0.99      ( k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_943,c_924]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_622,plain,
% 3.48/0.99      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_10,c_7]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_9165,plain,
% 3.48/0.99      ( k2_xboole_0(sK2,k4_xboole_0(k2_xboole_0(sK2,sK3),sK3)) = k2_xboole_0(sK2,k1_xboole_0) ),
% 3.48/0.99      inference(superposition,[status(thm)],[c_944,c_622]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_9384,plain,
% 3.48/0.99      ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = sK2 ),
% 3.48/0.99      inference(demodulation,[status(thm)],[c_9165,c_5,c_9]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_9857,plain,
% 3.48/0.99      ( k2_xboole_0(sK2,sK4) = sK2 ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_9384,c_8381]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_12117,plain,
% 3.48/0.99      ( sK4 = sK2 ),
% 3.48/0.99      inference(light_normalisation,[status(thm)],[c_12105,c_9857]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_150,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_279,plain,
% 3.48/0.99      ( sK4 != X0 | sK2 != X0 | sK2 = sK4 ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_150]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_1416,plain,
% 3.48/0.99      ( sK4 != sK2 | sK2 = sK4 | sK2 != sK2 ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_279]) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_149,plain,( X0 = X0 ),theory(equality) ).
% 3.48/0.99  
% 3.48/0.99  cnf(c_964,plain,
% 3.48/0.99      ( sK2 = sK2 ),
% 3.48/0.99      inference(instantiation,[status(thm)],[c_149]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(c_11,negated_conjecture,
% 3.48/1.00      ( sK2 != sK4 ),
% 3.48/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.48/1.00  
% 3.48/1.00  cnf(contradiction,plain,
% 3.48/1.00      ( $false ),
% 3.48/1.00      inference(minisat,[status(thm)],[c_12117,c_1416,c_964,c_11]) ).
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.48/1.00  
% 3.48/1.00  ------                               Statistics
% 3.48/1.00  
% 3.48/1.00  ------ General
% 3.48/1.00  
% 3.48/1.00  abstr_ref_over_cycles:                  0
% 3.48/1.00  abstr_ref_under_cycles:                 0
% 3.48/1.00  gc_basic_clause_elim:                   0
% 3.48/1.00  forced_gc_time:                         0
% 3.48/1.00  parsing_time:                           0.012
% 3.48/1.00  unif_index_cands_time:                  0.
% 3.48/1.00  unif_index_add_time:                    0.
% 3.48/1.00  orderings_time:                         0.
% 3.48/1.00  out_proof_time:                         0.008
% 3.48/1.00  total_time:                             0.335
% 3.48/1.00  num_of_symbols:                         41
% 3.48/1.00  num_of_terms:                           16265
% 3.48/1.00  
% 3.48/1.00  ------ Preprocessing
% 3.48/1.00  
% 3.48/1.00  num_of_splits:                          0
% 3.48/1.00  num_of_split_atoms:                     0
% 3.48/1.00  num_of_reused_defs:                     0
% 3.48/1.00  num_eq_ax_congr_red:                    9
% 3.48/1.00  num_of_sem_filtered_clauses:            1
% 3.48/1.00  num_of_subtypes:                        0
% 3.48/1.00  monotx_restored_types:                  0
% 3.48/1.00  sat_num_of_epr_types:                   0
% 3.48/1.00  sat_num_of_non_cyclic_types:            0
% 3.48/1.00  sat_guarded_non_collapsed_types:        0
% 3.48/1.00  num_pure_diseq_elim:                    0
% 3.48/1.00  simp_replaced_by:                       0
% 3.48/1.00  res_preprocessed:                       68
% 3.48/1.00  prep_upred:                             0
% 3.48/1.00  prep_unflattend:                        6
% 3.48/1.00  smt_new_axioms:                         0
% 3.48/1.00  pred_elim_cands:                        1
% 3.48/1.00  pred_elim:                              1
% 3.48/1.00  pred_elim_cl:                           1
% 3.48/1.00  pred_elim_cycles:                       3
% 3.48/1.00  merged_defs:                            0
% 3.48/1.00  merged_defs_ncl:                        0
% 3.48/1.00  bin_hyper_res:                          0
% 3.48/1.00  prep_cycles:                            4
% 3.48/1.00  pred_elim_time:                         0.
% 3.48/1.00  splitting_time:                         0.
% 3.48/1.00  sem_filter_time:                        0.
% 3.48/1.00  monotx_time:                            0.
% 3.48/1.00  subtype_inf_time:                       0.
% 3.48/1.00  
% 3.48/1.00  ------ Problem properties
% 3.48/1.00  
% 3.48/1.00  clauses:                                14
% 3.48/1.00  conjectures:                            2
% 3.48/1.00  epr:                                    1
% 3.48/1.00  horn:                                   13
% 3.48/1.00  ground:                                 2
% 3.48/1.00  unary:                                  12
% 3.48/1.00  binary:                                 2
% 3.48/1.00  lits:                                   16
% 3.48/1.00  lits_eq:                                11
% 3.48/1.00  fd_pure:                                0
% 3.48/1.00  fd_pseudo:                              0
% 3.48/1.00  fd_cond:                                1
% 3.48/1.00  fd_pseudo_cond:                         0
% 3.48/1.00  ac_symbols:                             0
% 3.48/1.00  
% 3.48/1.00  ------ Propositional Solver
% 3.48/1.00  
% 3.48/1.00  prop_solver_calls:                      32
% 3.48/1.00  prop_fast_solver_calls:                 313
% 3.48/1.00  smt_solver_calls:                       0
% 3.48/1.00  smt_fast_solver_calls:                  0
% 3.48/1.00  prop_num_of_clauses:                    3153
% 3.48/1.00  prop_preprocess_simplified:             4854
% 3.48/1.00  prop_fo_subsumed:                       0
% 3.48/1.00  prop_solver_time:                       0.
% 3.48/1.00  smt_solver_time:                        0.
% 3.48/1.00  smt_fast_solver_time:                   0.
% 3.48/1.00  prop_fast_solver_time:                  0.
% 3.48/1.00  prop_unsat_core_time:                   0.
% 3.48/1.00  
% 3.48/1.00  ------ QBF
% 3.48/1.00  
% 3.48/1.00  qbf_q_res:                              0
% 3.48/1.00  qbf_num_tautologies:                    0
% 3.48/1.00  qbf_prep_cycles:                        0
% 3.48/1.00  
% 3.48/1.00  ------ BMC1
% 3.48/1.00  
% 3.48/1.00  bmc1_current_bound:                     -1
% 3.48/1.00  bmc1_last_solved_bound:                 -1
% 3.48/1.00  bmc1_unsat_core_size:                   -1
% 3.48/1.00  bmc1_unsat_core_parents_size:           -1
% 3.48/1.00  bmc1_merge_next_fun:                    0
% 3.48/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.48/1.00  
% 3.48/1.00  ------ Instantiation
% 3.48/1.00  
% 3.48/1.00  inst_num_of_clauses:                    1019
% 3.48/1.00  inst_num_in_passive:                    429
% 3.48/1.00  inst_num_in_active:                     428
% 3.48/1.00  inst_num_in_unprocessed:                162
% 3.48/1.00  inst_num_of_loops:                      550
% 3.48/1.00  inst_num_of_learning_restarts:          0
% 3.48/1.00  inst_num_moves_active_passive:          117
% 3.48/1.00  inst_lit_activity:                      0
% 3.48/1.00  inst_lit_activity_moves:                0
% 3.48/1.00  inst_num_tautologies:                   0
% 3.48/1.00  inst_num_prop_implied:                  0
% 3.48/1.00  inst_num_existing_simplified:           0
% 3.48/1.00  inst_num_eq_res_simplified:             0
% 3.48/1.00  inst_num_child_elim:                    0
% 3.48/1.00  inst_num_of_dismatching_blockings:      389
% 3.48/1.00  inst_num_of_non_proper_insts:           1103
% 3.48/1.00  inst_num_of_duplicates:                 0
% 3.48/1.00  inst_inst_num_from_inst_to_res:         0
% 3.48/1.00  inst_dismatching_checking_time:         0.
% 3.48/1.00  
% 3.48/1.00  ------ Resolution
% 3.48/1.00  
% 3.48/1.00  res_num_of_clauses:                     0
% 3.48/1.00  res_num_in_passive:                     0
% 3.48/1.00  res_num_in_active:                      0
% 3.48/1.00  res_num_of_loops:                       72
% 3.48/1.00  res_forward_subset_subsumed:            212
% 3.48/1.00  res_backward_subset_subsumed:           0
% 3.48/1.00  res_forward_subsumed:                   0
% 3.48/1.00  res_backward_subsumed:                  0
% 3.48/1.00  res_forward_subsumption_resolution:     0
% 3.48/1.00  res_backward_subsumption_resolution:    0
% 3.48/1.00  res_clause_to_clause_subsumption:       7465
% 3.48/1.00  res_orphan_elimination:                 0
% 3.48/1.00  res_tautology_del:                      125
% 3.48/1.00  res_num_eq_res_simplified:              0
% 3.48/1.00  res_num_sel_changes:                    0
% 3.48/1.00  res_moves_from_active_to_pass:          0
% 3.48/1.00  
% 3.48/1.00  ------ Superposition
% 3.48/1.00  
% 3.48/1.00  sup_time_total:                         0.
% 3.48/1.00  sup_time_generating:                    0.
% 3.48/1.00  sup_time_sim_full:                      0.
% 3.48/1.00  sup_time_sim_immed:                     0.
% 3.48/1.00  
% 3.48/1.00  sup_num_of_clauses:                     787
% 3.48/1.00  sup_num_in_active:                      89
% 3.48/1.00  sup_num_in_passive:                     698
% 3.48/1.00  sup_num_of_loops:                       109
% 3.48/1.00  sup_fw_superposition:                   1293
% 3.48/1.00  sup_bw_superposition:                   1047
% 3.48/1.00  sup_immediate_simplified:               1452
% 3.48/1.00  sup_given_eliminated:                   7
% 3.48/1.00  comparisons_done:                       0
% 3.48/1.00  comparisons_avoided:                    0
% 3.48/1.00  
% 3.48/1.00  ------ Simplifications
% 3.48/1.00  
% 3.48/1.00  
% 3.48/1.00  sim_fw_subset_subsumed:                 0
% 3.48/1.00  sim_bw_subset_subsumed:                 0
% 3.48/1.00  sim_fw_subsumed:                        196
% 3.48/1.00  sim_bw_subsumed:                        10
% 3.48/1.00  sim_fw_subsumption_res:                 0
% 3.48/1.00  sim_bw_subsumption_res:                 0
% 3.48/1.00  sim_tautology_del:                      0
% 3.48/1.00  sim_eq_tautology_del:                   299
% 3.48/1.00  sim_eq_res_simp:                        0
% 3.48/1.00  sim_fw_demodulated:                     770
% 3.48/1.00  sim_bw_demodulated:                     67
% 3.48/1.00  sim_light_normalised:                   738
% 3.48/1.00  sim_joinable_taut:                      0
% 3.48/1.00  sim_joinable_simp:                      0
% 3.48/1.00  sim_ac_normalised:                      0
% 3.48/1.00  sim_smt_subsumption:                    0
% 3.48/1.00  
%------------------------------------------------------------------------------
