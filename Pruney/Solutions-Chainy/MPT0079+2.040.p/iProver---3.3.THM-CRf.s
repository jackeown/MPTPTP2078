%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:52 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  154 (2592 expanded)
%              Number of clauses        :  115 ( 966 expanded)
%              Number of leaves         :   14 ( 677 expanded)
%              Depth                    :   25
%              Number of atoms          :  186 (3942 expanded)
%              Number of equality atoms :  161 (3047 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f29])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,
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

fof(f20,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).

fof(f35,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f30,f29,f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f24,f29])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f33,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_56,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_12])).

cnf(c_57,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_56])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_80,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_8,c_7])).

cnf(c_90,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK3),sK1)) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_57,c_80])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_79,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_5])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_84,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_110,plain,
    ( k4_xboole_0(sK3,sK1) = sK3 ),
    inference(demodulation,[status(thm)],[c_90,c_5,c_79,c_84])).

cnf(c_99,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[status(thm)],[c_80,c_80])).

cnf(c_100,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_99,c_79])).

cnf(c_101,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_100,c_84])).

cnf(c_1589,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK3,X0))) = k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_110,c_101])).

cnf(c_149,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_57,c_7])).

cnf(c_151,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_79,c_7])).

cnf(c_10,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_6,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_138,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_10,c_6])).

cnf(c_139,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_138,c_79])).

cnf(c_165,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_151,c_139])).

cnf(c_168,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_149,c_165])).

cnf(c_169,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_168,c_110])).

cnf(c_1640,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1589,c_169])).

cnf(c_1641,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) = sK3 ),
    inference(demodulation,[status(thm)],[c_1640,c_5])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_115,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_79,c_4])).

cnf(c_116,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_115,c_2])).

cnf(c_14,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_72,negated_conjecture,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_14,c_9,c_0])).

cnf(c_270,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
    inference(superposition,[status(thm)],[c_72,c_9])).

cnf(c_400,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_270,c_9])).

cnf(c_871,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_116,c_400])).

cnf(c_898,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_871,c_72])).

cnf(c_124,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_6])).

cnf(c_158,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_79])).

cnf(c_159,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_158,c_4])).

cnf(c_1566,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_159,c_101])).

cnf(c_1659,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1566,c_5])).

cnf(c_6340,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_124,c_124,c_1659])).

cnf(c_6395,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK3),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_898,c_6340])).

cnf(c_125,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_72,c_6])).

cnf(c_6421,plain,
    ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)),k4_xboole_0(sK2,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_125,c_6340])).

cnf(c_81,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_250,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_72,c_81])).

cnf(c_174,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_125,c_4])).

cnf(c_177,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_174,c_4])).

cnf(c_352,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK3)) = k2_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_250,c_177])).

cnf(c_113,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_57,c_4])).

cnf(c_119,plain,
    ( k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK3,sK3) ),
    inference(light_normalisation,[status(thm)],[c_113,c_110])).

cnf(c_120,plain,
    ( k2_xboole_0(sK3,sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_119,c_2])).

cnf(c_353,plain,
    ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_352,c_72,c_120])).

cnf(c_366,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_353,c_177])).

cnf(c_6522,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK2,sK3)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_6421,c_366])).

cnf(c_909,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK3)) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
    inference(superposition,[status(thm)],[c_898,c_6])).

cnf(c_127,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_4])).

cnf(c_131,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_127,c_4])).

cnf(c_1163,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_131,c_250])).

cnf(c_1335,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK3)) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK3)) ),
    inference(superposition,[status(thm)],[c_1163,c_6])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_61,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_13])).

cnf(c_62,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_61])).

cnf(c_91,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK2),sK0)) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_62,c_80])).

cnf(c_108,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_91,c_5,c_79,c_84])).

cnf(c_182,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_108,c_7])).

cnf(c_122,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_6])).

cnf(c_662,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_122,c_7])).

cnf(c_670,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_662,c_7])).

cnf(c_1348,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k4_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_1335,c_182,c_670])).

cnf(c_2065,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK3)) = k4_xboole_0(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_909,c_909,c_1348])).

cnf(c_6438,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)),k4_xboole_0(sK2,sK3)) = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[status(thm)],[c_2065,c_6340])).

cnf(c_913,plain,
    ( k2_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(sK0,sK3))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_898,c_81])).

cnf(c_2795,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
    inference(superposition,[status(thm)],[c_116,c_913])).

cnf(c_2838,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_2795,c_898])).

cnf(c_6506,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK2,sK3)) = k2_xboole_0(sK0,sK3) ),
    inference(light_normalisation,[status(thm)],[c_6438,c_2838])).

cnf(c_6523,plain,
    ( k2_xboole_0(sK0,sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_6522,c_6506])).

cnf(c_6546,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK3,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_6395,c_6523])).

cnf(c_6547,plain,
    ( k4_xboole_0(sK2,sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_6546,c_110,c_125])).

cnf(c_6929,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK1,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_6547,c_101])).

cnf(c_82,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_522,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_72,c_82])).

cnf(c_704,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),sK3) = k4_xboole_0(k2_xboole_0(sK2,X0),sK3) ),
    inference(superposition,[status(thm)],[c_522,c_122])).

cnf(c_97,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_79,c_80])).

cnf(c_103,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_97,c_5,c_79])).

cnf(c_1929,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,X0),sK3),sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_704,c_103])).

cnf(c_519,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_82])).

cnf(c_1748,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_519])).

cnf(c_1858,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1748,c_519])).

cnf(c_1939,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(k2_xboole_0(sK2,X0),sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1929,c_1858])).

cnf(c_137,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_72,c_10])).

cnf(c_140,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_137,c_72])).

cnf(c_251,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_140,c_81])).

cnf(c_1454,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(sK2,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_251,c_6])).

cnf(c_1200,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(X0,k2_xboole_0(X1,sK0))) = k4_xboole_0(sK2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_82,c_182])).

cnf(c_1477,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_1454,c_670,c_1200])).

cnf(c_526,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_140,c_82])).

cnf(c_1507,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_526])).

cnf(c_1525,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_526,c_131])).

cnf(c_1135,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(sK2,X0),sK3) ),
    inference(superposition,[status(thm)],[c_522,c_131])).

cnf(c_1541,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK2,X0),sK3) ),
    inference(light_normalisation,[status(thm)],[c_1525,c_1135])).

cnf(c_1558,plain,
    ( k2_xboole_0(k2_xboole_0(sK2,X0),sK3) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_1507,c_526,c_1541])).

cnf(c_1940,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1939,c_1477,c_1558])).

cnf(c_6941,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_6929,c_1940])).

cnf(c_6942,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) = sK2 ),
    inference(demodulation,[status(thm)],[c_6941,c_5])).

cnf(c_8170,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_1641,c_6942])).

cnf(c_8204,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_8170,c_6547])).

cnf(c_11,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_9629,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_8204,c_11])).

cnf(c_9630,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_9629])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:24:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.97/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/0.98  
% 3.97/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.97/0.98  
% 3.97/0.98  ------  iProver source info
% 3.97/0.98  
% 3.97/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.97/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.97/0.98  git: non_committed_changes: false
% 3.97/0.98  git: last_make_outside_of_git: false
% 3.97/0.98  
% 3.97/0.98  ------ 
% 3.97/0.98  
% 3.97/0.98  ------ Input Options
% 3.97/0.98  
% 3.97/0.98  --out_options                           all
% 3.97/0.98  --tptp_safe_out                         true
% 3.97/0.98  --problem_path                          ""
% 3.97/0.98  --include_path                          ""
% 3.97/0.98  --clausifier                            res/vclausify_rel
% 3.97/0.98  --clausifier_options                    --mode clausify
% 3.97/0.98  --stdin                                 false
% 3.97/0.98  --stats_out                             all
% 3.97/0.98  
% 3.97/0.98  ------ General Options
% 3.97/0.98  
% 3.97/0.98  --fof                                   false
% 3.97/0.98  --time_out_real                         305.
% 3.97/0.98  --time_out_virtual                      -1.
% 3.97/0.98  --symbol_type_check                     false
% 3.97/0.98  --clausify_out                          false
% 3.97/0.98  --sig_cnt_out                           false
% 3.97/0.98  --trig_cnt_out                          false
% 3.97/0.98  --trig_cnt_out_tolerance                1.
% 3.97/0.98  --trig_cnt_out_sk_spl                   false
% 3.97/0.98  --abstr_cl_out                          false
% 3.97/0.98  
% 3.97/0.98  ------ Global Options
% 3.97/0.98  
% 3.97/0.98  --schedule                              default
% 3.97/0.98  --add_important_lit                     false
% 3.97/0.98  --prop_solver_per_cl                    1000
% 3.97/0.98  --min_unsat_core                        false
% 3.97/0.98  --soft_assumptions                      false
% 3.97/0.98  --soft_lemma_size                       3
% 3.97/0.98  --prop_impl_unit_size                   0
% 3.97/0.98  --prop_impl_unit                        []
% 3.97/0.98  --share_sel_clauses                     true
% 3.97/0.98  --reset_solvers                         false
% 3.97/0.98  --bc_imp_inh                            [conj_cone]
% 3.97/0.98  --conj_cone_tolerance                   3.
% 3.97/0.98  --extra_neg_conj                        none
% 3.97/0.98  --large_theory_mode                     true
% 3.97/0.98  --prolific_symb_bound                   200
% 3.97/0.98  --lt_threshold                          2000
% 3.97/0.98  --clause_weak_htbl                      true
% 3.97/0.98  --gc_record_bc_elim                     false
% 3.97/0.98  
% 3.97/0.98  ------ Preprocessing Options
% 3.97/0.98  
% 3.97/0.98  --preprocessing_flag                    true
% 3.97/0.98  --time_out_prep_mult                    0.1
% 3.97/0.98  --splitting_mode                        input
% 3.97/0.98  --splitting_grd                         true
% 3.97/0.98  --splitting_cvd                         false
% 3.97/0.98  --splitting_cvd_svl                     false
% 3.97/0.98  --splitting_nvd                         32
% 3.97/0.98  --sub_typing                            true
% 3.97/0.98  --prep_gs_sim                           true
% 3.97/0.98  --prep_unflatten                        true
% 3.97/0.98  --prep_res_sim                          true
% 3.97/0.98  --prep_upred                            true
% 3.97/0.98  --prep_sem_filter                       exhaustive
% 3.97/0.98  --prep_sem_filter_out                   false
% 3.97/0.98  --pred_elim                             true
% 3.97/0.98  --res_sim_input                         true
% 3.97/0.98  --eq_ax_congr_red                       true
% 3.97/0.98  --pure_diseq_elim                       true
% 3.97/0.98  --brand_transform                       false
% 3.97/0.98  --non_eq_to_eq                          false
% 3.97/0.98  --prep_def_merge                        true
% 3.97/0.98  --prep_def_merge_prop_impl              false
% 3.97/0.98  --prep_def_merge_mbd                    true
% 3.97/0.98  --prep_def_merge_tr_red                 false
% 3.97/0.98  --prep_def_merge_tr_cl                  false
% 3.97/0.98  --smt_preprocessing                     true
% 3.97/0.98  --smt_ac_axioms                         fast
% 3.97/0.98  --preprocessed_out                      false
% 3.97/0.98  --preprocessed_stats                    false
% 3.97/0.98  
% 3.97/0.98  ------ Abstraction refinement Options
% 3.97/0.98  
% 3.97/0.98  --abstr_ref                             []
% 3.97/0.98  --abstr_ref_prep                        false
% 3.97/0.98  --abstr_ref_until_sat                   false
% 3.97/0.98  --abstr_ref_sig_restrict                funpre
% 3.97/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.97/0.98  --abstr_ref_under                       []
% 3.97/0.98  
% 3.97/0.98  ------ SAT Options
% 3.97/0.98  
% 3.97/0.98  --sat_mode                              false
% 3.97/0.98  --sat_fm_restart_options                ""
% 3.97/0.98  --sat_gr_def                            false
% 3.97/0.98  --sat_epr_types                         true
% 3.97/0.98  --sat_non_cyclic_types                  false
% 3.97/0.98  --sat_finite_models                     false
% 3.97/0.98  --sat_fm_lemmas                         false
% 3.97/0.98  --sat_fm_prep                           false
% 3.97/0.98  --sat_fm_uc_incr                        true
% 3.97/0.98  --sat_out_model                         small
% 3.97/0.98  --sat_out_clauses                       false
% 3.97/0.98  
% 3.97/0.98  ------ QBF Options
% 3.97/0.98  
% 3.97/0.98  --qbf_mode                              false
% 3.97/0.98  --qbf_elim_univ                         false
% 3.97/0.98  --qbf_dom_inst                          none
% 3.97/0.98  --qbf_dom_pre_inst                      false
% 3.97/0.98  --qbf_sk_in                             false
% 3.97/0.98  --qbf_pred_elim                         true
% 3.97/0.98  --qbf_split                             512
% 3.97/0.98  
% 3.97/0.98  ------ BMC1 Options
% 3.97/0.98  
% 3.97/0.98  --bmc1_incremental                      false
% 3.97/0.98  --bmc1_axioms                           reachable_all
% 3.97/0.98  --bmc1_min_bound                        0
% 3.97/0.98  --bmc1_max_bound                        -1
% 3.97/0.98  --bmc1_max_bound_default                -1
% 3.97/0.98  --bmc1_symbol_reachability              true
% 3.97/0.98  --bmc1_property_lemmas                  false
% 3.97/0.98  --bmc1_k_induction                      false
% 3.97/0.98  --bmc1_non_equiv_states                 false
% 3.97/0.98  --bmc1_deadlock                         false
% 3.97/0.98  --bmc1_ucm                              false
% 3.97/0.98  --bmc1_add_unsat_core                   none
% 3.97/0.98  --bmc1_unsat_core_children              false
% 3.97/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.97/0.98  --bmc1_out_stat                         full
% 3.97/0.98  --bmc1_ground_init                      false
% 3.97/0.98  --bmc1_pre_inst_next_state              false
% 3.97/0.98  --bmc1_pre_inst_state                   false
% 3.97/0.98  --bmc1_pre_inst_reach_state             false
% 3.97/0.98  --bmc1_out_unsat_core                   false
% 3.97/0.98  --bmc1_aig_witness_out                  false
% 3.97/0.98  --bmc1_verbose                          false
% 3.97/0.98  --bmc1_dump_clauses_tptp                false
% 3.97/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.97/0.98  --bmc1_dump_file                        -
% 3.97/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.97/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.97/0.98  --bmc1_ucm_extend_mode                  1
% 3.97/0.98  --bmc1_ucm_init_mode                    2
% 3.97/0.98  --bmc1_ucm_cone_mode                    none
% 3.97/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.97/0.98  --bmc1_ucm_relax_model                  4
% 3.97/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.97/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.97/0.98  --bmc1_ucm_layered_model                none
% 3.97/0.98  --bmc1_ucm_max_lemma_size               10
% 3.97/0.98  
% 3.97/0.98  ------ AIG Options
% 3.97/0.98  
% 3.97/0.98  --aig_mode                              false
% 3.97/0.98  
% 3.97/0.98  ------ Instantiation Options
% 3.97/0.98  
% 3.97/0.98  --instantiation_flag                    true
% 3.97/0.98  --inst_sos_flag                         false
% 3.97/0.98  --inst_sos_phase                        true
% 3.97/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.97/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.97/0.98  --inst_lit_sel_side                     num_symb
% 3.97/0.98  --inst_solver_per_active                1400
% 3.97/0.98  --inst_solver_calls_frac                1.
% 3.97/0.98  --inst_passive_queue_type               priority_queues
% 3.97/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.97/0.98  --inst_passive_queues_freq              [25;2]
% 3.97/0.98  --inst_dismatching                      true
% 3.97/0.98  --inst_eager_unprocessed_to_passive     true
% 3.97/0.98  --inst_prop_sim_given                   true
% 3.97/0.98  --inst_prop_sim_new                     false
% 3.97/0.98  --inst_subs_new                         false
% 3.97/0.98  --inst_eq_res_simp                      false
% 3.97/0.98  --inst_subs_given                       false
% 3.97/0.98  --inst_orphan_elimination               true
% 3.97/0.98  --inst_learning_loop_flag               true
% 3.97/0.98  --inst_learning_start                   3000
% 3.97/0.98  --inst_learning_factor                  2
% 3.97/0.98  --inst_start_prop_sim_after_learn       3
% 3.97/0.98  --inst_sel_renew                        solver
% 3.97/0.98  --inst_lit_activity_flag                true
% 3.97/0.98  --inst_restr_to_given                   false
% 3.97/0.98  --inst_activity_threshold               500
% 3.97/0.98  --inst_out_proof                        true
% 3.97/0.98  
% 3.97/0.98  ------ Resolution Options
% 3.97/0.98  
% 3.97/0.98  --resolution_flag                       true
% 3.97/0.98  --res_lit_sel                           adaptive
% 3.97/0.98  --res_lit_sel_side                      none
% 3.97/0.98  --res_ordering                          kbo
% 3.97/0.98  --res_to_prop_solver                    active
% 3.97/0.98  --res_prop_simpl_new                    false
% 3.97/0.98  --res_prop_simpl_given                  true
% 3.97/0.98  --res_passive_queue_type                priority_queues
% 3.97/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.97/0.98  --res_passive_queues_freq               [15;5]
% 3.97/0.98  --res_forward_subs                      full
% 3.97/0.98  --res_backward_subs                     full
% 3.97/0.98  --res_forward_subs_resolution           true
% 3.97/0.98  --res_backward_subs_resolution          true
% 3.97/0.98  --res_orphan_elimination                true
% 3.97/0.98  --res_time_limit                        2.
% 3.97/0.98  --res_out_proof                         true
% 3.97/0.98  
% 3.97/0.98  ------ Superposition Options
% 3.97/0.98  
% 3.97/0.98  --superposition_flag                    true
% 3.97/0.98  --sup_passive_queue_type                priority_queues
% 3.97/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.97/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.97/0.98  --demod_completeness_check              fast
% 3.97/0.98  --demod_use_ground                      true
% 3.97/0.98  --sup_to_prop_solver                    passive
% 3.97/0.98  --sup_prop_simpl_new                    true
% 3.97/0.98  --sup_prop_simpl_given                  true
% 3.97/0.98  --sup_fun_splitting                     false
% 3.97/0.98  --sup_smt_interval                      50000
% 3.97/0.98  
% 3.97/0.98  ------ Superposition Simplification Setup
% 3.97/0.98  
% 3.97/0.98  --sup_indices_passive                   []
% 3.97/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.97/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.98  --sup_full_bw                           [BwDemod]
% 3.97/0.98  --sup_immed_triv                        [TrivRules]
% 3.97/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.98  --sup_immed_bw_main                     []
% 3.97/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.97/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.97/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.97/0.98  
% 3.97/0.98  ------ Combination Options
% 3.97/0.98  
% 3.97/0.98  --comb_res_mult                         3
% 3.97/0.98  --comb_sup_mult                         2
% 3.97/0.98  --comb_inst_mult                        10
% 3.97/0.98  
% 3.97/0.98  ------ Debug Options
% 3.97/0.98  
% 3.97/0.98  --dbg_backtrace                         false
% 3.97/0.98  --dbg_dump_prop_clauses                 false
% 3.97/0.98  --dbg_dump_prop_clauses_file            -
% 3.97/0.98  --dbg_out_stat                          false
% 3.97/0.98  ------ Parsing...
% 3.97/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.97/0.98  
% 3.97/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.97/0.98  
% 3.97/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.97/0.98  
% 3.97/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.97/0.98  ------ Proving...
% 3.97/0.98  ------ Problem Properties 
% 3.97/0.98  
% 3.97/0.98  
% 3.97/0.98  clauses                                 14
% 3.97/0.98  conjectures                             2
% 3.97/0.98  EPR                                     1
% 3.97/0.98  Horn                                    14
% 3.97/0.98  unary                                   14
% 3.97/0.98  binary                                  0
% 3.97/0.98  lits                                    14
% 3.97/0.98  lits eq                                 14
% 3.97/0.98  fd_pure                                 0
% 3.97/0.98  fd_pseudo                               0
% 3.97/0.98  fd_cond                                 0
% 3.97/0.98  fd_pseudo_cond                          0
% 3.97/0.98  AC symbols                              1
% 3.97/0.98  
% 3.97/0.98  ------ Schedule UEQ
% 3.97/0.98  
% 3.97/0.98  ------ pure equality problem: resolution off 
% 3.97/0.98  
% 3.97/0.98  ------ Option_UEQ Time Limit: Unbounded
% 3.97/0.98  
% 3.97/0.98  
% 3.97/0.98  ------ 
% 3.97/0.98  Current options:
% 3.97/0.98  ------ 
% 3.97/0.98  
% 3.97/0.98  ------ Input Options
% 3.97/0.98  
% 3.97/0.98  --out_options                           all
% 3.97/0.98  --tptp_safe_out                         true
% 3.97/0.98  --problem_path                          ""
% 3.97/0.98  --include_path                          ""
% 3.97/0.98  --clausifier                            res/vclausify_rel
% 3.97/0.98  --clausifier_options                    --mode clausify
% 3.97/0.98  --stdin                                 false
% 3.97/0.98  --stats_out                             all
% 3.97/0.98  
% 3.97/0.98  ------ General Options
% 3.97/0.98  
% 3.97/0.98  --fof                                   false
% 3.97/0.98  --time_out_real                         305.
% 3.97/0.98  --time_out_virtual                      -1.
% 3.97/0.98  --symbol_type_check                     false
% 3.97/0.98  --clausify_out                          false
% 3.97/0.98  --sig_cnt_out                           false
% 3.97/0.98  --trig_cnt_out                          false
% 3.97/0.98  --trig_cnt_out_tolerance                1.
% 3.97/0.98  --trig_cnt_out_sk_spl                   false
% 3.97/0.98  --abstr_cl_out                          false
% 3.97/0.98  
% 3.97/0.98  ------ Global Options
% 3.97/0.98  
% 3.97/0.98  --schedule                              default
% 3.97/0.98  --add_important_lit                     false
% 3.97/0.98  --prop_solver_per_cl                    1000
% 3.97/0.98  --min_unsat_core                        false
% 3.97/0.98  --soft_assumptions                      false
% 3.97/0.98  --soft_lemma_size                       3
% 3.97/0.98  --prop_impl_unit_size                   0
% 3.97/0.98  --prop_impl_unit                        []
% 3.97/0.98  --share_sel_clauses                     true
% 3.97/0.98  --reset_solvers                         false
% 3.97/0.98  --bc_imp_inh                            [conj_cone]
% 3.97/0.98  --conj_cone_tolerance                   3.
% 3.97/0.98  --extra_neg_conj                        none
% 3.97/0.98  --large_theory_mode                     true
% 3.97/0.98  --prolific_symb_bound                   200
% 3.97/0.98  --lt_threshold                          2000
% 3.97/0.98  --clause_weak_htbl                      true
% 3.97/0.98  --gc_record_bc_elim                     false
% 3.97/0.98  
% 3.97/0.98  ------ Preprocessing Options
% 3.97/0.98  
% 3.97/0.98  --preprocessing_flag                    true
% 3.97/0.98  --time_out_prep_mult                    0.1
% 3.97/0.98  --splitting_mode                        input
% 3.97/0.98  --splitting_grd                         true
% 3.97/0.98  --splitting_cvd                         false
% 3.97/0.98  --splitting_cvd_svl                     false
% 3.97/0.98  --splitting_nvd                         32
% 3.97/0.98  --sub_typing                            true
% 3.97/0.98  --prep_gs_sim                           true
% 3.97/0.98  --prep_unflatten                        true
% 3.97/0.98  --prep_res_sim                          true
% 3.97/0.98  --prep_upred                            true
% 3.97/0.98  --prep_sem_filter                       exhaustive
% 3.97/0.98  --prep_sem_filter_out                   false
% 3.97/0.98  --pred_elim                             true
% 3.97/0.98  --res_sim_input                         true
% 3.97/0.98  --eq_ax_congr_red                       true
% 3.97/0.98  --pure_diseq_elim                       true
% 3.97/0.98  --brand_transform                       false
% 3.97/0.98  --non_eq_to_eq                          false
% 3.97/0.98  --prep_def_merge                        true
% 3.97/0.98  --prep_def_merge_prop_impl              false
% 3.97/0.98  --prep_def_merge_mbd                    true
% 3.97/0.98  --prep_def_merge_tr_red                 false
% 3.97/0.98  --prep_def_merge_tr_cl                  false
% 3.97/0.98  --smt_preprocessing                     true
% 3.97/0.98  --smt_ac_axioms                         fast
% 3.97/0.98  --preprocessed_out                      false
% 3.97/0.98  --preprocessed_stats                    false
% 3.97/0.98  
% 3.97/0.98  ------ Abstraction refinement Options
% 3.97/0.98  
% 3.97/0.98  --abstr_ref                             []
% 3.97/0.98  --abstr_ref_prep                        false
% 3.97/0.98  --abstr_ref_until_sat                   false
% 3.97/0.98  --abstr_ref_sig_restrict                funpre
% 3.97/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.97/0.98  --abstr_ref_under                       []
% 3.97/0.98  
% 3.97/0.98  ------ SAT Options
% 3.97/0.98  
% 3.97/0.98  --sat_mode                              false
% 3.97/0.98  --sat_fm_restart_options                ""
% 3.97/0.98  --sat_gr_def                            false
% 3.97/0.98  --sat_epr_types                         true
% 3.97/0.98  --sat_non_cyclic_types                  false
% 3.97/0.98  --sat_finite_models                     false
% 3.97/0.98  --sat_fm_lemmas                         false
% 3.97/0.98  --sat_fm_prep                           false
% 3.97/0.98  --sat_fm_uc_incr                        true
% 3.97/0.98  --sat_out_model                         small
% 3.97/0.98  --sat_out_clauses                       false
% 3.97/0.98  
% 3.97/0.98  ------ QBF Options
% 3.97/0.98  
% 3.97/0.98  --qbf_mode                              false
% 3.97/0.98  --qbf_elim_univ                         false
% 3.97/0.98  --qbf_dom_inst                          none
% 3.97/0.98  --qbf_dom_pre_inst                      false
% 3.97/0.98  --qbf_sk_in                             false
% 3.97/0.98  --qbf_pred_elim                         true
% 3.97/0.98  --qbf_split                             512
% 3.97/0.98  
% 3.97/0.98  ------ BMC1 Options
% 3.97/0.98  
% 3.97/0.98  --bmc1_incremental                      false
% 3.97/0.98  --bmc1_axioms                           reachable_all
% 3.97/0.98  --bmc1_min_bound                        0
% 3.97/0.98  --bmc1_max_bound                        -1
% 3.97/0.98  --bmc1_max_bound_default                -1
% 3.97/0.98  --bmc1_symbol_reachability              true
% 3.97/0.98  --bmc1_property_lemmas                  false
% 3.97/0.98  --bmc1_k_induction                      false
% 3.97/0.98  --bmc1_non_equiv_states                 false
% 3.97/0.98  --bmc1_deadlock                         false
% 3.97/0.98  --bmc1_ucm                              false
% 3.97/0.98  --bmc1_add_unsat_core                   none
% 3.97/0.98  --bmc1_unsat_core_children              false
% 3.97/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.97/0.98  --bmc1_out_stat                         full
% 3.97/0.98  --bmc1_ground_init                      false
% 3.97/0.98  --bmc1_pre_inst_next_state              false
% 3.97/0.98  --bmc1_pre_inst_state                   false
% 3.97/0.98  --bmc1_pre_inst_reach_state             false
% 3.97/0.98  --bmc1_out_unsat_core                   false
% 3.97/0.98  --bmc1_aig_witness_out                  false
% 3.97/0.98  --bmc1_verbose                          false
% 3.97/0.98  --bmc1_dump_clauses_tptp                false
% 3.97/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.97/0.98  --bmc1_dump_file                        -
% 3.97/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.97/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.97/0.98  --bmc1_ucm_extend_mode                  1
% 3.97/0.98  --bmc1_ucm_init_mode                    2
% 3.97/0.98  --bmc1_ucm_cone_mode                    none
% 3.97/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.97/0.98  --bmc1_ucm_relax_model                  4
% 3.97/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.97/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.97/0.98  --bmc1_ucm_layered_model                none
% 3.97/0.98  --bmc1_ucm_max_lemma_size               10
% 3.97/0.98  
% 3.97/0.98  ------ AIG Options
% 3.97/0.98  
% 3.97/0.98  --aig_mode                              false
% 3.97/0.98  
% 3.97/0.98  ------ Instantiation Options
% 3.97/0.98  
% 3.97/0.98  --instantiation_flag                    false
% 3.97/0.98  --inst_sos_flag                         false
% 3.97/0.98  --inst_sos_phase                        true
% 3.97/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.97/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.97/0.98  --inst_lit_sel_side                     num_symb
% 3.97/0.98  --inst_solver_per_active                1400
% 3.97/0.98  --inst_solver_calls_frac                1.
% 3.97/0.98  --inst_passive_queue_type               priority_queues
% 3.97/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.97/0.98  --inst_passive_queues_freq              [25;2]
% 3.97/0.98  --inst_dismatching                      true
% 3.97/0.98  --inst_eager_unprocessed_to_passive     true
% 3.97/0.98  --inst_prop_sim_given                   true
% 3.97/0.98  --inst_prop_sim_new                     false
% 3.97/0.98  --inst_subs_new                         false
% 3.97/0.98  --inst_eq_res_simp                      false
% 3.97/0.98  --inst_subs_given                       false
% 3.97/0.98  --inst_orphan_elimination               true
% 3.97/0.98  --inst_learning_loop_flag               true
% 3.97/0.98  --inst_learning_start                   3000
% 3.97/0.98  --inst_learning_factor                  2
% 3.97/0.98  --inst_start_prop_sim_after_learn       3
% 3.97/0.98  --inst_sel_renew                        solver
% 3.97/0.98  --inst_lit_activity_flag                true
% 3.97/0.98  --inst_restr_to_given                   false
% 3.97/0.98  --inst_activity_threshold               500
% 3.97/0.98  --inst_out_proof                        true
% 3.97/0.98  
% 3.97/0.98  ------ Resolution Options
% 3.97/0.98  
% 3.97/0.98  --resolution_flag                       false
% 3.97/0.98  --res_lit_sel                           adaptive
% 3.97/0.98  --res_lit_sel_side                      none
% 3.97/0.98  --res_ordering                          kbo
% 3.97/0.99  --res_to_prop_solver                    active
% 3.97/0.99  --res_prop_simpl_new                    false
% 3.97/0.99  --res_prop_simpl_given                  true
% 3.97/0.99  --res_passive_queue_type                priority_queues
% 3.97/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.97/0.99  --res_passive_queues_freq               [15;5]
% 3.97/0.99  --res_forward_subs                      full
% 3.97/0.99  --res_backward_subs                     full
% 3.97/0.99  --res_forward_subs_resolution           true
% 3.97/0.99  --res_backward_subs_resolution          true
% 3.97/0.99  --res_orphan_elimination                true
% 3.97/0.99  --res_time_limit                        2.
% 3.97/0.99  --res_out_proof                         true
% 3.97/0.99  
% 3.97/0.99  ------ Superposition Options
% 3.97/0.99  
% 3.97/0.99  --superposition_flag                    true
% 3.97/0.99  --sup_passive_queue_type                priority_queues
% 3.97/0.99  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.97/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.97/0.99  --demod_completeness_check              fast
% 3.97/0.99  --demod_use_ground                      true
% 3.97/0.99  --sup_to_prop_solver                    active
% 3.97/0.99  --sup_prop_simpl_new                    false
% 3.97/0.99  --sup_prop_simpl_given                  false
% 3.97/0.99  --sup_fun_splitting                     true
% 3.97/0.99  --sup_smt_interval                      10000
% 3.97/0.99  
% 3.97/0.99  ------ Superposition Simplification Setup
% 3.97/0.99  
% 3.97/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.97/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.97/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.97/0.99  --sup_full_triv                         [TrivRules]
% 3.97/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.97/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.97/0.99  --sup_immed_triv                        [TrivRules]
% 3.97/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/0.99  --sup_immed_bw_main                     []
% 3.97/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.97/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.97/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.97/0.99  --sup_input_bw                          [BwDemod;BwSubsumption]
% 3.97/0.99  
% 3.97/0.99  ------ Combination Options
% 3.97/0.99  
% 3.97/0.99  --comb_res_mult                         1
% 3.97/0.99  --comb_sup_mult                         1
% 3.97/0.99  --comb_inst_mult                        1000000
% 3.97/0.99  
% 3.97/0.99  ------ Debug Options
% 3.97/0.99  
% 3.97/0.99  --dbg_backtrace                         false
% 3.97/0.99  --dbg_dump_prop_clauses                 false
% 3.97/0.99  --dbg_dump_prop_clauses_file            -
% 3.97/0.99  --dbg_out_stat                          false
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  ------ Proving...
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  % SZS status Theorem for theBenchmark.p
% 3.97/0.99  
% 3.97/0.99   Resolution empty clause
% 3.97/0.99  
% 3.97/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.97/0.99  
% 3.97/0.99  fof(f2,axiom,(
% 3.97/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f15,plain,(
% 3.97/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.97/0.99    inference(unused_predicate_definition_removal,[],[f2])).
% 3.97/0.99  
% 3.97/0.99  fof(f16,plain,(
% 3.97/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 3.97/0.99    inference(ennf_transformation,[],[f15])).
% 3.97/0.99  
% 3.97/0.99  fof(f22,plain,(
% 3.97/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f16])).
% 3.97/0.99  
% 3.97/0.99  fof(f9,axiom,(
% 3.97/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f29,plain,(
% 3.97/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.97/0.99    inference(cnf_transformation,[],[f9])).
% 3.97/0.99  
% 3.97/0.99  fof(f37,plain,(
% 3.97/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.97/0.99    inference(definition_unfolding,[],[f22,f29])).
% 3.97/0.99  
% 3.97/0.99  fof(f13,conjecture,(
% 3.97/0.99    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f14,negated_conjecture,(
% 3.97/0.99    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.97/0.99    inference(negated_conjecture,[],[f13])).
% 3.97/0.99  
% 3.97/0.99  fof(f17,plain,(
% 3.97/0.99    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 3.97/0.99    inference(ennf_transformation,[],[f14])).
% 3.97/0.99  
% 3.97/0.99  fof(f18,plain,(
% 3.97/0.99    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 3.97/0.99    inference(flattening,[],[f17])).
% 3.97/0.99  
% 3.97/0.99  fof(f19,plain,(
% 3.97/0.99    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 3.97/0.99    introduced(choice_axiom,[])).
% 3.97/0.99  
% 3.97/0.99  fof(f20,plain,(
% 3.97/0.99    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 3.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f19])).
% 3.97/0.99  
% 3.97/0.99  fof(f35,plain,(
% 3.97/0.99    r1_xboole_0(sK3,sK1)),
% 3.97/0.99    inference(cnf_transformation,[],[f20])).
% 3.97/0.99  
% 3.97/0.99  fof(f10,axiom,(
% 3.97/0.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f30,plain,(
% 3.97/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f10])).
% 3.97/0.99  
% 3.97/0.99  fof(f39,plain,(
% 3.97/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 3.97/0.99    inference(definition_unfolding,[],[f30,f29,f29])).
% 3.97/0.99  
% 3.97/0.99  fof(f8,axiom,(
% 3.97/0.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f28,plain,(
% 3.97/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f8])).
% 3.97/0.99  
% 3.97/0.99  fof(f6,axiom,(
% 3.97/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f26,plain,(
% 3.97/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.97/0.99    inference(cnf_transformation,[],[f6])).
% 3.97/0.99  
% 3.97/0.99  fof(f4,axiom,(
% 3.97/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f24,plain,(
% 3.97/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.97/0.99    inference(cnf_transformation,[],[f4])).
% 3.97/0.99  
% 3.97/0.99  fof(f38,plain,(
% 3.97/0.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.97/0.99    inference(definition_unfolding,[],[f24,f29])).
% 3.97/0.99  
% 3.97/0.99  fof(f3,axiom,(
% 3.97/0.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f23,plain,(
% 3.97/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.97/0.99    inference(cnf_transformation,[],[f3])).
% 3.97/0.99  
% 3.97/0.99  fof(f1,axiom,(
% 3.97/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f21,plain,(
% 3.97/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f1])).
% 3.97/0.99  
% 3.97/0.99  fof(f12,axiom,(
% 3.97/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f32,plain,(
% 3.97/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.97/0.99    inference(cnf_transformation,[],[f12])).
% 3.97/0.99  
% 3.97/0.99  fof(f7,axiom,(
% 3.97/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f27,plain,(
% 3.97/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f7])).
% 3.97/0.99  
% 3.97/0.99  fof(f5,axiom,(
% 3.97/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f25,plain,(
% 3.97/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.97/0.99    inference(cnf_transformation,[],[f5])).
% 3.97/0.99  
% 3.97/0.99  fof(f33,plain,(
% 3.97/0.99    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 3.97/0.99    inference(cnf_transformation,[],[f20])).
% 3.97/0.99  
% 3.97/0.99  fof(f11,axiom,(
% 3.97/0.99    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 3.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.97/0.99  
% 3.97/0.99  fof(f31,plain,(
% 3.97/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 3.97/0.99    inference(cnf_transformation,[],[f11])).
% 3.97/0.99  
% 3.97/0.99  fof(f34,plain,(
% 3.97/0.99    r1_xboole_0(sK2,sK0)),
% 3.97/0.99    inference(cnf_transformation,[],[f20])).
% 3.97/0.99  
% 3.97/0.99  fof(f36,plain,(
% 3.97/0.99    sK1 != sK2),
% 3.97/0.99    inference(cnf_transformation,[],[f20])).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1,plain,
% 3.97/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.97/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.97/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_12,negated_conjecture,
% 3.97/0.99      ( r1_xboole_0(sK3,sK1) ),
% 3.97/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_56,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.97/0.99      | sK3 != X0
% 3.97/0.99      | sK1 != X1 ),
% 3.97/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_12]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_57,plain,
% 3.97/0.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k1_xboole_0 ),
% 3.97/0.99      inference(unflattening,[status(thm)],[c_56]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_8,plain,
% 3.97/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 3.97/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_7,plain,
% 3.97/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.97/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_80,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_8,c_7]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_90,plain,
% 3.97/0.99      ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK3),sK1)) = k4_xboole_0(sK3,k1_xboole_0) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_57,c_80]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_5,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.97/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_3,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.97/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_79,plain,
% 3.97/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_3,c_5]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2,plain,
% 3.97/0.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.97/0.99      inference(cnf_transformation,[],[f23]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_0,plain,
% 3.97/0.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.97/0.99      inference(cnf_transformation,[],[f21]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_84,plain,
% 3.97/0.99      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_110,plain,
% 3.97/0.99      ( k4_xboole_0(sK3,sK1) = sK3 ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_90,c_5,c_79,c_84]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_99,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_80,c_80]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_100,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))) ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_99,c_79]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_101,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_100,c_84]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1589,plain,
% 3.97/0.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK3,X0))) = k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_110,c_101]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_149,plain,
% 3.97/0.99      ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_57,c_7]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_151,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_79,c_7]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_10,plain,
% 3.97/0.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 3.97/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 3.97/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_138,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_10,c_6]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_139,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_138,c_79]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_165,plain,
% 3.97/0.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_151,c_139]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_168,plain,
% 3.97/0.99      ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) = k1_xboole_0 ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_149,c_165]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_169,plain,
% 3.97/0.99      ( k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) = k1_xboole_0 ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_168,c_110]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1640,plain,
% 3.97/0.99      ( k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK3,k1_xboole_0) ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_1589,c_169]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1641,plain,
% 3.97/0.99      ( k4_xboole_0(sK3,k4_xboole_0(sK1,X0)) = sK3 ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_1640,c_5]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_4,plain,
% 3.97/0.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.97/0.99      inference(cnf_transformation,[],[f25]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_115,plain,
% 3.97/0.99      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_79,c_4]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_116,plain,
% 3.97/0.99      ( k2_xboole_0(X0,X0) = X0 ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_115,c_2]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_14,negated_conjecture,
% 3.97/0.99      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 3.97/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_9,plain,
% 3.97/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.97/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_72,negated_conjecture,
% 3.97/0.99      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 3.97/0.99      inference(theory_normalisation,[status(thm)],[c_14,c_9,c_0]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_270,plain,
% 3.97/0.99      ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),X0) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_72,c_9]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_400,plain,
% 3.97/0.99      ( k2_xboole_0(sK1,k2_xboole_0(sK0,X0)) = k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_270,c_9]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_871,plain,
% 3.97/0.99      ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK2,sK3) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_116,c_400]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_898,plain,
% 3.97/0.99      ( k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK1,sK0) ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_871,c_72]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_124,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_4,c_6]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_158,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_7,c_79]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_159,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_158,c_4]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1566,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_159,c_101]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1659,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_1566,c_5]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6340,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_124,c_124,c_1659]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6395,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(k2_xboole_0(sK0,sK3),sK1)) = sK1 ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_898,c_6340]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_125,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK0),sK3) = k4_xboole_0(sK2,sK3) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_72,c_6]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6421,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)),k4_xboole_0(sK2,sK3)) = sK3 ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_125,c_6340]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_81,plain,
% 3.97/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_250,plain,
% 3.97/0.99      ( k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_72,c_81]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_174,plain,
% 3.97/0.99      ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_125,c_4]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_177,plain,
% 3.97/0.99      ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK3,sK2) ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_174,c_4]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_352,plain,
% 3.97/0.99      ( k2_xboole_0(sK2,k2_xboole_0(sK3,sK3)) = k2_xboole_0(sK3,sK2) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_250,c_177]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_113,plain,
% 3.97/0.99      ( k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_57,c_4]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_119,plain,
% 3.97/0.99      ( k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK3,sK3) ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_113,c_110]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_120,plain,
% 3.97/0.99      ( k2_xboole_0(sK3,sK3) = sK3 ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_119,c_2]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_353,plain,
% 3.97/0.99      ( k2_xboole_0(sK3,sK2) = k2_xboole_0(sK1,sK0) ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_352,c_72,c_120]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_366,plain,
% 3.97/0.99      ( k2_xboole_0(sK3,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_353,c_177]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6522,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK2,sK3)) = sK3 ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_6421,c_366]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_909,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK3)) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_898,c_6]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_127,plain,
% 3.97/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_6,c_4]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_131,plain,
% 3.97/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_127,c_4]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1163,plain,
% 3.97/0.99      ( k2_xboole_0(sK2,k2_xboole_0(sK0,sK3)) = k2_xboole_0(sK0,sK1) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_131,c_250]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1335,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK3)) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK3)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_1163,c_6]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_13,negated_conjecture,
% 3.97/0.99      ( r1_xboole_0(sK2,sK0) ),
% 3.97/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_61,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.97/0.99      | sK0 != X1
% 3.97/0.99      | sK2 != X0 ),
% 3.97/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_13]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_62,plain,
% 3.97/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 3.97/0.99      inference(unflattening,[status(thm)],[c_61]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_91,plain,
% 3.97/0.99      ( k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK2),sK0)) = k4_xboole_0(sK2,k1_xboole_0) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_62,c_80]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_108,plain,
% 3.97/0.99      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_91,c_5,c_79,c_84]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_182,plain,
% 3.97/0.99      ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_108,c_7]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_122,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_0,c_6]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_662,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k4_xboole_0(X1,X0),X2) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_122,c_7]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_670,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_662,c_7]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1348,plain,
% 3.97/0.99      ( k4_xboole_0(sK1,k2_xboole_0(sK0,sK3)) = k4_xboole_0(sK2,sK3) ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_1335,c_182,c_670]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2065,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK3)) = k4_xboole_0(sK2,sK3) ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_909,c_909,c_1348]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6438,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)),k4_xboole_0(sK2,sK3)) = k2_xboole_0(sK0,sK3) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_2065,c_6340]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_913,plain,
% 3.97/0.99      ( k2_xboole_0(sK1,k2_xboole_0(X0,k2_xboole_0(sK0,sK3))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_898,c_81]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2795,plain,
% 3.97/0.99      ( k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_116,c_913]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_2838,plain,
% 3.97/0.99      ( k2_xboole_0(k2_xboole_0(sK0,sK3),k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_2795,c_898]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6506,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK2,sK3)) = k2_xboole_0(sK0,sK3) ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_6438,c_2838]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6523,plain,
% 3.97/0.99      ( k2_xboole_0(sK0,sK3) = sK3 ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_6522,c_6506]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6546,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK0),k4_xboole_0(sK3,sK1)) = sK1 ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_6395,c_6523]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6547,plain,
% 3.97/0.99      ( k4_xboole_0(sK2,sK3) = sK1 ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_6546,c_110,c_125]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6929,plain,
% 3.97/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK1,X0))) = k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_6547,c_101]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_82,plain,
% 3.97/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_522,plain,
% 3.97/0.99      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_72,c_82]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_704,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),sK3) = k4_xboole_0(k2_xboole_0(sK2,X0),sK3) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_522,c_122]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_97,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_79,c_80]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_103,plain,
% 3.97/0.99      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_97,c_5,c_79]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1929,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK2,X0),sK3),sK3)) = k1_xboole_0 ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_704,c_103]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_519,plain,
% 3.97/0.99      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_2,c_82]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1748,plain,
% 3.97/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_4,c_519]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1858,plain,
% 3.97/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_1748,c_519]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1939,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(k2_xboole_0(sK2,X0),sK3)) = k1_xboole_0 ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_1929,c_1858]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_137,plain,
% 3.97/0.99      ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK2,sK3) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_72,c_10]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_140,plain,
% 3.97/0.99      ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k2_xboole_0(sK1,sK0) ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_137,c_72]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_251,plain,
% 3.97/0.99      ( k2_xboole_0(sK2,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_140,c_81]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1454,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(sK2,k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_251,c_6]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1200,plain,
% 3.97/0.99      ( k4_xboole_0(sK2,k2_xboole_0(X0,k2_xboole_0(X1,sK0))) = k4_xboole_0(sK2,k2_xboole_0(X1,X0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_82,c_182]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1477,plain,
% 3.97/0.99      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(sK1,sK0)),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_1454,c_670,c_1200]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_526,plain,
% 3.97/0.99      ( k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_140,c_82]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1507,plain,
% 3.97/0.99      ( k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK2,X0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_10,c_526]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1525,plain,
% 3.97/0.99      ( k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(sK1,sK0)) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_526,c_131]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1135,plain,
% 3.97/0.99      ( k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k2_xboole_0(k2_xboole_0(sK2,X0),sK3) ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_522,c_131]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1541,plain,
% 3.97/0.99      ( k2_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(sK1,sK0)) = k2_xboole_0(k2_xboole_0(sK2,X0),sK3) ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_1525,c_1135]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1558,plain,
% 3.97/0.99      ( k2_xboole_0(k2_xboole_0(sK2,X0),sK3) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_1507,c_526,c_1541]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_1940,plain,
% 3.97/0.99      ( k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k1_xboole_0 ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_1939,c_1477,c_1558]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6941,plain,
% 3.97/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k1_xboole_0) ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_6929,c_1940]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_6942,plain,
% 3.97/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK3,X0)) = sK2 ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_6941,c_5]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_8170,plain,
% 3.97/0.99      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 3.97/0.99      inference(superposition,[status(thm)],[c_1641,c_6942]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_8204,plain,
% 3.97/0.99      ( sK2 = sK1 ),
% 3.97/0.99      inference(light_normalisation,[status(thm)],[c_8170,c_6547]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_11,negated_conjecture,
% 3.97/0.99      ( sK1 != sK2 ),
% 3.97/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_9629,plain,
% 3.97/0.99      ( sK1 != sK1 ),
% 3.97/0.99      inference(demodulation,[status(thm)],[c_8204,c_11]) ).
% 3.97/0.99  
% 3.97/0.99  cnf(c_9630,plain,
% 3.97/0.99      ( $false ),
% 3.97/0.99      inference(equality_resolution_simp,[status(thm)],[c_9629]) ).
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.97/0.99  
% 3.97/0.99  ------                               Statistics
% 3.97/0.99  
% 3.97/0.99  ------ General
% 3.97/0.99  
% 3.97/0.99  abstr_ref_over_cycles:                  0
% 3.97/0.99  abstr_ref_under_cycles:                 0
% 3.97/0.99  gc_basic_clause_elim:                   0
% 3.97/0.99  forced_gc_time:                         0
% 3.97/0.99  parsing_time:                           0.009
% 3.97/0.99  unif_index_cands_time:                  0.
% 3.97/0.99  unif_index_add_time:                    0.
% 3.97/0.99  orderings_time:                         0.
% 3.97/0.99  out_proof_time:                         0.008
% 3.97/0.99  total_time:                             0.441
% 3.97/0.99  num_of_symbols:                         39
% 3.97/0.99  num_of_terms:                           19956
% 3.97/0.99  
% 3.97/0.99  ------ Preprocessing
% 3.97/0.99  
% 3.97/0.99  num_of_splits:                          0
% 3.97/0.99  num_of_split_atoms:                     0
% 3.97/0.99  num_of_reused_defs:                     0
% 3.97/0.99  num_eq_ax_congr_red:                    0
% 3.97/0.99  num_of_sem_filtered_clauses:            0
% 3.97/0.99  num_of_subtypes:                        0
% 3.97/0.99  monotx_restored_types:                  0
% 3.97/0.99  sat_num_of_epr_types:                   0
% 3.97/0.99  sat_num_of_non_cyclic_types:            0
% 3.97/0.99  sat_guarded_non_collapsed_types:        0
% 3.97/0.99  num_pure_diseq_elim:                    0
% 3.97/0.99  simp_replaced_by:                       0
% 3.97/0.99  res_preprocessed:                       47
% 3.97/0.99  prep_upred:                             0
% 3.97/0.99  prep_unflattend:                        4
% 3.97/0.99  smt_new_axioms:                         0
% 3.97/0.99  pred_elim_cands:                        0
% 3.97/0.99  pred_elim:                              1
% 3.97/0.99  pred_elim_cl:                           1
% 3.97/0.99  pred_elim_cycles:                       2
% 3.97/0.99  merged_defs:                            0
% 3.97/0.99  merged_defs_ncl:                        0
% 3.97/0.99  bin_hyper_res:                          0
% 3.97/0.99  prep_cycles:                            3
% 3.97/0.99  pred_elim_time:                         0.
% 3.97/0.99  splitting_time:                         0.
% 3.97/0.99  sem_filter_time:                        0.
% 3.97/0.99  monotx_time:                            0.
% 3.97/0.99  subtype_inf_time:                       0.
% 3.97/0.99  
% 3.97/0.99  ------ Problem properties
% 3.97/0.99  
% 3.97/0.99  clauses:                                14
% 3.97/0.99  conjectures:                            2
% 3.97/0.99  epr:                                    1
% 3.97/0.99  horn:                                   14
% 3.97/0.99  ground:                                 4
% 3.97/0.99  unary:                                  14
% 3.97/0.99  binary:                                 0
% 3.97/0.99  lits:                                   14
% 3.97/0.99  lits_eq:                                14
% 3.97/0.99  fd_pure:                                0
% 3.97/0.99  fd_pseudo:                              0
% 3.97/0.99  fd_cond:                                0
% 3.97/0.99  fd_pseudo_cond:                         0
% 3.97/0.99  ac_symbols:                             1
% 3.97/0.99  
% 3.97/0.99  ------ Propositional Solver
% 3.97/0.99  
% 3.97/0.99  prop_solver_calls:                      17
% 3.97/0.99  prop_fast_solver_calls:                 110
% 3.97/0.99  smt_solver_calls:                       0
% 3.97/0.99  smt_fast_solver_calls:                  0
% 3.97/0.99  prop_num_of_clauses:                    226
% 3.97/0.99  prop_preprocess_simplified:             613
% 3.97/0.99  prop_fo_subsumed:                       0
% 3.97/0.99  prop_solver_time:                       0.
% 3.97/0.99  smt_solver_time:                        0.
% 3.97/0.99  smt_fast_solver_time:                   0.
% 3.97/0.99  prop_fast_solver_time:                  0.
% 3.97/0.99  prop_unsat_core_time:                   0.
% 3.97/0.99  
% 3.97/0.99  ------ QBF
% 3.97/0.99  
% 3.97/0.99  qbf_q_res:                              0
% 3.97/0.99  qbf_num_tautologies:                    0
% 3.97/0.99  qbf_prep_cycles:                        0
% 3.97/0.99  
% 3.97/0.99  ------ BMC1
% 3.97/0.99  
% 3.97/0.99  bmc1_current_bound:                     -1
% 3.97/0.99  bmc1_last_solved_bound:                 -1
% 3.97/0.99  bmc1_unsat_core_size:                   -1
% 3.97/0.99  bmc1_unsat_core_parents_size:           -1
% 3.97/0.99  bmc1_merge_next_fun:                    0
% 3.97/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.97/0.99  
% 3.97/0.99  ------ Instantiation
% 3.97/0.99  
% 3.97/0.99  inst_num_of_clauses:                    0
% 3.97/0.99  inst_num_in_passive:                    0
% 3.97/0.99  inst_num_in_active:                     0
% 3.97/0.99  inst_num_in_unprocessed:                0
% 3.97/0.99  inst_num_of_loops:                      0
% 3.97/0.99  inst_num_of_learning_restarts:          0
% 3.97/0.99  inst_num_moves_active_passive:          0
% 3.97/0.99  inst_lit_activity:                      0
% 3.97/0.99  inst_lit_activity_moves:                0
% 3.97/0.99  inst_num_tautologies:                   0
% 3.97/0.99  inst_num_prop_implied:                  0
% 3.97/0.99  inst_num_existing_simplified:           0
% 3.97/0.99  inst_num_eq_res_simplified:             0
% 3.97/0.99  inst_num_child_elim:                    0
% 3.97/0.99  inst_num_of_dismatching_blockings:      0
% 3.97/0.99  inst_num_of_non_proper_insts:           0
% 3.97/0.99  inst_num_of_duplicates:                 0
% 3.97/0.99  inst_inst_num_from_inst_to_res:         0
% 3.97/0.99  inst_dismatching_checking_time:         0.
% 3.97/0.99  
% 3.97/0.99  ------ Resolution
% 3.97/0.99  
% 3.97/0.99  res_num_of_clauses:                     0
% 3.97/0.99  res_num_in_passive:                     0
% 3.97/0.99  res_num_in_active:                      0
% 3.97/0.99  res_num_of_loops:                       50
% 3.97/0.99  res_forward_subset_subsumed:            0
% 3.97/0.99  res_backward_subset_subsumed:           0
% 3.97/0.99  res_forward_subsumed:                   0
% 3.97/0.99  res_backward_subsumed:                  0
% 3.97/0.99  res_forward_subsumption_resolution:     0
% 3.97/0.99  res_backward_subsumption_resolution:    0
% 3.97/0.99  res_clause_to_clause_subsumption:       21019
% 3.97/0.99  res_orphan_elimination:                 0
% 3.97/0.99  res_tautology_del:                      0
% 3.97/0.99  res_num_eq_res_simplified:              0
% 3.97/0.99  res_num_sel_changes:                    0
% 3.97/0.99  res_moves_from_active_to_pass:          0
% 3.97/0.99  
% 3.97/0.99  ------ Superposition
% 3.97/0.99  
% 3.97/0.99  sup_time_total:                         0.
% 3.97/0.99  sup_time_generating:                    0.
% 3.97/0.99  sup_time_sim_full:                      0.
% 3.97/0.99  sup_time_sim_immed:                     0.
% 3.97/0.99  
% 3.97/0.99  sup_num_of_clauses:                     1941
% 3.97/0.99  sup_num_in_active:                      50
% 3.97/0.99  sup_num_in_passive:                     1891
% 3.97/0.99  sup_num_of_loops:                       134
% 3.97/0.99  sup_fw_superposition:                   3300
% 3.97/0.99  sup_bw_superposition:                   2287
% 3.97/0.99  sup_immediate_simplified:               3424
% 3.97/0.99  sup_given_eliminated:                   5
% 3.97/0.99  comparisons_done:                       0
% 3.97/0.99  comparisons_avoided:                    0
% 3.97/0.99  
% 3.97/0.99  ------ Simplifications
% 3.97/0.99  
% 3.97/0.99  
% 3.97/0.99  sim_fw_subset_subsumed:                 0
% 3.97/0.99  sim_bw_subset_subsumed:                 0
% 3.97/0.99  sim_fw_subsumed:                        286
% 3.97/0.99  sim_bw_subsumed:                        42
% 3.97/0.99  sim_fw_subsumption_res:                 0
% 3.97/0.99  sim_bw_subsumption_res:                 0
% 3.97/0.99  sim_tautology_del:                      0
% 3.97/0.99  sim_eq_tautology_del:                   689
% 3.97/0.99  sim_eq_res_simp:                        0
% 3.97/0.99  sim_fw_demodulated:                     2042
% 3.97/0.99  sim_bw_demodulated:                     175
% 3.97/0.99  sim_light_normalised:                   1671
% 3.97/0.99  sim_joinable_taut:                      218
% 3.97/0.99  sim_joinable_simp:                      0
% 3.97/0.99  sim_ac_normalised:                      0
% 3.97/0.99  sim_smt_subsumption:                    0
% 3.97/0.99  
%------------------------------------------------------------------------------
