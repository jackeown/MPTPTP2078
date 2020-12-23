%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:48 EST 2020

% Result     : Theorem 51.47s
% Output     : CNFRefutation 51.47s
% Verified   : 
% Statistics : Number of formulae       :  168 (2204 expanded)
%              Number of clauses        :  122 ( 883 expanded)
%              Number of leaves         :   18 ( 495 expanded)
%              Depth                    :   35
%              Number of atoms          :  253 (3625 expanded)
%              Number of equality atoms :  218 (3011 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f25])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK3,sK5)
        | ~ r1_tarski(sK2,sK4) )
      & k1_xboole_0 != k2_zfmisc_1(sK2,sK3)
      & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( ~ r1_tarski(sK3,sK5)
      | ~ r1_tarski(sK2,sK4) )
    & k1_xboole_0 != k2_zfmisc_1(sK2,sK3)
    & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f34])).

fof(f58,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
      & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f57,f44,f44])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f56,f44,f44])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,
    ( ~ r1_tarski(sK3,sK5)
    | ~ r1_tarski(sK2,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_515,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_517,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_713,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = k2_zfmisc_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_515,c_517])).

cnf(c_18,plain,
    ( k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_19,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1215,plain,
    ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_4,c_18])).

cnf(c_1339,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_19,c_19,c_1215])).

cnf(c_1345,plain,
    ( k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X0,X1),X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(superposition,[status(thm)],[c_18,c_1339])).

cnf(c_106649,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK2,sK4),k5_xboole_0(sK3,k3_xboole_0(sK3,sK5))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK2,sK4),sK3),k2_zfmisc_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_713,c_1345])).

cnf(c_20,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1226,plain,
    ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k3_xboole_0(X0,X2),X1) ),
    inference(superposition,[status(thm)],[c_4,c_18])).

cnf(c_1381,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k3_xboole_0(X0,X2),X1)) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1) ),
    inference(light_normalisation,[status(thm)],[c_20,c_20,c_1226])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_13,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_538,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_13,c_1])).

cnf(c_6969,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_12,c_538])).

cnf(c_7013,plain,
    ( k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X0,X1),X2),k2_zfmisc_1(X0,X2)) = k5_xboole_0(k1_xboole_0,k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_1381,c_6969])).

cnf(c_757,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_12,c_1])).

cnf(c_7045,plain,
    ( k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X0,X1),X2),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_7013,c_757])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_533,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_3919,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(X0,k2_zfmisc_1(sK4,sK5))) = k3_xboole_0(X0,k2_zfmisc_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_713,c_533])).

cnf(c_823,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK4,sK5),X0)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),X0) ),
    inference(superposition,[status(thm)],[c_713,c_8])).

cnf(c_858,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(X0,k2_zfmisc_1(sK4,sK5))) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),X0) ),
    inference(superposition,[status(thm)],[c_0,c_823])).

cnf(c_865,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(X0,k3_xboole_0(X1,k2_zfmisc_1(sK4,sK5)))) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_8,c_858])).

cnf(c_916,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k3_xboole_0(X0,k2_zfmisc_1(sK4,sK5)),X0)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(X0,k2_zfmisc_1(sK4,sK5))) ),
    inference(superposition,[status(thm)],[c_4,c_865])).

cnf(c_924,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k3_xboole_0(X0,k2_zfmisc_1(sK4,sK5)),X0)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),X0) ),
    inference(light_normalisation,[status(thm)],[c_916,c_858])).

cnf(c_4387,plain,
    ( k3_xboole_0(k3_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5)),k2_zfmisc_1(sK2,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_3919,c_924])).

cnf(c_4388,plain,
    ( k3_xboole_0(k3_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5)),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_4387,c_713])).

cnf(c_1227,plain,
    ( k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X3,X4))) = k3_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(X2,X3)),k2_zfmisc_1(X1,X4)) ),
    inference(superposition,[status(thm)],[c_8,c_18])).

cnf(c_1242,plain,
    ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k3_xboole_0(X3,X4))) = k3_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(X1,X3)),k2_zfmisc_1(X2,X4)) ),
    inference(demodulation,[status(thm)],[c_1227,c_18])).

cnf(c_3918,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4,c_533])).

cnf(c_4082,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_3918])).

cnf(c_4243,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),X0)) = k3_xboole_0(k3_xboole_0(k2_zfmisc_1(sK4,sK5),X0),k2_zfmisc_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_823,c_4082])).

cnf(c_4333,plain,
    ( k3_xboole_0(k3_xboole_0(k2_zfmisc_1(sK4,sK5),X0),k2_zfmisc_1(sK2,sK3)) = k3_xboole_0(X0,k2_zfmisc_1(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_4243,c_4082])).

cnf(c_4389,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK2,k3_xboole_0(sK5,sK3))) = k2_zfmisc_1(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_4388,c_1215,c_1242,c_4333])).

cnf(c_762,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_8])).

cnf(c_2150,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_762])).

cnf(c_4582,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK2,k3_xboole_0(sK5,sK3)),k2_zfmisc_1(sK2,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,k3_xboole_0(sK5,sK3)),k2_zfmisc_1(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_4389,c_2150])).

cnf(c_2997,plain,
    ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k3_xboole_0(X3,X1))) = k2_zfmisc_1(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ),
    inference(superposition,[status(thm)],[c_2150,c_18])).

cnf(c_1224,plain,
    ( k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_18])).

cnf(c_3017,plain,
    ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k3_xboole_0(X3,X1))) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X2,X1)) ),
    inference(demodulation,[status(thm)],[c_2997,c_1224])).

cnf(c_4598,plain,
    ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = k2_zfmisc_1(sK2,k3_xboole_0(sK5,sK3)) ),
    inference(demodulation,[status(thm)],[c_4582,c_4,c_1215,c_1242,c_3017])).

cnf(c_4599,plain,
    ( k2_zfmisc_1(sK2,k3_xboole_0(sK5,sK3)) = k2_zfmisc_1(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_4598,c_713])).

cnf(c_4607,plain,
    ( k2_zfmisc_1(sK2,k3_xboole_0(sK3,sK5)) = k2_zfmisc_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_0,c_4599])).

cnf(c_4670,plain,
    ( k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK5))) = k5_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_4607,c_1339])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4671,plain,
    ( k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK5))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4670,c_14])).

cnf(c_30100,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK2,X0),k5_xboole_0(sK3,k3_xboole_0(sK3,sK5))) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,k5_xboole_0(sK3,k3_xboole_0(sK3,sK5)))) ),
    inference(superposition,[status(thm)],[c_4671,c_1226])).

cnf(c_15,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_17135,plain,
    ( k2_zfmisc_1(X0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_15,c_1215])).

cnf(c_18751,plain,
    ( k2_zfmisc_1(X0,k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_17135])).

cnf(c_18931,plain,
    ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k3_xboole_0(X0,X2),X1)) ),
    inference(superposition,[status(thm)],[c_18751,c_18])).

cnf(c_18770,plain,
    ( k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X1,X2)) ),
    inference(superposition,[status(thm)],[c_17135,c_18])).

cnf(c_18859,plain,
    ( k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_18770,c_15])).

cnf(c_19010,plain,
    ( k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X1),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_18931,c_15,c_18859])).

cnf(c_19011,plain,
    ( k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1)) = sP0_iProver_split(X1) ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_19010])).

cnf(c_19190,plain,
    ( k3_xboole_0(k2_zfmisc_1(X0,X1),k1_xboole_0) = sP0_iProver_split(X1) ),
    inference(demodulation,[status(thm)],[c_18931,c_15,c_18859,c_19011])).

cnf(c_18957,plain,
    ( k5_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(X1,k1_xboole_0)),k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k3_xboole_0(X0,X2),X1))) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_18751,c_1381])).

cnf(c_19015,plain,
    ( k2_zfmisc_1(X0,k3_xboole_0(X1,k1_xboole_0)) = sP0_iProver_split(X1) ),
    inference(demodulation,[status(thm)],[c_19011,c_18751])).

cnf(c_19135,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k3_xboole_0(X1,X2),X0))) = k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_18957,c_19015])).

cnf(c_19136,plain,
    ( k5_xboole_0(sP0_iProver_split(X0),k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X1,X0))) = sP0_iProver_split(X0) ),
    inference(demodulation,[status(thm)],[c_19135,c_18859,c_19015])).

cnf(c_19137,plain,
    ( sP0_iProver_split(X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19136,c_14,c_19011])).

cnf(c_21080,plain,
    ( k3_xboole_0(k2_zfmisc_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19190,c_19137])).

cnf(c_21120,plain,
    ( k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_21080,c_0])).

cnf(c_30378,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK2,X0),k5_xboole_0(sK3,k3_xboole_0(sK3,sK5))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_30100,c_21120])).

cnf(c_106892,plain,
    ( k2_zfmisc_1(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_106649,c_7045,c_30378])).

cnf(c_17,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_109662,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_106892,c_17])).

cnf(c_537,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_13,c_1])).

cnf(c_5533,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14,c_537])).

cnf(c_5550,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_5533,c_12])).

cnf(c_6892,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_5550,c_13])).

cnf(c_11688,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X0,X2)) = X1 ),
    inference(superposition,[status(thm)],[c_6892,c_5550])).

cnf(c_11707,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X2)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_11688,c_13])).

cnf(c_13491,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(k5_xboole_0(X0,X1),X3)) = X2 ),
    inference(superposition,[status(thm)],[c_13,c_11707])).

cnf(c_111472,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(sK2,sK4))) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_109662,c_13491])).

cnf(c_13504,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
    inference(superposition,[status(thm)],[c_1,c_11707])).

cnf(c_539,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_13,c_1])).

cnf(c_14783,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,X1),X3)) = k5_xboole_0(X3,X2) ),
    inference(superposition,[status(thm)],[c_13504,c_539])).

cnf(c_111480,plain,
    ( k3_xboole_0(sK2,sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_111472,c_12,c_14783])).

cnf(c_111611,plain,
    ( k3_xboole_0(sK4,sK2) = k3_xboole_0(sK2,sK2)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_111480,c_4082])).

cnf(c_111704,plain,
    ( k3_xboole_0(sK4,sK2) = sK2
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_111611,c_4])).

cnf(c_112014,plain,
    ( k3_xboole_0(sK4,k3_xboole_0(sK2,X0)) = k3_xboole_0(sK2,X0)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_111704,c_8])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(sK2,sK4)
    | ~ r1_tarski(sK3,sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,plain,
    ( r1_tarski(sK2,sK4) != iProver_top
    | r1_tarski(sK3,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_29,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_250,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_610,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(X0,X1)
    | sK2 != X0
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_939,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(X0,sK3)
    | sK2 != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_940,plain,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(k1_xboole_0,sK3)
    | sK2 != k1_xboole_0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_244,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1815,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_244])).

cnf(c_245,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_552,plain,
    ( k2_zfmisc_1(sK2,sK3) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_558,plain,
    ( k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(X0,X1)
    | k1_xboole_0 != k2_zfmisc_1(X0,X1)
    | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_552])).

cnf(c_5932,plain,
    ( k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(X0,sK3)
    | k1_xboole_0 != k2_zfmisc_1(X0,sK3)
    | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_558])).

cnf(c_5933,plain,
    ( k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(k1_xboole_0,sK3)
    | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_5932])).

cnf(c_4882,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK5)) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4671,c_17])).

cnf(c_9848,plain,
    ( k5_xboole_0(k3_xboole_0(sK3,sK5),k1_xboole_0) = sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4882,c_5550])).

cnf(c_9860,plain,
    ( k3_xboole_0(sK3,sK5) = sK3
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9848,c_12])).

cnf(c_9,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_518,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1088,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_518])).

cnf(c_9874,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_9860,c_1088])).

cnf(c_585,plain,
    ( k2_zfmisc_1(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_15684,plain,
    ( k2_zfmisc_1(X0,sK3) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k2_zfmisc_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_585])).

cnf(c_15692,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15684])).

cnf(c_111617,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_111480,c_1088])).

cnf(c_136327,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_137212,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_112014,c_22,c_25,c_29,c_30,c_940,c_1815,c_5933,c_9874,c_15692,c_111617,c_136327])).

cnf(c_137593,plain,
    ( k2_zfmisc_1(sK2,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_137212,c_22])).

cnf(c_137594,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_137593,c_15])).

cnf(c_137595,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_137594])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 51.47/6.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.47/6.99  
% 51.47/6.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.47/6.99  
% 51.47/6.99  ------  iProver source info
% 51.47/6.99  
% 51.47/6.99  git: date: 2020-06-30 10:37:57 +0100
% 51.47/6.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.47/6.99  git: non_committed_changes: false
% 51.47/6.99  git: last_make_outside_of_git: false
% 51.47/6.99  
% 51.47/6.99  ------ 
% 51.47/6.99  
% 51.47/6.99  ------ Input Options
% 51.47/6.99  
% 51.47/6.99  --out_options                           all
% 51.47/6.99  --tptp_safe_out                         true
% 51.47/6.99  --problem_path                          ""
% 51.47/6.99  --include_path                          ""
% 51.47/6.99  --clausifier                            res/vclausify_rel
% 51.47/6.99  --clausifier_options                    ""
% 51.47/6.99  --stdin                                 false
% 51.47/6.99  --stats_out                             all
% 51.47/6.99  
% 51.47/6.99  ------ General Options
% 51.47/6.99  
% 51.47/6.99  --fof                                   false
% 51.47/6.99  --time_out_real                         305.
% 51.47/6.99  --time_out_virtual                      -1.
% 51.47/6.99  --symbol_type_check                     false
% 51.47/6.99  --clausify_out                          false
% 51.47/6.99  --sig_cnt_out                           false
% 51.47/6.99  --trig_cnt_out                          false
% 51.47/6.99  --trig_cnt_out_tolerance                1.
% 51.47/6.99  --trig_cnt_out_sk_spl                   false
% 51.47/6.99  --abstr_cl_out                          false
% 51.47/6.99  
% 51.47/6.99  ------ Global Options
% 51.47/6.99  
% 51.47/6.99  --schedule                              default
% 51.47/6.99  --add_important_lit                     false
% 51.47/6.99  --prop_solver_per_cl                    1000
% 51.47/6.99  --min_unsat_core                        false
% 51.47/6.99  --soft_assumptions                      false
% 51.47/6.99  --soft_lemma_size                       3
% 51.47/6.99  --prop_impl_unit_size                   0
% 51.47/6.99  --prop_impl_unit                        []
% 51.47/6.99  --share_sel_clauses                     true
% 51.47/6.99  --reset_solvers                         false
% 51.47/6.99  --bc_imp_inh                            [conj_cone]
% 51.47/6.99  --conj_cone_tolerance                   3.
% 51.47/6.99  --extra_neg_conj                        none
% 51.47/6.99  --large_theory_mode                     true
% 51.47/6.99  --prolific_symb_bound                   200
% 51.47/6.99  --lt_threshold                          2000
% 51.47/6.99  --clause_weak_htbl                      true
% 51.47/6.99  --gc_record_bc_elim                     false
% 51.47/6.99  
% 51.47/6.99  ------ Preprocessing Options
% 51.47/6.99  
% 51.47/6.99  --preprocessing_flag                    true
% 51.47/6.99  --time_out_prep_mult                    0.1
% 51.47/6.99  --splitting_mode                        input
% 51.47/6.99  --splitting_grd                         true
% 51.47/6.99  --splitting_cvd                         false
% 51.47/6.99  --splitting_cvd_svl                     false
% 51.47/6.99  --splitting_nvd                         32
% 51.47/6.99  --sub_typing                            true
% 51.47/6.99  --prep_gs_sim                           true
% 51.47/6.99  --prep_unflatten                        true
% 51.47/6.99  --prep_res_sim                          true
% 51.47/6.99  --prep_upred                            true
% 51.47/6.99  --prep_sem_filter                       exhaustive
% 51.47/6.99  --prep_sem_filter_out                   false
% 51.47/6.99  --pred_elim                             true
% 51.47/6.99  --res_sim_input                         true
% 51.47/6.99  --eq_ax_congr_red                       true
% 51.47/6.99  --pure_diseq_elim                       true
% 51.47/6.99  --brand_transform                       false
% 51.47/6.99  --non_eq_to_eq                          false
% 51.47/6.99  --prep_def_merge                        true
% 51.47/6.99  --prep_def_merge_prop_impl              false
% 51.47/6.99  --prep_def_merge_mbd                    true
% 51.47/6.99  --prep_def_merge_tr_red                 false
% 51.47/6.99  --prep_def_merge_tr_cl                  false
% 51.47/6.99  --smt_preprocessing                     true
% 51.47/6.99  --smt_ac_axioms                         fast
% 51.47/6.99  --preprocessed_out                      false
% 51.47/6.99  --preprocessed_stats                    false
% 51.47/6.99  
% 51.47/6.99  ------ Abstraction refinement Options
% 51.47/6.99  
% 51.47/6.99  --abstr_ref                             []
% 51.47/6.99  --abstr_ref_prep                        false
% 51.47/6.99  --abstr_ref_until_sat                   false
% 51.47/6.99  --abstr_ref_sig_restrict                funpre
% 51.47/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.47/6.99  --abstr_ref_under                       []
% 51.47/6.99  
% 51.47/6.99  ------ SAT Options
% 51.47/6.99  
% 51.47/6.99  --sat_mode                              false
% 51.47/6.99  --sat_fm_restart_options                ""
% 51.47/6.99  --sat_gr_def                            false
% 51.47/6.99  --sat_epr_types                         true
% 51.47/6.99  --sat_non_cyclic_types                  false
% 51.47/6.99  --sat_finite_models                     false
% 51.47/6.99  --sat_fm_lemmas                         false
% 51.47/6.99  --sat_fm_prep                           false
% 51.47/6.99  --sat_fm_uc_incr                        true
% 51.47/6.99  --sat_out_model                         small
% 51.47/6.99  --sat_out_clauses                       false
% 51.47/6.99  
% 51.47/6.99  ------ QBF Options
% 51.47/6.99  
% 51.47/6.99  --qbf_mode                              false
% 51.47/6.99  --qbf_elim_univ                         false
% 51.47/6.99  --qbf_dom_inst                          none
% 51.47/6.99  --qbf_dom_pre_inst                      false
% 51.47/6.99  --qbf_sk_in                             false
% 51.47/6.99  --qbf_pred_elim                         true
% 51.47/6.99  --qbf_split                             512
% 51.47/6.99  
% 51.47/6.99  ------ BMC1 Options
% 51.47/6.99  
% 51.47/6.99  --bmc1_incremental                      false
% 51.47/6.99  --bmc1_axioms                           reachable_all
% 51.47/6.99  --bmc1_min_bound                        0
% 51.47/6.99  --bmc1_max_bound                        -1
% 51.47/6.99  --bmc1_max_bound_default                -1
% 51.47/6.99  --bmc1_symbol_reachability              true
% 51.47/6.99  --bmc1_property_lemmas                  false
% 51.47/6.99  --bmc1_k_induction                      false
% 51.47/6.99  --bmc1_non_equiv_states                 false
% 51.47/6.99  --bmc1_deadlock                         false
% 51.47/6.99  --bmc1_ucm                              false
% 51.47/6.99  --bmc1_add_unsat_core                   none
% 51.47/6.99  --bmc1_unsat_core_children              false
% 51.47/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.47/6.99  --bmc1_out_stat                         full
% 51.47/6.99  --bmc1_ground_init                      false
% 51.47/6.99  --bmc1_pre_inst_next_state              false
% 51.47/6.99  --bmc1_pre_inst_state                   false
% 51.47/6.99  --bmc1_pre_inst_reach_state             false
% 51.47/6.99  --bmc1_out_unsat_core                   false
% 51.47/6.99  --bmc1_aig_witness_out                  false
% 51.47/6.99  --bmc1_verbose                          false
% 51.47/6.99  --bmc1_dump_clauses_tptp                false
% 51.47/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.47/6.99  --bmc1_dump_file                        -
% 51.47/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.47/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.47/6.99  --bmc1_ucm_extend_mode                  1
% 51.47/6.99  --bmc1_ucm_init_mode                    2
% 51.47/6.99  --bmc1_ucm_cone_mode                    none
% 51.47/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.47/6.99  --bmc1_ucm_relax_model                  4
% 51.47/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.47/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.47/6.99  --bmc1_ucm_layered_model                none
% 51.47/6.99  --bmc1_ucm_max_lemma_size               10
% 51.47/6.99  
% 51.47/6.99  ------ AIG Options
% 51.47/6.99  
% 51.47/6.99  --aig_mode                              false
% 51.47/6.99  
% 51.47/6.99  ------ Instantiation Options
% 51.47/6.99  
% 51.47/6.99  --instantiation_flag                    true
% 51.47/6.99  --inst_sos_flag                         true
% 51.47/6.99  --inst_sos_phase                        true
% 51.47/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.47/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.47/6.99  --inst_lit_sel_side                     num_symb
% 51.47/6.99  --inst_solver_per_active                1400
% 51.47/6.99  --inst_solver_calls_frac                1.
% 51.47/6.99  --inst_passive_queue_type               priority_queues
% 51.47/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.47/6.99  --inst_passive_queues_freq              [25;2]
% 51.47/6.99  --inst_dismatching                      true
% 51.47/6.99  --inst_eager_unprocessed_to_passive     true
% 51.47/6.99  --inst_prop_sim_given                   true
% 51.47/6.99  --inst_prop_sim_new                     false
% 51.47/6.99  --inst_subs_new                         false
% 51.47/6.99  --inst_eq_res_simp                      false
% 51.47/6.99  --inst_subs_given                       false
% 51.47/6.99  --inst_orphan_elimination               true
% 51.47/6.99  --inst_learning_loop_flag               true
% 51.47/6.99  --inst_learning_start                   3000
% 51.47/6.99  --inst_learning_factor                  2
% 51.47/6.99  --inst_start_prop_sim_after_learn       3
% 51.47/6.99  --inst_sel_renew                        solver
% 51.47/6.99  --inst_lit_activity_flag                true
% 51.47/6.99  --inst_restr_to_given                   false
% 51.47/6.99  --inst_activity_threshold               500
% 51.47/6.99  --inst_out_proof                        true
% 51.47/6.99  
% 51.47/6.99  ------ Resolution Options
% 51.47/6.99  
% 51.47/6.99  --resolution_flag                       true
% 51.47/6.99  --res_lit_sel                           adaptive
% 51.47/6.99  --res_lit_sel_side                      none
% 51.47/6.99  --res_ordering                          kbo
% 51.47/6.99  --res_to_prop_solver                    active
% 51.47/6.99  --res_prop_simpl_new                    false
% 51.47/6.99  --res_prop_simpl_given                  true
% 51.47/6.99  --res_passive_queue_type                priority_queues
% 51.47/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.47/6.99  --res_passive_queues_freq               [15;5]
% 51.47/6.99  --res_forward_subs                      full
% 51.47/6.99  --res_backward_subs                     full
% 51.47/6.99  --res_forward_subs_resolution           true
% 51.47/6.99  --res_backward_subs_resolution          true
% 51.47/6.99  --res_orphan_elimination                true
% 51.47/6.99  --res_time_limit                        2.
% 51.47/6.99  --res_out_proof                         true
% 51.47/6.99  
% 51.47/6.99  ------ Superposition Options
% 51.47/6.99  
% 51.47/6.99  --superposition_flag                    true
% 51.47/6.99  --sup_passive_queue_type                priority_queues
% 51.47/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.47/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.47/6.99  --demod_completeness_check              fast
% 51.47/6.99  --demod_use_ground                      true
% 51.47/6.99  --sup_to_prop_solver                    passive
% 51.47/6.99  --sup_prop_simpl_new                    true
% 51.47/6.99  --sup_prop_simpl_given                  true
% 51.47/6.99  --sup_fun_splitting                     true
% 51.47/6.99  --sup_smt_interval                      50000
% 51.47/6.99  
% 51.47/6.99  ------ Superposition Simplification Setup
% 51.47/6.99  
% 51.47/6.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.47/6.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.47/6.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.47/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.47/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.47/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.47/6.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.47/6.99  --sup_immed_triv                        [TrivRules]
% 51.47/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.47/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.47/6.99  --sup_immed_bw_main                     []
% 51.47/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.47/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.47/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.47/6.99  --sup_input_bw                          []
% 51.47/6.99  
% 51.47/6.99  ------ Combination Options
% 51.47/6.99  
% 51.47/6.99  --comb_res_mult                         3
% 51.47/6.99  --comb_sup_mult                         2
% 51.47/6.99  --comb_inst_mult                        10
% 51.47/6.99  
% 51.47/6.99  ------ Debug Options
% 51.47/6.99  
% 51.47/6.99  --dbg_backtrace                         false
% 51.47/6.99  --dbg_dump_prop_clauses                 false
% 51.47/6.99  --dbg_dump_prop_clauses_file            -
% 51.47/6.99  --dbg_out_stat                          false
% 51.47/6.99  ------ Parsing...
% 51.47/6.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.47/6.99  
% 51.47/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.47/6.99  
% 51.47/6.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.47/6.99  
% 51.47/6.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.47/6.99  ------ Proving...
% 51.47/6.99  ------ Problem Properties 
% 51.47/6.99  
% 51.47/6.99  
% 51.47/6.99  clauses                                 24
% 51.47/6.99  conjectures                             3
% 51.47/6.99  EPR                                     1
% 51.47/6.99  Horn                                    21
% 51.47/6.99  unary                                   16
% 51.47/6.99  binary                                  7
% 51.47/6.99  lits                                    33
% 51.47/6.99  lits eq                                 21
% 51.47/6.99  fd_pure                                 0
% 51.47/6.99  fd_pseudo                               0
% 51.47/6.99  fd_cond                                 2
% 51.47/6.99  fd_pseudo_cond                          0
% 51.47/6.99  AC symbols                              2
% 51.47/6.99  
% 51.47/6.99  ------ Schedule dynamic 5 is on 
% 51.47/6.99  
% 51.47/6.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.47/6.99  
% 51.47/6.99  
% 51.47/6.99  ------ 
% 51.47/6.99  Current options:
% 51.47/6.99  ------ 
% 51.47/6.99  
% 51.47/6.99  ------ Input Options
% 51.47/6.99  
% 51.47/6.99  --out_options                           all
% 51.47/6.99  --tptp_safe_out                         true
% 51.47/6.99  --problem_path                          ""
% 51.47/6.99  --include_path                          ""
% 51.47/6.99  --clausifier                            res/vclausify_rel
% 51.47/6.99  --clausifier_options                    ""
% 51.47/6.99  --stdin                                 false
% 51.47/6.99  --stats_out                             all
% 51.47/6.99  
% 51.47/6.99  ------ General Options
% 51.47/6.99  
% 51.47/6.99  --fof                                   false
% 51.47/6.99  --time_out_real                         305.
% 51.47/6.99  --time_out_virtual                      -1.
% 51.47/6.99  --symbol_type_check                     false
% 51.47/6.99  --clausify_out                          false
% 51.47/6.99  --sig_cnt_out                           false
% 51.47/6.99  --trig_cnt_out                          false
% 51.47/6.99  --trig_cnt_out_tolerance                1.
% 51.47/6.99  --trig_cnt_out_sk_spl                   false
% 51.47/6.99  --abstr_cl_out                          false
% 51.47/6.99  
% 51.47/6.99  ------ Global Options
% 51.47/6.99  
% 51.47/6.99  --schedule                              default
% 51.47/6.99  --add_important_lit                     false
% 51.47/6.99  --prop_solver_per_cl                    1000
% 51.47/6.99  --min_unsat_core                        false
% 51.47/6.99  --soft_assumptions                      false
% 51.47/6.99  --soft_lemma_size                       3
% 51.47/6.99  --prop_impl_unit_size                   0
% 51.47/6.99  --prop_impl_unit                        []
% 51.47/6.99  --share_sel_clauses                     true
% 51.47/6.99  --reset_solvers                         false
% 51.47/6.99  --bc_imp_inh                            [conj_cone]
% 51.47/6.99  --conj_cone_tolerance                   3.
% 51.47/6.99  --extra_neg_conj                        none
% 51.47/6.99  --large_theory_mode                     true
% 51.47/6.99  --prolific_symb_bound                   200
% 51.47/6.99  --lt_threshold                          2000
% 51.47/6.99  --clause_weak_htbl                      true
% 51.47/6.99  --gc_record_bc_elim                     false
% 51.47/6.99  
% 51.47/6.99  ------ Preprocessing Options
% 51.47/6.99  
% 51.47/6.99  --preprocessing_flag                    true
% 51.47/6.99  --time_out_prep_mult                    0.1
% 51.47/6.99  --splitting_mode                        input
% 51.47/6.99  --splitting_grd                         true
% 51.47/6.99  --splitting_cvd                         false
% 51.47/6.99  --splitting_cvd_svl                     false
% 51.47/6.99  --splitting_nvd                         32
% 51.47/6.99  --sub_typing                            true
% 51.47/6.99  --prep_gs_sim                           true
% 51.47/6.99  --prep_unflatten                        true
% 51.47/6.99  --prep_res_sim                          true
% 51.47/6.99  --prep_upred                            true
% 51.47/6.99  --prep_sem_filter                       exhaustive
% 51.47/6.99  --prep_sem_filter_out                   false
% 51.47/6.99  --pred_elim                             true
% 51.47/6.99  --res_sim_input                         true
% 51.47/6.99  --eq_ax_congr_red                       true
% 51.47/6.99  --pure_diseq_elim                       true
% 51.47/6.99  --brand_transform                       false
% 51.47/6.99  --non_eq_to_eq                          false
% 51.47/6.99  --prep_def_merge                        true
% 51.47/6.99  --prep_def_merge_prop_impl              false
% 51.47/6.99  --prep_def_merge_mbd                    true
% 51.47/6.99  --prep_def_merge_tr_red                 false
% 51.47/6.99  --prep_def_merge_tr_cl                  false
% 51.47/6.99  --smt_preprocessing                     true
% 51.47/6.99  --smt_ac_axioms                         fast
% 51.47/6.99  --preprocessed_out                      false
% 51.47/6.99  --preprocessed_stats                    false
% 51.47/6.99  
% 51.47/6.99  ------ Abstraction refinement Options
% 51.47/6.99  
% 51.47/6.99  --abstr_ref                             []
% 51.47/6.99  --abstr_ref_prep                        false
% 51.47/6.99  --abstr_ref_until_sat                   false
% 51.47/6.99  --abstr_ref_sig_restrict                funpre
% 51.47/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.47/6.99  --abstr_ref_under                       []
% 51.47/6.99  
% 51.47/6.99  ------ SAT Options
% 51.47/6.99  
% 51.47/6.99  --sat_mode                              false
% 51.47/6.99  --sat_fm_restart_options                ""
% 51.47/6.99  --sat_gr_def                            false
% 51.47/6.99  --sat_epr_types                         true
% 51.47/6.99  --sat_non_cyclic_types                  false
% 51.47/6.99  --sat_finite_models                     false
% 51.47/6.99  --sat_fm_lemmas                         false
% 51.47/6.99  --sat_fm_prep                           false
% 51.47/6.99  --sat_fm_uc_incr                        true
% 51.47/6.99  --sat_out_model                         small
% 51.47/6.99  --sat_out_clauses                       false
% 51.47/6.99  
% 51.47/6.99  ------ QBF Options
% 51.47/6.99  
% 51.47/6.99  --qbf_mode                              false
% 51.47/6.99  --qbf_elim_univ                         false
% 51.47/6.99  --qbf_dom_inst                          none
% 51.47/6.99  --qbf_dom_pre_inst                      false
% 51.47/6.99  --qbf_sk_in                             false
% 51.47/6.99  --qbf_pred_elim                         true
% 51.47/6.99  --qbf_split                             512
% 51.47/6.99  
% 51.47/6.99  ------ BMC1 Options
% 51.47/6.99  
% 51.47/6.99  --bmc1_incremental                      false
% 51.47/6.99  --bmc1_axioms                           reachable_all
% 51.47/6.99  --bmc1_min_bound                        0
% 51.47/6.99  --bmc1_max_bound                        -1
% 51.47/6.99  --bmc1_max_bound_default                -1
% 51.47/6.99  --bmc1_symbol_reachability              true
% 51.47/6.99  --bmc1_property_lemmas                  false
% 51.47/6.99  --bmc1_k_induction                      false
% 51.47/6.99  --bmc1_non_equiv_states                 false
% 51.47/6.99  --bmc1_deadlock                         false
% 51.47/6.99  --bmc1_ucm                              false
% 51.47/6.99  --bmc1_add_unsat_core                   none
% 51.47/6.99  --bmc1_unsat_core_children              false
% 51.47/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.47/6.99  --bmc1_out_stat                         full
% 51.47/6.99  --bmc1_ground_init                      false
% 51.47/6.99  --bmc1_pre_inst_next_state              false
% 51.47/6.99  --bmc1_pre_inst_state                   false
% 51.47/6.99  --bmc1_pre_inst_reach_state             false
% 51.47/6.99  --bmc1_out_unsat_core                   false
% 51.47/6.99  --bmc1_aig_witness_out                  false
% 51.47/6.99  --bmc1_verbose                          false
% 51.47/6.99  --bmc1_dump_clauses_tptp                false
% 51.47/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.47/6.99  --bmc1_dump_file                        -
% 51.47/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.47/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.47/6.99  --bmc1_ucm_extend_mode                  1
% 51.47/6.99  --bmc1_ucm_init_mode                    2
% 51.47/6.99  --bmc1_ucm_cone_mode                    none
% 51.47/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.47/6.99  --bmc1_ucm_relax_model                  4
% 51.47/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.47/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.47/6.99  --bmc1_ucm_layered_model                none
% 51.47/6.99  --bmc1_ucm_max_lemma_size               10
% 51.47/6.99  
% 51.47/6.99  ------ AIG Options
% 51.47/6.99  
% 51.47/6.99  --aig_mode                              false
% 51.47/6.99  
% 51.47/6.99  ------ Instantiation Options
% 51.47/6.99  
% 51.47/6.99  --instantiation_flag                    true
% 51.47/6.99  --inst_sos_flag                         true
% 51.47/6.99  --inst_sos_phase                        true
% 51.47/6.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.47/6.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.47/6.99  --inst_lit_sel_side                     none
% 51.47/6.99  --inst_solver_per_active                1400
% 51.47/6.99  --inst_solver_calls_frac                1.
% 51.47/6.99  --inst_passive_queue_type               priority_queues
% 51.47/6.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.47/6.99  --inst_passive_queues_freq              [25;2]
% 51.47/6.99  --inst_dismatching                      true
% 51.47/6.99  --inst_eager_unprocessed_to_passive     true
% 51.47/6.99  --inst_prop_sim_given                   true
% 51.47/6.99  --inst_prop_sim_new                     false
% 51.47/6.99  --inst_subs_new                         false
% 51.47/6.99  --inst_eq_res_simp                      false
% 51.47/6.99  --inst_subs_given                       false
% 51.47/6.99  --inst_orphan_elimination               true
% 51.47/6.99  --inst_learning_loop_flag               true
% 51.47/6.99  --inst_learning_start                   3000
% 51.47/6.99  --inst_learning_factor                  2
% 51.47/6.99  --inst_start_prop_sim_after_learn       3
% 51.47/6.99  --inst_sel_renew                        solver
% 51.47/6.99  --inst_lit_activity_flag                true
% 51.47/6.99  --inst_restr_to_given                   false
% 51.47/6.99  --inst_activity_threshold               500
% 51.47/6.99  --inst_out_proof                        true
% 51.47/6.99  
% 51.47/6.99  ------ Resolution Options
% 51.47/6.99  
% 51.47/6.99  --resolution_flag                       false
% 51.47/6.99  --res_lit_sel                           adaptive
% 51.47/6.99  --res_lit_sel_side                      none
% 51.47/6.99  --res_ordering                          kbo
% 51.47/6.99  --res_to_prop_solver                    active
% 51.47/6.99  --res_prop_simpl_new                    false
% 51.47/6.99  --res_prop_simpl_given                  true
% 51.47/6.99  --res_passive_queue_type                priority_queues
% 51.47/6.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.47/6.99  --res_passive_queues_freq               [15;5]
% 51.47/6.99  --res_forward_subs                      full
% 51.47/6.99  --res_backward_subs                     full
% 51.47/6.99  --res_forward_subs_resolution           true
% 51.47/6.99  --res_backward_subs_resolution          true
% 51.47/6.99  --res_orphan_elimination                true
% 51.47/6.99  --res_time_limit                        2.
% 51.47/6.99  --res_out_proof                         true
% 51.47/6.99  
% 51.47/6.99  ------ Superposition Options
% 51.47/6.99  
% 51.47/6.99  --superposition_flag                    true
% 51.47/6.99  --sup_passive_queue_type                priority_queues
% 51.47/6.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.47/6.99  --sup_passive_queues_freq               [8;1;4]
% 51.47/6.99  --demod_completeness_check              fast
% 51.47/6.99  --demod_use_ground                      true
% 51.47/6.99  --sup_to_prop_solver                    passive
% 51.47/6.99  --sup_prop_simpl_new                    true
% 51.47/6.99  --sup_prop_simpl_given                  true
% 51.47/6.99  --sup_fun_splitting                     true
% 51.47/6.99  --sup_smt_interval                      50000
% 51.47/6.99  
% 51.47/6.99  ------ Superposition Simplification Setup
% 51.47/6.99  
% 51.47/6.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.47/6.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.47/6.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.47/6.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.47/6.99  --sup_full_triv                         [TrivRules;PropSubs]
% 51.47/6.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.47/6.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.47/6.99  --sup_immed_triv                        [TrivRules]
% 51.47/6.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.47/6.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.47/6.99  --sup_immed_bw_main                     []
% 51.47/6.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.47/6.99  --sup_input_triv                        [Unflattening;TrivRules]
% 51.47/6.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.47/6.99  --sup_input_bw                          []
% 51.47/6.99  
% 51.47/6.99  ------ Combination Options
% 51.47/6.99  
% 51.47/6.99  --comb_res_mult                         3
% 51.47/6.99  --comb_sup_mult                         2
% 51.47/6.99  --comb_inst_mult                        10
% 51.47/6.99  
% 51.47/6.99  ------ Debug Options
% 51.47/6.99  
% 51.47/6.99  --dbg_backtrace                         false
% 51.47/6.99  --dbg_dump_prop_clauses                 false
% 51.47/6.99  --dbg_dump_prop_clauses_file            -
% 51.47/6.99  --dbg_out_stat                          false
% 51.47/6.99  
% 51.47/6.99  
% 51.47/6.99  
% 51.47/6.99  
% 51.47/6.99  ------ Proving...
% 51.47/6.99  
% 51.47/6.99  
% 51.47/6.99  % SZS status Theorem for theBenchmark.p
% 51.47/6.99  
% 51.47/6.99   Resolution empty clause
% 51.47/6.99  
% 51.47/6.99  % SZS output start CNFRefutation for theBenchmark.p
% 51.47/6.99  
% 51.47/6.99  fof(f18,conjecture,(
% 51.47/6.99    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f19,negated_conjecture,(
% 51.47/6.99    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 51.47/6.99    inference(negated_conjecture,[],[f18])).
% 51.47/6.99  
% 51.47/6.99  fof(f25,plain,(
% 51.47/6.99    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 51.47/6.99    inference(ennf_transformation,[],[f19])).
% 51.47/6.99  
% 51.47/6.99  fof(f26,plain,(
% 51.47/6.99    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 51.47/6.99    inference(flattening,[],[f25])).
% 51.47/6.99  
% 51.47/6.99  fof(f34,plain,(
% 51.47/6.99    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK3,sK5) | ~r1_tarski(sK2,sK4)) & k1_xboole_0 != k2_zfmisc_1(sK2,sK3) & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)))),
% 51.47/6.99    introduced(choice_axiom,[])).
% 51.47/6.99  
% 51.47/6.99  fof(f35,plain,(
% 51.47/6.99    (~r1_tarski(sK3,sK5) | ~r1_tarski(sK2,sK4)) & k1_xboole_0 != k2_zfmisc_1(sK2,sK3) & r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))),
% 51.47/6.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f26,f34])).
% 51.47/6.99  
% 51.47/6.99  fof(f58,plain,(
% 51.47/6.99    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))),
% 51.47/6.99    inference(cnf_transformation,[],[f35])).
% 51.47/6.99  
% 51.47/6.99  fof(f10,axiom,(
% 51.47/6.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f24,plain,(
% 51.47/6.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 51.47/6.99    inference(ennf_transformation,[],[f10])).
% 51.47/6.99  
% 51.47/6.99  fof(f47,plain,(
% 51.47/6.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f24])).
% 51.47/6.99  
% 51.47/6.99  fof(f16,axiom,(
% 51.47/6.99    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f55,plain,(
% 51.47/6.99    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))) )),
% 51.47/6.99    inference(cnf_transformation,[],[f16])).
% 51.47/6.99  
% 51.47/6.99  fof(f17,axiom,(
% 51.47/6.99    ! [X0,X1,X2] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2))),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f57,plain,(
% 51.47/6.99    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))) )),
% 51.47/6.99    inference(cnf_transformation,[],[f17])).
% 51.47/6.99  
% 51.47/6.99  fof(f7,axiom,(
% 51.47/6.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f44,plain,(
% 51.47/6.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f7])).
% 51.47/6.99  
% 51.47/6.99  fof(f62,plain,(
% 51.47/6.99    ( ! [X2,X0,X1] : (k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 51.47/6.99    inference(definition_unfolding,[],[f57,f44,f44])).
% 51.47/6.99  
% 51.47/6.99  fof(f4,axiom,(
% 51.47/6.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f20,plain,(
% 51.47/6.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 51.47/6.99    inference(rectify,[],[f4])).
% 51.47/6.99  
% 51.47/6.99  fof(f40,plain,(
% 51.47/6.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 51.47/6.99    inference(cnf_transformation,[],[f20])).
% 51.47/6.99  
% 51.47/6.99  fof(f56,plain,(
% 51.47/6.99    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f17])).
% 51.47/6.99  
% 51.47/6.99  fof(f63,plain,(
% 51.47/6.99    ( ! [X2,X0,X1] : (k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) )),
% 51.47/6.99    inference(definition_unfolding,[],[f56,f44,f44])).
% 51.47/6.99  
% 51.47/6.99  fof(f12,axiom,(
% 51.47/6.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f49,plain,(
% 51.47/6.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 51.47/6.99    inference(cnf_transformation,[],[f12])).
% 51.47/6.99  
% 51.47/6.99  fof(f13,axiom,(
% 51.47/6.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f50,plain,(
% 51.47/6.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f13])).
% 51.47/6.99  
% 51.47/6.99  fof(f2,axiom,(
% 51.47/6.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f37,plain,(
% 51.47/6.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f2])).
% 51.47/6.99  
% 51.47/6.99  fof(f1,axiom,(
% 51.47/6.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f36,plain,(
% 51.47/6.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f1])).
% 51.47/6.99  
% 51.47/6.99  fof(f8,axiom,(
% 51.47/6.99    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f45,plain,(
% 51.47/6.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f8])).
% 51.47/6.99  
% 51.47/6.99  fof(f14,axiom,(
% 51.47/6.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f51,plain,(
% 51.47/6.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 51.47/6.99    inference(cnf_transformation,[],[f14])).
% 51.47/6.99  
% 51.47/6.99  fof(f15,axiom,(
% 51.47/6.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f32,plain,(
% 51.47/6.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 51.47/6.99    inference(nnf_transformation,[],[f15])).
% 51.47/6.99  
% 51.47/6.99  fof(f33,plain,(
% 51.47/6.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 51.47/6.99    inference(flattening,[],[f32])).
% 51.47/6.99  
% 51.47/6.99  fof(f54,plain,(
% 51.47/6.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 51.47/6.99    inference(cnf_transformation,[],[f33])).
% 51.47/6.99  
% 51.47/6.99  fof(f64,plain,(
% 51.47/6.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 51.47/6.99    inference(equality_resolution,[],[f54])).
% 51.47/6.99  
% 51.47/6.99  fof(f52,plain,(
% 51.47/6.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f33])).
% 51.47/6.99  
% 51.47/6.99  fof(f59,plain,(
% 51.47/6.99    k1_xboole_0 != k2_zfmisc_1(sK2,sK3)),
% 51.47/6.99    inference(cnf_transformation,[],[f35])).
% 51.47/6.99  
% 51.47/6.99  fof(f60,plain,(
% 51.47/6.99    ~r1_tarski(sK3,sK5) | ~r1_tarski(sK2,sK4)),
% 51.47/6.99    inference(cnf_transformation,[],[f35])).
% 51.47/6.99  
% 51.47/6.99  fof(f53,plain,(
% 51.47/6.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 51.47/6.99    inference(cnf_transformation,[],[f33])).
% 51.47/6.99  
% 51.47/6.99  fof(f65,plain,(
% 51.47/6.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 51.47/6.99    inference(equality_resolution,[],[f53])).
% 51.47/6.99  
% 51.47/6.99  fof(f9,axiom,(
% 51.47/6.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 51.47/6.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.47/6.99  
% 51.47/6.99  fof(f46,plain,(
% 51.47/6.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 51.47/6.99    inference(cnf_transformation,[],[f9])).
% 51.47/6.99  
% 51.47/6.99  cnf(c_23,negated_conjecture,
% 51.47/6.99      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
% 51.47/6.99      inference(cnf_transformation,[],[f58]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_515,plain,
% 51.47/6.99      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 51.47/6.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_10,plain,
% 51.47/6.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 51.47/6.99      inference(cnf_transformation,[],[f47]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_517,plain,
% 51.47/6.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 51.47/6.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_713,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = k2_zfmisc_1(sK2,sK3) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_515,c_517]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_18,plain,
% 51.47/6.99      ( k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 51.47/6.99      inference(cnf_transformation,[],[f55]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_19,plain,
% 51.47/6.99      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 51.47/6.99      inference(cnf_transformation,[],[f62]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4,plain,
% 51.47/6.99      ( k3_xboole_0(X0,X0) = X0 ),
% 51.47/6.99      inference(cnf_transformation,[],[f40]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1215,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_4,c_18]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1339,plain,
% 51.47/6.99      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) = k2_zfmisc_1(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 51.47/6.99      inference(light_normalisation,[status(thm)],[c_19,c_19,c_1215]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1345,plain,
% 51.47/6.99      ( k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X0,X1),X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_18,c_1339]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_106649,plain,
% 51.47/6.99      ( k2_zfmisc_1(k3_xboole_0(sK2,sK4),k5_xboole_0(sK3,k3_xboole_0(sK3,sK5))) = k5_xboole_0(k2_zfmisc_1(k3_xboole_0(sK2,sK4),sK3),k2_zfmisc_1(sK2,sK3)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_713,c_1345]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_20,plain,
% 51.47/6.99      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1) ),
% 51.47/6.99      inference(cnf_transformation,[],[f63]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1226,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k3_xboole_0(X0,X2),X1) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_4,c_18]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1381,plain,
% 51.47/6.99      ( k5_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k3_xboole_0(X0,X2),X1)) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),X1) ),
% 51.47/6.99      inference(light_normalisation,[status(thm)],[c_20,c_20,c_1226]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_12,plain,
% 51.47/6.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 51.47/6.99      inference(cnf_transformation,[],[f49]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_13,plain,
% 51.47/6.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 51.47/6.99      inference(cnf_transformation,[],[f50]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1,plain,
% 51.47/6.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 51.47/6.99      inference(cnf_transformation,[],[f37]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_538,plain,
% 51.47/6.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_13,c_1]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_6969,plain,
% 51.47/6.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_12,c_538]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_7013,plain,
% 51.47/6.99      ( k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X0,X1),X2),k2_zfmisc_1(X0,X2)) = k5_xboole_0(k1_xboole_0,k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_1381,c_6969]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_757,plain,
% 51.47/6.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_12,c_1]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_7045,plain,
% 51.47/6.99      ( k5_xboole_0(k2_zfmisc_1(k3_xboole_0(X0,X1),X2),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_7013,c_757]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_0,plain,
% 51.47/6.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 51.47/6.99      inference(cnf_transformation,[],[f36]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_8,plain,
% 51.47/6.99      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 51.47/6.99      inference(cnf_transformation,[],[f45]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_533,plain,
% 51.47/6.99      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_3919,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(X0,k2_zfmisc_1(sK4,sK5))) = k3_xboole_0(X0,k2_zfmisc_1(sK2,sK3)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_713,c_533]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_823,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK4,sK5),X0)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),X0) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_713,c_8]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_858,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(X0,k2_zfmisc_1(sK4,sK5))) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),X0) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_0,c_823]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_865,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(X0,k3_xboole_0(X1,k2_zfmisc_1(sK4,sK5)))) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(X0,X1)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_8,c_858]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_916,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k3_xboole_0(X0,k2_zfmisc_1(sK4,sK5)),X0)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(X0,k2_zfmisc_1(sK4,sK5))) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_4,c_865]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_924,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k3_xboole_0(X0,k2_zfmisc_1(sK4,sK5)),X0)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),X0) ),
% 51.47/6.99      inference(light_normalisation,[status(thm)],[c_916,c_858]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4387,plain,
% 51.47/6.99      ( k3_xboole_0(k3_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5)),k2_zfmisc_1(sK2,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_3919,c_924]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4388,plain,
% 51.47/6.99      ( k3_xboole_0(k3_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK4,sK5)),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(sK2,sK3) ),
% 51.47/6.99      inference(light_normalisation,[status(thm)],[c_4387,c_713]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1227,plain,
% 51.47/6.99      ( k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X3,X4))) = k3_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(X2,X3)),k2_zfmisc_1(X1,X4)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_8,c_18]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1242,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k3_xboole_0(X3,X4))) = k3_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(X1,X3)),k2_zfmisc_1(X2,X4)) ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_1227,c_18]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_3918,plain,
% 51.47/6.99      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_4,c_533]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4082,plain,
% 51.47/6.99      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_0,c_3918]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4243,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k3_xboole_0(k2_zfmisc_1(sK2,sK3),X0)) = k3_xboole_0(k3_xboole_0(k2_zfmisc_1(sK4,sK5),X0),k2_zfmisc_1(sK2,sK3)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_823,c_4082]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4333,plain,
% 51.47/6.99      ( k3_xboole_0(k3_xboole_0(k2_zfmisc_1(sK4,sK5),X0),k2_zfmisc_1(sK2,sK3)) = k3_xboole_0(X0,k2_zfmisc_1(sK2,sK3)) ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_4243,c_4082]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4389,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK2,k3_xboole_0(sK5,sK3))) = k2_zfmisc_1(sK2,sK3) ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_4388,c_1215,c_1242,c_4333]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_762,plain,
% 51.47/6.99      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_4,c_8]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_2150,plain,
% 51.47/6.99      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_0,c_762]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4582,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(sK2,k3_xboole_0(sK5,sK3)),k2_zfmisc_1(sK2,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,k3_xboole_0(sK5,sK3)),k2_zfmisc_1(sK4,sK5)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_4389,c_2150]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_2997,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k3_xboole_0(X3,X1))) = k2_zfmisc_1(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_2150,c_18]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1224,plain,
% 51.47/6.99      ( k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_0,c_18]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_3017,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k3_xboole_0(X3,X1))) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X2,X1)) ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_2997,c_1224]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4598,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)) = k2_zfmisc_1(sK2,k3_xboole_0(sK5,sK3)) ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_4582,c_4,c_1215,c_1242,c_3017]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4599,plain,
% 51.47/6.99      ( k2_zfmisc_1(sK2,k3_xboole_0(sK5,sK3)) = k2_zfmisc_1(sK2,sK3) ),
% 51.47/6.99      inference(light_normalisation,[status(thm)],[c_4598,c_713]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4607,plain,
% 51.47/6.99      ( k2_zfmisc_1(sK2,k3_xboole_0(sK3,sK5)) = k2_zfmisc_1(sK2,sK3) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_0,c_4599]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4670,plain,
% 51.47/6.99      ( k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK5))) = k5_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_4607,c_1339]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_14,plain,
% 51.47/6.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 51.47/6.99      inference(cnf_transformation,[],[f51]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4671,plain,
% 51.47/6.99      ( k2_zfmisc_1(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK5))) = k1_xboole_0 ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_4670,c_14]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_30100,plain,
% 51.47/6.99      ( k2_zfmisc_1(k3_xboole_0(sK2,X0),k5_xboole_0(sK3,k3_xboole_0(sK3,sK5))) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,k5_xboole_0(sK3,k3_xboole_0(sK3,sK5)))) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_4671,c_1226]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_15,plain,
% 51.47/6.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 51.47/6.99      inference(cnf_transformation,[],[f64]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_17135,plain,
% 51.47/6.99      ( k2_zfmisc_1(X0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_15,c_1215]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_18751,plain,
% 51.47/6.99      ( k2_zfmisc_1(X0,k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_0,c_17135]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_18931,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k3_xboole_0(X0,X2),X1)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_18751,c_18]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_18770,plain,
% 51.47/6.99      ( k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X1,X2)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_17135,c_18]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_18859,plain,
% 51.47/6.99      ( k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X1,X2)) ),
% 51.47/6.99      inference(light_normalisation,[status(thm)],[c_18770,c_15]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_19010,plain,
% 51.47/6.99      ( k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X1),k1_xboole_0) ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_18931,c_15,c_18859]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_19011,plain,
% 51.47/6.99      ( k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1)) = sP0_iProver_split(X1) ),
% 51.47/6.99      inference(splitting,
% 51.47/6.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 51.47/6.99                [c_19010]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_19190,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(X0,X1),k1_xboole_0) = sP0_iProver_split(X1) ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_18931,c_15,c_18859,c_19011]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_18957,plain,
% 51.47/6.99      ( k5_xboole_0(k2_zfmisc_1(X0,k3_xboole_0(X1,k1_xboole_0)),k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k3_xboole_0(X0,X2),X1))) = k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X2)),k3_xboole_0(X1,k1_xboole_0)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_18751,c_1381]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_19015,plain,
% 51.47/6.99      ( k2_zfmisc_1(X0,k3_xboole_0(X1,k1_xboole_0)) = sP0_iProver_split(X1) ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_19011,c_18751]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_19135,plain,
% 51.47/6.99      ( k5_xboole_0(sP0_iProver_split(X0),k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k3_xboole_0(X1,X2),X0))) = k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X0,k1_xboole_0)) ),
% 51.47/6.99      inference(light_normalisation,[status(thm)],[c_18957,c_19015]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_19136,plain,
% 51.47/6.99      ( k5_xboole_0(sP0_iProver_split(X0),k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X1,X0))) = sP0_iProver_split(X0) ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_19135,c_18859,c_19015]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_19137,plain,
% 51.47/6.99      ( sP0_iProver_split(X0) = k1_xboole_0 ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_19136,c_14,c_19011]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_21080,plain,
% 51.47/6.99      ( k3_xboole_0(k2_zfmisc_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_19190,c_19137]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_21120,plain,
% 51.47/6.99      ( k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X0,X1)) = k1_xboole_0 ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_21080,c_0]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_30378,plain,
% 51.47/6.99      ( k2_zfmisc_1(k3_xboole_0(sK2,X0),k5_xboole_0(sK3,k3_xboole_0(sK3,sK5))) = k1_xboole_0 ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_30100,c_21120]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_106892,plain,
% 51.47/6.99      ( k2_zfmisc_1(k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)),sK3) = k1_xboole_0 ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_106649,c_7045,c_30378]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_17,plain,
% 51.47/6.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 51.47/6.99      | k1_xboole_0 = X0
% 51.47/6.99      | k1_xboole_0 = X1 ),
% 51.47/6.99      inference(cnf_transformation,[],[f52]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_109662,plain,
% 51.47/6.99      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = k1_xboole_0
% 51.47/6.99      | sK3 = k1_xboole_0 ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_106892,c_17]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_537,plain,
% 51.47/6.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_13,c_1]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_5533,plain,
% 51.47/6.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_14,c_537]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_5550,plain,
% 51.47/6.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_5533,c_12]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_6892,plain,
% 51.47/6.99      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X1,X2) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_5550,c_13]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_11688,plain,
% 51.47/6.99      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k5_xboole_0(X0,X2)) = X1 ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_6892,c_5550]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_11707,plain,
% 51.47/6.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X2)) = X1 ),
% 51.47/6.99      inference(light_normalisation,[status(thm)],[c_11688,c_13]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_13491,plain,
% 51.47/6.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3))),k5_xboole_0(k5_xboole_0(X0,X1),X3)) = X2 ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_13,c_11707]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_111472,plain,
% 51.47/6.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)),k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(sK2,sK4))) = sK2
% 51.47/6.99      | sK3 = k1_xboole_0 ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_109662,c_13491]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_13504,plain,
% 51.47/6.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2 ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_1,c_11707]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_539,plain,
% 51.47/6.99      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_13,c_1]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_14783,plain,
% 51.47/6.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(k5_xboole_0(X0,X1),X3)) = k5_xboole_0(X3,X2) ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_13504,c_539]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_111480,plain,
% 51.47/6.99      ( k3_xboole_0(sK2,sK4) = sK2 | sK3 = k1_xboole_0 ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_111472,c_12,c_14783]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_111611,plain,
% 51.47/6.99      ( k3_xboole_0(sK4,sK2) = k3_xboole_0(sK2,sK2) | sK3 = k1_xboole_0 ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_111480,c_4082]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_111704,plain,
% 51.47/6.99      ( k3_xboole_0(sK4,sK2) = sK2 | sK3 = k1_xboole_0 ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_111611,c_4]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_112014,plain,
% 51.47/6.99      ( k3_xboole_0(sK4,k3_xboole_0(sK2,X0)) = k3_xboole_0(sK2,X0)
% 51.47/6.99      | sK3 = k1_xboole_0 ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_111704,c_8]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_22,negated_conjecture,
% 51.47/6.99      ( k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
% 51.47/6.99      inference(cnf_transformation,[],[f59]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_21,negated_conjecture,
% 51.47/6.99      ( ~ r1_tarski(sK2,sK4) | ~ r1_tarski(sK3,sK5) ),
% 51.47/6.99      inference(cnf_transformation,[],[f60]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_25,plain,
% 51.47/6.99      ( r1_tarski(sK2,sK4) != iProver_top | r1_tarski(sK3,sK5) != iProver_top ),
% 51.47/6.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_29,plain,
% 51.47/6.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 51.47/6.99      | k1_xboole_0 = k1_xboole_0 ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_17]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_16,plain,
% 51.47/6.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 51.47/6.99      inference(cnf_transformation,[],[f65]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_30,plain,
% 51.47/6.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_16]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_250,plain,
% 51.47/6.99      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 51.47/6.99      theory(equality) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_610,plain,
% 51.47/6.99      ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(X0,X1) | sK2 != X0 | sK3 != X1 ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_250]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_939,plain,
% 51.47/6.99      ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(X0,sK3) | sK2 != X0 | sK3 != sK3 ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_610]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_940,plain,
% 51.47/6.99      ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(k1_xboole_0,sK3)
% 51.47/6.99      | sK2 != k1_xboole_0
% 51.47/6.99      | sK3 != sK3 ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_939]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_244,plain,( X0 = X0 ),theory(equality) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1815,plain,
% 51.47/6.99      ( sK3 = sK3 ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_244]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_245,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_552,plain,
% 51.47/6.99      ( k2_zfmisc_1(sK2,sK3) != X0
% 51.47/6.99      | k1_xboole_0 != X0
% 51.47/6.99      | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_245]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_558,plain,
% 51.47/6.99      ( k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(X0,X1)
% 51.47/6.99      | k1_xboole_0 != k2_zfmisc_1(X0,X1)
% 51.47/6.99      | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_552]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_5932,plain,
% 51.47/6.99      ( k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(X0,sK3)
% 51.47/6.99      | k1_xboole_0 != k2_zfmisc_1(X0,sK3)
% 51.47/6.99      | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_558]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_5933,plain,
% 51.47/6.99      ( k2_zfmisc_1(sK2,sK3) != k2_zfmisc_1(k1_xboole_0,sK3)
% 51.47/6.99      | k1_xboole_0 = k2_zfmisc_1(sK2,sK3)
% 51.47/6.99      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_5932]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_4882,plain,
% 51.47/6.99      ( k5_xboole_0(sK3,k3_xboole_0(sK3,sK5)) = k1_xboole_0
% 51.47/6.99      | sK2 = k1_xboole_0 ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_4671,c_17]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_9848,plain,
% 51.47/6.99      ( k5_xboole_0(k3_xboole_0(sK3,sK5),k1_xboole_0) = sK3
% 51.47/6.99      | sK2 = k1_xboole_0 ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_4882,c_5550]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_9860,plain,
% 51.47/6.99      ( k3_xboole_0(sK3,sK5) = sK3 | sK2 = k1_xboole_0 ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_9848,c_12]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_9,plain,
% 51.47/6.99      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 51.47/6.99      inference(cnf_transformation,[],[f46]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_518,plain,
% 51.47/6.99      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 51.47/6.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_1088,plain,
% 51.47/6.99      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_0,c_518]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_9874,plain,
% 51.47/6.99      ( sK2 = k1_xboole_0 | r1_tarski(sK3,sK5) = iProver_top ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_9860,c_1088]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_585,plain,
% 51.47/6.99      ( k2_zfmisc_1(X0,X1) != X2
% 51.47/6.99      | k1_xboole_0 != X2
% 51.47/6.99      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_245]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_15684,plain,
% 51.47/6.99      ( k2_zfmisc_1(X0,sK3) != X1
% 51.47/6.99      | k1_xboole_0 != X1
% 51.47/6.99      | k1_xboole_0 = k2_zfmisc_1(X0,sK3) ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_585]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_15692,plain,
% 51.47/6.99      ( k2_zfmisc_1(k1_xboole_0,sK3) != k1_xboole_0
% 51.47/6.99      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK3)
% 51.47/6.99      | k1_xboole_0 != k1_xboole_0 ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_15684]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_111617,plain,
% 51.47/6.99      ( sK3 = k1_xboole_0 | r1_tarski(sK2,sK4) = iProver_top ),
% 51.47/6.99      inference(superposition,[status(thm)],[c_111480,c_1088]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_136327,plain,
% 51.47/6.99      ( k2_zfmisc_1(k1_xboole_0,sK3) = k1_xboole_0 ),
% 51.47/6.99      inference(instantiation,[status(thm)],[c_16]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_137212,plain,
% 51.47/6.99      ( sK3 = k1_xboole_0 ),
% 51.47/6.99      inference(global_propositional_subsumption,
% 51.47/6.99                [status(thm)],
% 51.47/6.99                [c_112014,c_22,c_25,c_29,c_30,c_940,c_1815,c_5933,c_9874,
% 51.47/6.99                 c_15692,c_111617,c_136327]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_137593,plain,
% 51.47/6.99      ( k2_zfmisc_1(sK2,k1_xboole_0) != k1_xboole_0 ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_137212,c_22]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_137594,plain,
% 51.47/6.99      ( k1_xboole_0 != k1_xboole_0 ),
% 51.47/6.99      inference(demodulation,[status(thm)],[c_137593,c_15]) ).
% 51.47/6.99  
% 51.47/6.99  cnf(c_137595,plain,
% 51.47/6.99      ( $false ),
% 51.47/6.99      inference(equality_resolution_simp,[status(thm)],[c_137594]) ).
% 51.47/6.99  
% 51.47/6.99  
% 51.47/6.99  % SZS output end CNFRefutation for theBenchmark.p
% 51.47/6.99  
% 51.47/6.99  ------                               Statistics
% 51.47/6.99  
% 51.47/6.99  ------ General
% 51.47/6.99  
% 51.47/6.99  abstr_ref_over_cycles:                  0
% 51.47/6.99  abstr_ref_under_cycles:                 0
% 51.47/6.99  gc_basic_clause_elim:                   0
% 51.47/6.99  forced_gc_time:                         0
% 51.47/6.99  parsing_time:                           0.018
% 51.47/6.99  unif_index_cands_time:                  0.
% 51.47/6.99  unif_index_add_time:                    0.
% 51.47/6.99  orderings_time:                         0.
% 51.47/6.99  out_proof_time:                         0.019
% 51.47/6.99  total_time:                             6.439
% 51.47/6.99  num_of_symbols:                         46
% 51.47/6.99  num_of_terms:                           313908
% 51.47/6.99  
% 51.47/6.99  ------ Preprocessing
% 51.47/6.99  
% 51.47/6.99  num_of_splits:                          0
% 51.47/6.99  num_of_split_atoms:                     2
% 51.47/6.99  num_of_reused_defs:                     0
% 51.47/6.99  num_eq_ax_congr_red:                    10
% 51.47/6.99  num_of_sem_filtered_clauses:            1
% 51.47/6.99  num_of_subtypes:                        0
% 51.47/6.99  monotx_restored_types:                  0
% 51.47/6.99  sat_num_of_epr_types:                   0
% 51.47/6.99  sat_num_of_non_cyclic_types:            0
% 51.47/6.99  sat_guarded_non_collapsed_types:        0
% 51.47/6.99  num_pure_diseq_elim:                    0
% 51.47/6.99  simp_replaced_by:                       0
% 51.47/6.99  res_preprocessed:                       87
% 51.47/6.99  prep_upred:                             0
% 51.47/6.99  prep_unflattend:                        7
% 51.47/6.99  smt_new_axioms:                         0
% 51.47/6.99  pred_elim_cands:                        3
% 51.47/6.99  pred_elim:                              0
% 51.47/6.99  pred_elim_cl:                           0
% 51.47/6.99  pred_elim_cycles:                       2
% 51.47/6.99  merged_defs:                            6
% 51.47/6.99  merged_defs_ncl:                        0
% 51.47/6.99  bin_hyper_res:                          6
% 51.47/6.99  prep_cycles:                            3
% 51.47/6.99  pred_elim_time:                         0.002
% 51.47/6.99  splitting_time:                         0.
% 51.47/6.99  sem_filter_time:                        0.
% 51.47/6.99  monotx_time:                            0.
% 51.47/6.99  subtype_inf_time:                       0.
% 51.47/6.99  
% 51.47/6.99  ------ Problem properties
% 51.47/6.99  
% 51.47/6.99  clauses:                                24
% 51.47/6.99  conjectures:                            3
% 51.47/6.99  epr:                                    1
% 51.47/6.99  horn:                                   21
% 51.47/6.99  ground:                                 3
% 51.47/6.99  unary:                                  16
% 51.47/6.99  binary:                                 7
% 51.47/6.99  lits:                                   33
% 51.47/6.99  lits_eq:                                21
% 51.47/6.99  fd_pure:                                0
% 51.47/6.99  fd_pseudo:                              0
% 51.47/6.99  fd_cond:                                2
% 51.47/6.99  fd_pseudo_cond:                         0
% 51.47/6.99  ac_symbols:                             2
% 51.47/6.99  
% 51.47/6.99  ------ Propositional Solver
% 51.47/6.99  
% 51.47/6.99  prop_solver_calls:                      68
% 51.47/6.99  prop_fast_solver_calls:                 1000
% 51.47/6.99  smt_solver_calls:                       0
% 51.47/6.99  smt_fast_solver_calls:                  0
% 51.47/6.99  prop_num_of_clauses:                    67314
% 51.47/6.99  prop_preprocess_simplified:             28072
% 51.47/6.99  prop_fo_subsumed:                       10
% 51.47/6.99  prop_solver_time:                       0.
% 51.47/6.99  smt_solver_time:                        0.
% 51.47/6.99  smt_fast_solver_time:                   0.
% 51.47/6.99  prop_fast_solver_time:                  0.
% 51.47/6.99  prop_unsat_core_time:                   0.
% 51.47/6.99  
% 51.47/6.99  ------ QBF
% 51.47/6.99  
% 51.47/6.99  qbf_q_res:                              0
% 51.47/6.99  qbf_num_tautologies:                    0
% 51.47/6.99  qbf_prep_cycles:                        0
% 51.47/6.99  
% 51.47/6.99  ------ BMC1
% 51.47/6.99  
% 51.47/6.99  bmc1_current_bound:                     -1
% 51.47/6.99  bmc1_last_solved_bound:                 -1
% 51.47/6.99  bmc1_unsat_core_size:                   -1
% 51.47/6.99  bmc1_unsat_core_parents_size:           -1
% 51.47/6.99  bmc1_merge_next_fun:                    0
% 51.47/6.99  bmc1_unsat_core_clauses_time:           0.
% 51.47/6.99  
% 51.47/6.99  ------ Instantiation
% 51.47/6.99  
% 51.47/6.99  inst_num_of_clauses:                    5546
% 51.47/6.99  inst_num_in_passive:                    3576
% 51.47/6.99  inst_num_in_active:                     1896
% 51.47/6.99  inst_num_in_unprocessed:                76
% 51.47/6.99  inst_num_of_loops:                      2670
% 51.47/6.99  inst_num_of_learning_restarts:          0
% 51.47/6.99  inst_num_moves_active_passive:          769
% 51.47/6.99  inst_lit_activity:                      0
% 51.47/6.99  inst_lit_activity_moves:                0
% 51.47/6.99  inst_num_tautologies:                   0
% 51.47/6.99  inst_num_prop_implied:                  0
% 51.47/6.99  inst_num_existing_simplified:           0
% 51.47/6.99  inst_num_eq_res_simplified:             0
% 51.47/6.99  inst_num_child_elim:                    0
% 51.47/6.99  inst_num_of_dismatching_blockings:      1742
% 51.47/6.99  inst_num_of_non_proper_insts:           5249
% 51.47/6.99  inst_num_of_duplicates:                 0
% 51.47/6.99  inst_inst_num_from_inst_to_res:         0
% 51.47/6.99  inst_dismatching_checking_time:         0.
% 51.47/6.99  
% 51.47/6.99  ------ Resolution
% 51.47/6.99  
% 51.47/6.99  res_num_of_clauses:                     0
% 51.47/6.99  res_num_in_passive:                     0
% 51.47/6.99  res_num_in_active:                      0
% 51.47/6.99  res_num_of_loops:                       90
% 51.47/6.99  res_forward_subset_subsumed:            401
% 51.47/6.99  res_backward_subset_subsumed:           4
% 51.47/6.99  res_forward_subsumed:                   0
% 51.47/6.99  res_backward_subsumed:                  0
% 51.47/6.99  res_forward_subsumption_resolution:     0
% 51.47/6.99  res_backward_subsumption_resolution:    0
% 51.47/6.99  res_clause_to_clause_subsumption:       301672
% 51.47/7.00  res_orphan_elimination:                 0
% 51.47/7.00  res_tautology_del:                      311
% 51.47/7.00  res_num_eq_res_simplified:              0
% 51.47/7.00  res_num_sel_changes:                    0
% 51.47/7.00  res_moves_from_active_to_pass:          0
% 51.47/7.00  
% 51.47/7.00  ------ Superposition
% 51.47/7.00  
% 51.47/7.00  sup_time_total:                         0.
% 51.47/7.00  sup_time_generating:                    0.
% 51.47/7.00  sup_time_sim_full:                      0.
% 51.47/7.00  sup_time_sim_immed:                     0.
% 51.47/7.00  
% 51.47/7.00  sup_num_of_clauses:                     20614
% 51.47/7.00  sup_num_in_active:                      113
% 51.47/7.00  sup_num_in_passive:                     20501
% 51.47/7.00  sup_num_of_loops:                       532
% 51.47/7.00  sup_fw_superposition:                   28413
% 51.47/7.00  sup_bw_superposition:                   24089
% 51.47/7.00  sup_immediate_simplified:               26565
% 51.47/7.00  sup_given_eliminated:                   11
% 51.47/7.00  comparisons_done:                       0
% 51.47/7.00  comparisons_avoided:                    60
% 51.47/7.00  
% 51.47/7.00  ------ Simplifications
% 51.47/7.00  
% 51.47/7.00  
% 51.47/7.00  sim_fw_subset_subsumed:                 1928
% 51.47/7.00  sim_bw_subset_subsumed:                 303
% 51.47/7.00  sim_fw_subsumed:                        3395
% 51.47/7.00  sim_bw_subsumed:                        1412
% 51.47/7.00  sim_fw_subsumption_res:                 0
% 51.47/7.00  sim_bw_subsumption_res:                 0
% 51.47/7.00  sim_tautology_del:                      39
% 51.47/7.00  sim_eq_tautology_del:                   2998
% 51.47/7.00  sim_eq_res_simp:                        119
% 51.47/7.00  sim_fw_demodulated:                     20426
% 51.47/7.00  sim_bw_demodulated:                     863
% 51.47/7.00  sim_light_normalised:                   6071
% 51.47/7.00  sim_joinable_taut:                      653
% 51.47/7.00  sim_joinable_simp:                      0
% 51.47/7.00  sim_ac_normalised:                      0
% 51.47/7.00  sim_smt_subsumption:                    0
% 51.47/7.00  
%------------------------------------------------------------------------------
