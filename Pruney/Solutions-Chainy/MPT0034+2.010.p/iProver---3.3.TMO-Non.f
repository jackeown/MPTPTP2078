%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:28 EST 2020

% Result     : Timeout 59.83s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  127 (1375 expanded)
%              Number of clauses        :   90 ( 615 expanded)
%              Number of leaves         :   13 ( 312 expanded)
%              Depth                    :   29
%              Number of atoms          :  180 (2063 expanded)
%              Number of equality atoms :   95 (1102 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f23])).

fof(f38,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_274,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_281,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3456,plain,
    ( k2_xboole_0(sK2,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_274,c_281])).

cnf(c_6,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_273,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3457,plain,
    ( k2_xboole_0(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_273,c_281])).

cnf(c_11,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_727,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_11,c_6])).

cnf(c_11271,plain,
    ( k3_xboole_0(k2_xboole_0(X0,sK0),k2_xboole_0(X0,sK1)) = k2_xboole_0(X0,sK0) ),
    inference(superposition,[status(thm)],[c_3457,c_727])).

cnf(c_12843,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,sK0),sK1) = k2_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_3457,c_11271])).

cnf(c_1,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_12920,plain,
    ( k3_xboole_0(k2_xboole_0(sK0,sK0),k3_xboole_0(sK1,X0)) = k3_xboole_0(k2_xboole_0(sK0,sK0),X0) ),
    inference(superposition,[status(thm)],[c_12843,c_1])).

cnf(c_702,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_1901,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = k3_xboole_0(k3_xboole_0(X0,X2),X3) ),
    inference(superposition,[status(thm)],[c_702,c_1])).

cnf(c_169250,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK0),X0),X1)) = k3_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_12920,c_1901])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_7,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_819,plain,
    ( k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k1_xboole_0)),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k2_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_7])).

cnf(c_8,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_837,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k2_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_819,c_4,c_8])).

cnf(c_703,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_2,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_280,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1084,plain,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_280])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_276,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1537,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1084,c_276])).

cnf(c_43394,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k2_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_837,c_1537])).

cnf(c_43395,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k2_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_43394,c_4])).

cnf(c_3757,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_3457,c_11])).

cnf(c_606,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_6])).

cnf(c_707,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_606])).

cnf(c_1931,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(X0,X1),X0)) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_707])).

cnf(c_1981,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(X0,X1),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1931,c_6])).

cnf(c_7361,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,X0),sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_3757,c_1981])).

cnf(c_14046,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k2_xboole_0(sK1,X0),sK0),X1)) = k3_xboole_0(sK0,X1) ),
    inference(superposition,[status(thm)],[c_7361,c_1])).

cnf(c_43464,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1)) = k3_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_43395,c_14046])).

cnf(c_3754,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_3457,c_1981])).

cnf(c_43470,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_43464,c_3754])).

cnf(c_726,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_11])).

cnf(c_1331,plain,
    ( k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)),k3_xboole_0(k2_xboole_0(k1_xboole_0,X1),X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(k1_xboole_0,X1),X2)),k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_726,c_7])).

cnf(c_92269,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k2_xboole_0(X0,sK0)) = k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_43470,c_1331])).

cnf(c_93078,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k2_xboole_0(X0,sK0)) = k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(X0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_92269,c_3457])).

cnf(c_817,plain,
    ( k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)),k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_7])).

cnf(c_842,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_817,c_8])).

cnf(c_57225,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)),k2_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_842,c_4,c_1537])).

cnf(c_95637,plain,
    ( k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(k1_xboole_0,sK1),k1_xboole_0)),k3_xboole_0(k1_xboole_0,sK0)),k2_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),k1_xboole_0)))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),k1_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_93078,c_57225])).

cnf(c_3755,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_3457,c_702])).

cnf(c_823,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k3_xboole_0(k2_xboole_0(X2,X0),X3)) = k3_xboole_0(k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)),X3) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_52968,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1)),k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(k2_xboole_0(X0,sK0),X1)) = k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(X0,sK0)),X1) ),
    inference(superposition,[status(thm)],[c_43470,c_823])).

cnf(c_53012,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(k2_xboole_0(X0,sK0),X1)) = k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(X0,sK0)),X1) ),
    inference(demodulation,[status(thm)],[c_52968,c_726])).

cnf(c_53013,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(k2_xboole_0(X0,sK0),X1)) = k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(X0,sK0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_53012,c_3457])).

cnf(c_95658,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),k1_xboole_0))) = sK0 ),
    inference(demodulation,[status(thm)],[c_95637,c_4,c_6,c_8,c_1537,c_3755,c_53013])).

cnf(c_95659,plain,
    ( k2_xboole_0(k1_xboole_0,sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_95658,c_4,c_43470])).

cnf(c_821,plain,
    ( k2_xboole_0(k2_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(X0,X1)),k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_4,c_7])).

cnf(c_832,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,X1)),X1) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_821,c_4,c_8])).

cnf(c_39110,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,X1)),X1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_832,c_1537])).

cnf(c_100343,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,k2_xboole_0(sK0,X0)),X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_95659,c_39110])).

cnf(c_100392,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_100343,c_6])).

cnf(c_169392,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,X0),X1),X2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_1901,c_100392])).

cnf(c_6896,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK1,X0),X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_3755,c_1])).

cnf(c_23427,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_1,c_6896])).

cnf(c_23603,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_23427,c_3755])).

cnf(c_824,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X0))) = k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_1])).

cnf(c_100321,plain,
    ( k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK0)),k3_xboole_0(sK0,X0)) = k3_xboole_0(k2_xboole_0(X0,k1_xboole_0),k3_xboole_0(sK0,k2_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_95659,c_824])).

cnf(c_100441,plain,
    ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0)),k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,k3_xboole_0(sK0,k2_xboole_0(sK0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_100321,c_4,c_8])).

cnf(c_100442,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,sK0) ),
    inference(demodulation,[status(thm)],[c_100441,c_4,c_6,c_1537])).

cnf(c_170980,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,X0),X1),X2)) = k3_xboole_0(k3_xboole_0(X1,X2),sK0) ),
    inference(demodulation,[status(thm)],[c_169392,c_23603,c_100442])).

cnf(c_171274,plain,
    ( k3_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK1,X0)),X1) = k3_xboole_0(k3_xboole_0(X0,X1),sK0) ),
    inference(demodulation,[status(thm)],[c_169250,c_170980])).

cnf(c_171276,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),sK0) ),
    inference(light_normalisation,[status(thm)],[c_171274,c_3755,c_23603])).

cnf(c_188288,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,sK0)) = k3_xboole_0(sK0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_171276,c_1])).

cnf(c_198042,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(X0,X1),sK0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_6,c_188288])).

cnf(c_199745,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK3,sK0)) = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_3456,c_198042])).

cnf(c_201023,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_199745,c_280])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_889,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3)
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[status(thm)],[c_3,c_12])).

cnf(c_375,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3)
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_407,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_396,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),X0)
    | r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_478,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_892,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_889,c_14,c_12,c_375,c_407,c_478])).

cnf(c_518,plain,
    ( r1_tarski(X0,sK3)
    | ~ r1_tarski(X0,sK2) ),
    inference(resolution,[status(thm)],[c_5,c_13])).

cnf(c_1106,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK2) ),
    inference(resolution,[status(thm)],[c_892,c_518])).

cnf(c_1107,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1106])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_201023,c_1107])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:57:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 59.83/7.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 59.83/7.96  
% 59.83/7.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.83/7.96  
% 59.83/7.96  ------  iProver source info
% 59.83/7.96  
% 59.83/7.96  git: date: 2020-06-30 10:37:57 +0100
% 59.83/7.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.83/7.96  git: non_committed_changes: false
% 59.83/7.96  git: last_make_outside_of_git: false
% 59.83/7.96  
% 59.83/7.96  ------ 
% 59.83/7.96  ------ Parsing...
% 59.83/7.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.83/7.96  
% 59.83/7.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 59.83/7.96  
% 59.83/7.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.83/7.96  
% 59.83/7.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.83/7.96  ------ Proving...
% 59.83/7.96  ------ Problem Properties 
% 59.83/7.96  
% 59.83/7.96  
% 59.83/7.96  clauses                                 15
% 59.83/7.96  conjectures                             3
% 59.83/7.96  EPR                                     5
% 59.83/7.96  Horn                                    15
% 59.83/7.96  unary                                   11
% 59.83/7.96  binary                                  2
% 59.83/7.96  lits                                    21
% 59.83/7.96  lits eq                                 8
% 59.83/7.96  fd_pure                                 0
% 59.83/7.96  fd_pseudo                               0
% 59.83/7.96  fd_cond                                 1
% 59.83/7.96  fd_pseudo_cond                          0
% 59.83/7.96  AC symbols                              0
% 59.83/7.96  
% 59.83/7.96  ------ Input Options Time Limit: Unbounded
% 59.83/7.96  
% 59.83/7.96  
% 59.83/7.96  ------ 
% 59.83/7.96  Current options:
% 59.83/7.96  ------ 
% 59.83/7.96  
% 59.83/7.96  
% 59.83/7.96  
% 59.83/7.96  
% 59.83/7.96  ------ Proving...
% 59.83/7.96  
% 59.83/7.96  
% 59.83/7.96  % SZS status Theorem for theBenchmark.p
% 59.83/7.96  
% 59.83/7.96  % SZS output start CNFRefutation for theBenchmark.p
% 59.83/7.96  
% 59.83/7.96  fof(f13,conjecture,(
% 59.83/7.96    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 59.83/7.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.83/7.96  
% 59.83/7.96  fof(f14,negated_conjecture,(
% 59.83/7.96    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 59.83/7.96    inference(negated_conjecture,[],[f13])).
% 59.83/7.96  
% 59.83/7.96  fof(f21,plain,(
% 59.83/7.96    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 59.83/7.96    inference(ennf_transformation,[],[f14])).
% 59.83/7.96  
% 59.83/7.96  fof(f22,plain,(
% 59.83/7.96    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 59.83/7.96    inference(flattening,[],[f21])).
% 59.83/7.96  
% 59.83/7.96  fof(f23,plain,(
% 59.83/7.96    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 59.83/7.96    introduced(choice_axiom,[])).
% 59.83/7.96  
% 59.83/7.96  fof(f24,plain,(
% 59.83/7.96    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 59.83/7.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f23])).
% 59.83/7.96  
% 59.83/7.96  fof(f38,plain,(
% 59.83/7.96    r1_tarski(sK2,sK3)),
% 59.83/7.96    inference(cnf_transformation,[],[f24])).
% 59.83/7.96  
% 59.83/7.96  fof(f1,axiom,(
% 59.83/7.96    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 59.83/7.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.83/7.96  
% 59.83/7.96  fof(f15,plain,(
% 59.83/7.96    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 59.83/7.96    inference(ennf_transformation,[],[f1])).
% 59.83/7.96  
% 59.83/7.96  fof(f25,plain,(
% 59.83/7.96    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 59.83/7.96    inference(cnf_transformation,[],[f15])).
% 59.83/7.96  
% 59.83/7.96  fof(f7,axiom,(
% 59.83/7.96    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 59.83/7.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.83/7.96  
% 59.83/7.96  fof(f31,plain,(
% 59.83/7.96    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 59.83/7.96    inference(cnf_transformation,[],[f7])).
% 59.83/7.96  
% 59.83/7.96  fof(f37,plain,(
% 59.83/7.96    r1_tarski(sK0,sK1)),
% 59.83/7.96    inference(cnf_transformation,[],[f24])).
% 59.83/7.96  
% 59.83/7.96  fof(f12,axiom,(
% 59.83/7.96    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 59.83/7.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.83/7.96  
% 59.83/7.96  fof(f36,plain,(
% 59.83/7.96    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 59.83/7.96    inference(cnf_transformation,[],[f12])).
% 59.83/7.96  
% 59.83/7.96  fof(f2,axiom,(
% 59.83/7.96    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 59.83/7.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.83/7.96  
% 59.83/7.96  fof(f26,plain,(
% 59.83/7.96    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 59.83/7.96    inference(cnf_transformation,[],[f2])).
% 59.83/7.96  
% 59.83/7.96  fof(f5,axiom,(
% 59.83/7.96    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 59.83/7.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.83/7.96  
% 59.83/7.96  fof(f29,plain,(
% 59.83/7.96    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 59.83/7.96    inference(cnf_transformation,[],[f5])).
% 59.83/7.96  
% 59.83/7.96  fof(f8,axiom,(
% 59.83/7.96    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))),
% 59.83/7.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.83/7.96  
% 59.83/7.96  fof(f32,plain,(
% 59.83/7.96    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))) )),
% 59.83/7.96    inference(cnf_transformation,[],[f8])).
% 59.83/7.96  
% 59.83/7.96  fof(f9,axiom,(
% 59.83/7.96    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 59.83/7.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.83/7.96  
% 59.83/7.96  fof(f33,plain,(
% 59.83/7.96    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 59.83/7.96    inference(cnf_transformation,[],[f9])).
% 59.83/7.96  
% 59.83/7.96  fof(f3,axiom,(
% 59.83/7.96    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 59.83/7.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.83/7.96  
% 59.83/7.96  fof(f27,plain,(
% 59.83/7.96    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 59.83/7.96    inference(cnf_transformation,[],[f3])).
% 59.83/7.96  
% 59.83/7.96  fof(f11,axiom,(
% 59.83/7.96    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 59.83/7.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.83/7.96  
% 59.83/7.96  fof(f20,plain,(
% 59.83/7.96    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 59.83/7.96    inference(ennf_transformation,[],[f11])).
% 59.83/7.96  
% 59.83/7.96  fof(f35,plain,(
% 59.83/7.96    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 59.83/7.96    inference(cnf_transformation,[],[f20])).
% 59.83/7.96  
% 59.83/7.96  fof(f4,axiom,(
% 59.83/7.96    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 59.83/7.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.83/7.96  
% 59.83/7.96  fof(f16,plain,(
% 59.83/7.96    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 59.83/7.96    inference(ennf_transformation,[],[f4])).
% 59.83/7.96  
% 59.83/7.96  fof(f17,plain,(
% 59.83/7.96    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 59.83/7.96    inference(flattening,[],[f16])).
% 59.83/7.96  
% 59.83/7.96  fof(f28,plain,(
% 59.83/7.96    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 59.83/7.96    inference(cnf_transformation,[],[f17])).
% 59.83/7.96  
% 59.83/7.96  fof(f39,plain,(
% 59.83/7.96    ~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),
% 59.83/7.96    inference(cnf_transformation,[],[f24])).
% 59.83/7.96  
% 59.83/7.96  fof(f6,axiom,(
% 59.83/7.96    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 59.83/7.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.83/7.96  
% 59.83/7.96  fof(f18,plain,(
% 59.83/7.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 59.83/7.96    inference(ennf_transformation,[],[f6])).
% 59.83/7.96  
% 59.83/7.96  fof(f19,plain,(
% 59.83/7.96    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 59.83/7.96    inference(flattening,[],[f18])).
% 59.83/7.96  
% 59.83/7.96  fof(f30,plain,(
% 59.83/7.96    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 59.83/7.96    inference(cnf_transformation,[],[f19])).
% 59.83/7.96  
% 59.83/7.96  cnf(c_13,negated_conjecture,
% 59.83/7.96      ( r1_tarski(sK2,sK3) ),
% 59.83/7.96      inference(cnf_transformation,[],[f38]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_274,plain,
% 59.83/7.96      ( r1_tarski(sK2,sK3) = iProver_top ),
% 59.83/7.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_0,plain,
% 59.83/7.96      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 59.83/7.96      inference(cnf_transformation,[],[f25]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_281,plain,
% 59.83/7.96      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 59.83/7.96      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_3456,plain,
% 59.83/7.96      ( k2_xboole_0(sK2,sK3) = sK3 ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_274,c_281]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_6,plain,
% 59.83/7.96      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 59.83/7.96      inference(cnf_transformation,[],[f31]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_14,negated_conjecture,
% 59.83/7.96      ( r1_tarski(sK0,sK1) ),
% 59.83/7.96      inference(cnf_transformation,[],[f37]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_273,plain,
% 59.83/7.96      ( r1_tarski(sK0,sK1) = iProver_top ),
% 59.83/7.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_3457,plain,
% 59.83/7.96      ( k2_xboole_0(sK0,sK1) = sK1 ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_273,c_281]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_11,plain,
% 59.83/7.96      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 59.83/7.96      inference(cnf_transformation,[],[f36]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_727,plain,
% 59.83/7.96      ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X0,X1) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_11,c_6]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_11271,plain,
% 59.83/7.96      ( k3_xboole_0(k2_xboole_0(X0,sK0),k2_xboole_0(X0,sK1)) = k2_xboole_0(X0,sK0) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_3457,c_727]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_12843,plain,
% 59.83/7.96      ( k3_xboole_0(k2_xboole_0(sK0,sK0),sK1) = k2_xboole_0(sK0,sK0) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_3457,c_11271]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_1,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 59.83/7.96      inference(cnf_transformation,[],[f26]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_12920,plain,
% 59.83/7.96      ( k3_xboole_0(k2_xboole_0(sK0,sK0),k3_xboole_0(sK1,X0)) = k3_xboole_0(k2_xboole_0(sK0,sK0),X0) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_12843,c_1]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_702,plain,
% 59.83/7.96      ( k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,X2) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_1901,plain,
% 59.83/7.96      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X2),X3)) = k3_xboole_0(k3_xboole_0(X0,X2),X3) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_702,c_1]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_169250,plain,
% 59.83/7.96      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK0),X0),X1)) = k3_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK1,X0)),X1) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_12920,c_1901]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_4,plain,
% 59.83/7.96      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 59.83/7.96      inference(cnf_transformation,[],[f29]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_7,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) ),
% 59.83/7.96      inference(cnf_transformation,[],[f32]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_819,plain,
% 59.83/7.96      ( k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k1_xboole_0)),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k2_xboole_0(k1_xboole_0,X0)) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_4,c_7]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_8,plain,
% 59.83/7.96      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 59.83/7.96      inference(cnf_transformation,[],[f33]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_837,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k2_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k1_xboole_0,X0)) ),
% 59.83/7.96      inference(demodulation,[status(thm)],[c_819,c_4,c_8]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_703,plain,
% 59.83/7.96      ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_2,plain,
% 59.83/7.96      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 59.83/7.96      inference(cnf_transformation,[],[f27]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_280,plain,
% 59.83/7.96      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 59.83/7.96      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_1084,plain,
% 59.83/7.96      ( r1_tarski(k3_xboole_0(k1_xboole_0,X0),X1) = iProver_top ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_703,c_280]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_10,plain,
% 59.83/7.96      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 59.83/7.96      inference(cnf_transformation,[],[f35]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_276,plain,
% 59.83/7.96      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 59.83/7.96      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_1537,plain,
% 59.83/7.96      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_1084,c_276]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_43394,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k2_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
% 59.83/7.96      inference(light_normalisation,[status(thm)],[c_837,c_1537]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_43395,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X1),k2_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,X1) ),
% 59.83/7.96      inference(demodulation,[status(thm)],[c_43394,c_4]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_3757,plain,
% 59.83/7.96      ( k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK1,X0) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_3457,c_11]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_606,plain,
% 59.83/7.96      ( k3_xboole_0(X0,X0) = X0 ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_4,c_6]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_707,plain,
% 59.83/7.96      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_1,c_606]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_1931,plain,
% 59.83/7.96      ( k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(X0,X1),X0)) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_6,c_707]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_1981,plain,
% 59.83/7.96      ( k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(X0,X1),X0)) = X0 ),
% 59.83/7.96      inference(light_normalisation,[status(thm)],[c_1931,c_6]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_7361,plain,
% 59.83/7.96      ( k3_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK1,X0),sK0)) = sK0 ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_3757,c_1981]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_14046,plain,
% 59.83/7.96      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k2_xboole_0(sK1,X0),sK0),X1)) = k3_xboole_0(sK0,X1) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_7361,c_1]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_43464,plain,
% 59.83/7.96      ( k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1)) = k3_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_43395,c_14046]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_3754,plain,
% 59.83/7.96      ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK0)) = sK0 ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_3457,c_1981]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_43470,plain,
% 59.83/7.96      ( k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1)) = sK0 ),
% 59.83/7.96      inference(light_normalisation,[status(thm)],[c_43464,c_3754]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_726,plain,
% 59.83/7.96      ( k2_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X0,X1) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_4,c_11]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_1331,plain,
% 59.83/7.96      ( k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)),k3_xboole_0(k2_xboole_0(k1_xboole_0,X1),X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(k1_xboole_0,X1),X2)),k2_xboole_0(X2,X0)) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_726,c_7]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_92269,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k2_xboole_0(X0,sK0)) = k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(X0,sK0)) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_43470,c_1331]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_93078,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k2_xboole_0(X0,sK0)) = k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(X0,sK0)) ),
% 59.83/7.96      inference(light_normalisation,[status(thm)],[c_92269,c_3457]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_817,plain,
% 59.83/7.96      ( k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)),k2_xboole_0(X1,X0)) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_4,c_7]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_842,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X1,X0)) ),
% 59.83/7.96      inference(light_normalisation,[status(thm)],[c_817,c_8]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_57225,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)),k2_xboole_0(X1,X0)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)) ),
% 59.83/7.96      inference(demodulation,[status(thm)],[c_842,c_4,c_1537]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_95637,plain,
% 59.83/7.96      ( k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(k1_xboole_0,sK1),k1_xboole_0)),k3_xboole_0(k1_xboole_0,sK0)),k2_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),k1_xboole_0)))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k3_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),k1_xboole_0)))) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_93078,c_57225]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_3755,plain,
% 59.83/7.96      ( k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_3457,c_702]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_823,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k3_xboole_0(k2_xboole_0(X2,X0),X3)) = k3_xboole_0(k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)),X3) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_52968,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK1)),k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(k2_xboole_0(X0,sK0),X1)) = k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(X0,sK0)),X1) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_43470,c_823]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_53012,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(k2_xboole_0(X0,sK0),X1)) = k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(X0,sK0)),X1) ),
% 59.83/7.96      inference(demodulation,[status(thm)],[c_52968,c_726]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_53013,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(k2_xboole_0(X0,sK0),X1)) = k3_xboole_0(k2_xboole_0(k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(k1_xboole_0,sK1),X0)),k3_xboole_0(X0,sK0)),X1) ),
% 59.83/7.96      inference(light_normalisation,[status(thm)],[c_53012,c_3457]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_95658,plain,
% 59.83/7.96      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,k2_xboole_0(k2_xboole_0(k1_xboole_0,sK1),k1_xboole_0))) = sK0 ),
% 59.83/7.96      inference(demodulation,
% 59.83/7.96                [status(thm)],
% 59.83/7.96                [c_95637,c_4,c_6,c_8,c_1537,c_3755,c_53013]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_95659,plain,
% 59.83/7.96      ( k2_xboole_0(k1_xboole_0,sK0) = sK0 ),
% 59.83/7.96      inference(demodulation,[status(thm)],[c_95658,c_4,c_43470]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_821,plain,
% 59.83/7.96      ( k2_xboole_0(k2_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(X0,X1)),k3_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,X1)),X1) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_4,c_7]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_832,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,X1)),X1) = k2_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(X0,X1)) ),
% 59.83/7.96      inference(demodulation,[status(thm)],[c_821,c_4,c_8]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_39110,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(X0,X1)),X1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
% 59.83/7.96      inference(light_normalisation,[status(thm)],[c_832,c_1537]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_100343,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(sK0,k2_xboole_0(sK0,X0)),X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_95659,c_39110]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_100392,plain,
% 59.83/7.96      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,X0) ),
% 59.83/7.96      inference(demodulation,[status(thm)],[c_100343,c_6]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_169392,plain,
% 59.83/7.96      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,X0),X1),X2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK0,X1),X2)) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_1901,c_100392]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_6896,plain,
% 59.83/7.96      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK1,X0),X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_3755,c_1]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_23427,plain,
% 59.83/7.96      ( k3_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_1,c_6896]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_23603,plain,
% 59.83/7.96      ( k3_xboole_0(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ),
% 59.83/7.96      inference(demodulation,[status(thm)],[c_23427,c_3755]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_824,plain,
% 59.83/7.96      ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X2,X0))) = k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_7,c_1]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_100321,plain,
% 59.83/7.96      ( k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k1_xboole_0,sK0)),k3_xboole_0(sK0,X0)) = k3_xboole_0(k2_xboole_0(X0,k1_xboole_0),k3_xboole_0(sK0,k2_xboole_0(sK0,X0))) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_95659,c_824]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_100441,plain,
% 59.83/7.96      ( k2_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK0)),k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,k3_xboole_0(sK0,k2_xboole_0(sK0,X0))) ),
% 59.83/7.96      inference(light_normalisation,[status(thm)],[c_100321,c_4,c_8]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_100442,plain,
% 59.83/7.96      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) = k3_xboole_0(X0,sK0) ),
% 59.83/7.96      inference(demodulation,[status(thm)],[c_100441,c_4,c_6,c_1537]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_170980,plain,
% 59.83/7.96      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,X0),X1),X2)) = k3_xboole_0(k3_xboole_0(X1,X2),sK0) ),
% 59.83/7.96      inference(demodulation,[status(thm)],[c_169392,c_23603,c_100442]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_171274,plain,
% 59.83/7.96      ( k3_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK1,X0)),X1) = k3_xboole_0(k3_xboole_0(X0,X1),sK0) ),
% 59.83/7.96      inference(demodulation,[status(thm)],[c_169250,c_170980]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_171276,plain,
% 59.83/7.96      ( k3_xboole_0(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),sK0) ),
% 59.83/7.96      inference(light_normalisation,
% 59.83/7.96                [status(thm)],
% 59.83/7.96                [c_171274,c_3755,c_23603]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_188288,plain,
% 59.83/7.96      ( k3_xboole_0(X0,k3_xboole_0(X1,sK0)) = k3_xboole_0(sK0,k3_xboole_0(X0,X1)) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_171276,c_1]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_198042,plain,
% 59.83/7.96      ( k3_xboole_0(X0,k3_xboole_0(k2_xboole_0(X0,X1),sK0)) = k3_xboole_0(sK0,X0) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_6,c_188288]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_199745,plain,
% 59.83/7.96      ( k3_xboole_0(sK2,k3_xboole_0(sK3,sK0)) = k3_xboole_0(sK0,sK2) ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_3456,c_198042]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_201023,plain,
% 59.83/7.96      ( r1_tarski(k3_xboole_0(sK0,sK2),sK2) = iProver_top ),
% 59.83/7.96      inference(superposition,[status(thm)],[c_199745,c_280]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_3,plain,
% 59.83/7.96      ( ~ r1_tarski(X0,X1)
% 59.83/7.96      | ~ r1_tarski(X0,X2)
% 59.83/7.96      | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 59.83/7.96      inference(cnf_transformation,[],[f28]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_12,negated_conjecture,
% 59.83/7.96      ( ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
% 59.83/7.96      inference(cnf_transformation,[],[f39]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_889,plain,
% 59.83/7.96      ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3)
% 59.83/7.96      | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
% 59.83/7.96      inference(resolution,[status(thm)],[c_3,c_12]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_375,plain,
% 59.83/7.96      ( r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
% 59.83/7.96      | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3)
% 59.83/7.96      | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
% 59.83/7.96      inference(instantiation,[status(thm)],[c_3]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_407,plain,
% 59.83/7.96      ( r1_tarski(k3_xboole_0(sK0,sK2),sK0) ),
% 59.83/7.96      inference(instantiation,[status(thm)],[c_2]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_5,plain,
% 59.83/7.96      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 59.83/7.96      inference(cnf_transformation,[],[f30]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_396,plain,
% 59.83/7.96      ( ~ r1_tarski(X0,sK1)
% 59.83/7.96      | ~ r1_tarski(k3_xboole_0(sK0,sK2),X0)
% 59.83/7.96      | r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
% 59.83/7.96      inference(instantiation,[status(thm)],[c_5]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_478,plain,
% 59.83/7.96      ( r1_tarski(k3_xboole_0(sK0,sK2),sK1)
% 59.83/7.96      | ~ r1_tarski(k3_xboole_0(sK0,sK2),sK0)
% 59.83/7.96      | ~ r1_tarski(sK0,sK1) ),
% 59.83/7.96      inference(instantiation,[status(thm)],[c_396]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_892,plain,
% 59.83/7.96      ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK3) ),
% 59.83/7.96      inference(global_propositional_subsumption,
% 59.83/7.96                [status(thm)],
% 59.83/7.96                [c_889,c_14,c_12,c_375,c_407,c_478]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_518,plain,
% 59.83/7.96      ( r1_tarski(X0,sK3) | ~ r1_tarski(X0,sK2) ),
% 59.83/7.96      inference(resolution,[status(thm)],[c_5,c_13]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_1106,plain,
% 59.83/7.96      ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK2) ),
% 59.83/7.96      inference(resolution,[status(thm)],[c_892,c_518]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(c_1107,plain,
% 59.83/7.96      ( r1_tarski(k3_xboole_0(sK0,sK2),sK2) != iProver_top ),
% 59.83/7.96      inference(predicate_to_equality,[status(thm)],[c_1106]) ).
% 59.83/7.96  
% 59.83/7.96  cnf(contradiction,plain,
% 59.83/7.96      ( $false ),
% 59.83/7.96      inference(minisat,[status(thm)],[c_201023,c_1107]) ).
% 59.83/7.96  
% 59.83/7.96  
% 59.83/7.96  % SZS output end CNFRefutation for theBenchmark.p
% 59.83/7.96  
% 59.83/7.96  ------                               Statistics
% 59.83/7.96  
% 59.83/7.96  ------ Selected
% 59.83/7.96  
% 59.83/7.96  total_time:                             7.512
% 59.83/7.96  
%------------------------------------------------------------------------------
