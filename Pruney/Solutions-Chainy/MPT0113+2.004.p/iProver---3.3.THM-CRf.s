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
% DateTime   : Thu Dec  3 11:25:43 EST 2020

% Result     : Theorem 4.17s
% Output     : CNFRefutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :  119 (2167 expanded)
%              Number of clauses        :   74 ( 805 expanded)
%              Number of leaves         :   16 ( 573 expanded)
%              Depth                    :   25
%              Number of atoms          :  177 (2721 expanded)
%              Number of equality atoms :   99 (2008 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f13,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f50,f50])).

fof(f17,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f50])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f50])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK2,sK4)
        | ~ r1_tarski(sK2,sK3) )
      & r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ r1_xboole_0(sK2,sK4)
      | ~ r1_tarski(sK2,sK3) )
    & r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f33])).

fof(f56,plain,(
    r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,
    ( ~ r1_xboole_0(sK2,sK4)
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_654,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1064,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_14,c_2])).

cnf(c_19,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_649,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1071,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_649])).

cnf(c_1538,plain,
    ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1064,c_1071])).

cnf(c_1545,plain,
    ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1538,c_14])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_660,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2020,plain,
    ( r1_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_660])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_661,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6759,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2020,c_661])).

cnf(c_13,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1206,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1064,c_13])).

cnf(c_10,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1214,plain,
    ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_1206,c_10])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1762,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1214,c_1])).

cnf(c_17,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_651,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2165,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_649,c_651])).

cnf(c_2776,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)),k4_xboole_0(X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_2165])).

cnf(c_3813,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1064,c_2776])).

cnf(c_6780,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3813,c_661])).

cnf(c_1201,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1064,c_654])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_655,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4091,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1201,c_655])).

cnf(c_4094,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_4091,c_14])).

cnf(c_6807,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6780,c_4094])).

cnf(c_6810,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6759,c_6807])).

cnf(c_4087,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_654,c_655])).

cnf(c_6811,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6810,c_14,c_4087])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1072,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_7139,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_6811,c_1072])).

cnf(c_7187,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7139,c_6811])).

cnf(c_1567,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1064,c_1072])).

cnf(c_1568,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_1567,c_14])).

cnf(c_4258,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_4094,c_1568])).

cnf(c_1205,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1064,c_0])).

cnf(c_4264,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_4094,c_1205])).

cnf(c_4271,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_4264,c_1205])).

cnf(c_4279,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_4258,c_4271])).

cnf(c_7188,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7187,c_14,c_4279])).

cnf(c_1209,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1064,c_0])).

cnf(c_7197,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_7188,c_1209])).

cnf(c_7240,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7197,c_6807])).

cnf(c_7241,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7240,c_14,c_7188])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_647,plain,
    ( r1_tarski(sK2,k4_xboole_0(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4088,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = sK2 ),
    inference(superposition,[status(thm)],[c_647,c_655])).

cnf(c_4636,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_4088,c_0])).

cnf(c_4855,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k5_xboole_0(sK2,sK2)) = k2_xboole_0(k4_xboole_0(sK3,sK4),sK2) ),
    inference(superposition,[status(thm)],[c_4636,c_13])).

cnf(c_7588,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK3,sK4),sK2) ),
    inference(demodulation,[status(thm)],[c_7241,c_4855])).

cnf(c_7602,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),sK2) = k4_xboole_0(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_7588,c_10])).

cnf(c_8030,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_7602,c_1])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_656,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8090,plain,
    ( r1_tarski(k4_xboole_0(sK3,sK4),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8030,c_656])).

cnf(c_16674,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_8090])).

cnf(c_2016,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_649,c_660])).

cnf(c_16,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_652,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8044,plain,
    ( r1_xboole_0(X0,k4_xboole_0(sK3,sK4)) != iProver_top
    | r1_xboole_0(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7602,c_652])).

cnf(c_13745,plain,
    ( r1_xboole_0(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2016,c_8044])).

cnf(c_15377,plain,
    ( r1_xboole_0(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_13745,c_660])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,plain,
    ( r1_tarski(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16674,c_15377,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:40:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.17/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/0.99  
% 4.17/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.17/0.99  
% 4.17/0.99  ------  iProver source info
% 4.17/0.99  
% 4.17/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.17/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.17/0.99  git: non_committed_changes: false
% 4.17/0.99  git: last_make_outside_of_git: false
% 4.17/0.99  
% 4.17/0.99  ------ 
% 4.17/0.99  
% 4.17/0.99  ------ Input Options
% 4.17/0.99  
% 4.17/0.99  --out_options                           all
% 4.17/0.99  --tptp_safe_out                         true
% 4.17/0.99  --problem_path                          ""
% 4.17/0.99  --include_path                          ""
% 4.17/0.99  --clausifier                            res/vclausify_rel
% 4.17/0.99  --clausifier_options                    ""
% 4.17/0.99  --stdin                                 false
% 4.17/0.99  --stats_out                             all
% 4.17/0.99  
% 4.17/0.99  ------ General Options
% 4.17/0.99  
% 4.17/0.99  --fof                                   false
% 4.17/0.99  --time_out_real                         305.
% 4.17/0.99  --time_out_virtual                      -1.
% 4.17/0.99  --symbol_type_check                     false
% 4.17/0.99  --clausify_out                          false
% 4.17/0.99  --sig_cnt_out                           false
% 4.17/0.99  --trig_cnt_out                          false
% 4.17/0.99  --trig_cnt_out_tolerance                1.
% 4.17/0.99  --trig_cnt_out_sk_spl                   false
% 4.17/0.99  --abstr_cl_out                          false
% 4.17/0.99  
% 4.17/0.99  ------ Global Options
% 4.17/0.99  
% 4.17/0.99  --schedule                              default
% 4.17/0.99  --add_important_lit                     false
% 4.17/0.99  --prop_solver_per_cl                    1000
% 4.17/0.99  --min_unsat_core                        false
% 4.17/0.99  --soft_assumptions                      false
% 4.17/0.99  --soft_lemma_size                       3
% 4.17/0.99  --prop_impl_unit_size                   0
% 4.17/0.99  --prop_impl_unit                        []
% 4.17/0.99  --share_sel_clauses                     true
% 4.17/0.99  --reset_solvers                         false
% 4.17/0.99  --bc_imp_inh                            [conj_cone]
% 4.17/0.99  --conj_cone_tolerance                   3.
% 4.17/0.99  --extra_neg_conj                        none
% 4.17/0.99  --large_theory_mode                     true
% 4.17/0.99  --prolific_symb_bound                   200
% 4.17/0.99  --lt_threshold                          2000
% 4.17/0.99  --clause_weak_htbl                      true
% 4.17/0.99  --gc_record_bc_elim                     false
% 4.17/0.99  
% 4.17/0.99  ------ Preprocessing Options
% 4.17/0.99  
% 4.17/0.99  --preprocessing_flag                    true
% 4.17/0.99  --time_out_prep_mult                    0.1
% 4.17/0.99  --splitting_mode                        input
% 4.17/0.99  --splitting_grd                         true
% 4.17/0.99  --splitting_cvd                         false
% 4.17/0.99  --splitting_cvd_svl                     false
% 4.17/0.99  --splitting_nvd                         32
% 4.17/0.99  --sub_typing                            true
% 4.17/0.99  --prep_gs_sim                           true
% 4.17/0.99  --prep_unflatten                        true
% 4.17/0.99  --prep_res_sim                          true
% 4.17/0.99  --prep_upred                            true
% 4.17/0.99  --prep_sem_filter                       exhaustive
% 4.17/0.99  --prep_sem_filter_out                   false
% 4.17/0.99  --pred_elim                             true
% 4.17/0.99  --res_sim_input                         true
% 4.17/0.99  --eq_ax_congr_red                       true
% 4.17/0.99  --pure_diseq_elim                       true
% 4.17/0.99  --brand_transform                       false
% 4.17/0.99  --non_eq_to_eq                          false
% 4.17/0.99  --prep_def_merge                        true
% 4.17/0.99  --prep_def_merge_prop_impl              false
% 4.17/0.99  --prep_def_merge_mbd                    true
% 4.17/0.99  --prep_def_merge_tr_red                 false
% 4.17/0.99  --prep_def_merge_tr_cl                  false
% 4.17/0.99  --smt_preprocessing                     true
% 4.17/0.99  --smt_ac_axioms                         fast
% 4.17/0.99  --preprocessed_out                      false
% 4.17/0.99  --preprocessed_stats                    false
% 4.17/0.99  
% 4.17/0.99  ------ Abstraction refinement Options
% 4.17/0.99  
% 4.17/0.99  --abstr_ref                             []
% 4.17/0.99  --abstr_ref_prep                        false
% 4.17/0.99  --abstr_ref_until_sat                   false
% 4.17/0.99  --abstr_ref_sig_restrict                funpre
% 4.17/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.17/0.99  --abstr_ref_under                       []
% 4.17/0.99  
% 4.17/0.99  ------ SAT Options
% 4.17/0.99  
% 4.17/0.99  --sat_mode                              false
% 4.17/0.99  --sat_fm_restart_options                ""
% 4.17/0.99  --sat_gr_def                            false
% 4.17/0.99  --sat_epr_types                         true
% 4.17/0.99  --sat_non_cyclic_types                  false
% 4.17/0.99  --sat_finite_models                     false
% 4.17/0.99  --sat_fm_lemmas                         false
% 4.17/0.99  --sat_fm_prep                           false
% 4.17/0.99  --sat_fm_uc_incr                        true
% 4.17/0.99  --sat_out_model                         small
% 4.17/0.99  --sat_out_clauses                       false
% 4.17/0.99  
% 4.17/0.99  ------ QBF Options
% 4.17/0.99  
% 4.17/0.99  --qbf_mode                              false
% 4.17/0.99  --qbf_elim_univ                         false
% 4.17/0.99  --qbf_dom_inst                          none
% 4.17/0.99  --qbf_dom_pre_inst                      false
% 4.17/0.99  --qbf_sk_in                             false
% 4.17/0.99  --qbf_pred_elim                         true
% 4.17/0.99  --qbf_split                             512
% 4.17/0.99  
% 4.17/0.99  ------ BMC1 Options
% 4.17/0.99  
% 4.17/0.99  --bmc1_incremental                      false
% 4.17/0.99  --bmc1_axioms                           reachable_all
% 4.17/0.99  --bmc1_min_bound                        0
% 4.17/0.99  --bmc1_max_bound                        -1
% 4.17/0.99  --bmc1_max_bound_default                -1
% 4.17/0.99  --bmc1_symbol_reachability              true
% 4.17/0.99  --bmc1_property_lemmas                  false
% 4.17/0.99  --bmc1_k_induction                      false
% 4.17/0.99  --bmc1_non_equiv_states                 false
% 4.17/0.99  --bmc1_deadlock                         false
% 4.17/0.99  --bmc1_ucm                              false
% 4.17/0.99  --bmc1_add_unsat_core                   none
% 4.17/0.99  --bmc1_unsat_core_children              false
% 4.17/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.17/0.99  --bmc1_out_stat                         full
% 4.17/0.99  --bmc1_ground_init                      false
% 4.17/0.99  --bmc1_pre_inst_next_state              false
% 4.17/0.99  --bmc1_pre_inst_state                   false
% 4.17/0.99  --bmc1_pre_inst_reach_state             false
% 4.17/0.99  --bmc1_out_unsat_core                   false
% 4.17/0.99  --bmc1_aig_witness_out                  false
% 4.17/0.99  --bmc1_verbose                          false
% 4.17/0.99  --bmc1_dump_clauses_tptp                false
% 4.17/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.17/0.99  --bmc1_dump_file                        -
% 4.17/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.17/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.17/0.99  --bmc1_ucm_extend_mode                  1
% 4.17/0.99  --bmc1_ucm_init_mode                    2
% 4.17/0.99  --bmc1_ucm_cone_mode                    none
% 4.17/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.17/0.99  --bmc1_ucm_relax_model                  4
% 4.17/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.17/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.17/0.99  --bmc1_ucm_layered_model                none
% 4.17/0.99  --bmc1_ucm_max_lemma_size               10
% 4.17/0.99  
% 4.17/0.99  ------ AIG Options
% 4.17/0.99  
% 4.17/0.99  --aig_mode                              false
% 4.17/0.99  
% 4.17/0.99  ------ Instantiation Options
% 4.17/0.99  
% 4.17/0.99  --instantiation_flag                    true
% 4.17/0.99  --inst_sos_flag                         true
% 4.17/0.99  --inst_sos_phase                        true
% 4.17/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.17/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.17/0.99  --inst_lit_sel_side                     num_symb
% 4.17/0.99  --inst_solver_per_active                1400
% 4.17/0.99  --inst_solver_calls_frac                1.
% 4.17/0.99  --inst_passive_queue_type               priority_queues
% 4.17/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.17/0.99  --inst_passive_queues_freq              [25;2]
% 4.17/0.99  --inst_dismatching                      true
% 4.17/0.99  --inst_eager_unprocessed_to_passive     true
% 4.17/0.99  --inst_prop_sim_given                   true
% 4.17/0.99  --inst_prop_sim_new                     false
% 4.17/0.99  --inst_subs_new                         false
% 4.17/0.99  --inst_eq_res_simp                      false
% 4.17/0.99  --inst_subs_given                       false
% 4.17/0.99  --inst_orphan_elimination               true
% 4.17/0.99  --inst_learning_loop_flag               true
% 4.17/0.99  --inst_learning_start                   3000
% 4.17/0.99  --inst_learning_factor                  2
% 4.17/0.99  --inst_start_prop_sim_after_learn       3
% 4.17/0.99  --inst_sel_renew                        solver
% 4.17/0.99  --inst_lit_activity_flag                true
% 4.17/0.99  --inst_restr_to_given                   false
% 4.17/0.99  --inst_activity_threshold               500
% 4.17/0.99  --inst_out_proof                        true
% 4.17/0.99  
% 4.17/0.99  ------ Resolution Options
% 4.17/0.99  
% 4.17/0.99  --resolution_flag                       true
% 4.17/0.99  --res_lit_sel                           adaptive
% 4.17/0.99  --res_lit_sel_side                      none
% 4.17/0.99  --res_ordering                          kbo
% 4.17/0.99  --res_to_prop_solver                    active
% 4.17/0.99  --res_prop_simpl_new                    false
% 4.17/0.99  --res_prop_simpl_given                  true
% 4.17/0.99  --res_passive_queue_type                priority_queues
% 4.17/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.17/0.99  --res_passive_queues_freq               [15;5]
% 4.17/0.99  --res_forward_subs                      full
% 4.17/0.99  --res_backward_subs                     full
% 4.17/0.99  --res_forward_subs_resolution           true
% 4.17/0.99  --res_backward_subs_resolution          true
% 4.17/0.99  --res_orphan_elimination                true
% 4.17/0.99  --res_time_limit                        2.
% 4.17/0.99  --res_out_proof                         true
% 4.17/0.99  
% 4.17/0.99  ------ Superposition Options
% 4.17/0.99  
% 4.17/0.99  --superposition_flag                    true
% 4.17/0.99  --sup_passive_queue_type                priority_queues
% 4.17/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.17/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.17/0.99  --demod_completeness_check              fast
% 4.17/0.99  --demod_use_ground                      true
% 4.17/0.99  --sup_to_prop_solver                    passive
% 4.17/0.99  --sup_prop_simpl_new                    true
% 4.17/0.99  --sup_prop_simpl_given                  true
% 4.17/0.99  --sup_fun_splitting                     true
% 4.17/0.99  --sup_smt_interval                      50000
% 4.17/0.99  
% 4.17/0.99  ------ Superposition Simplification Setup
% 4.17/0.99  
% 4.17/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.17/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.17/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.17/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.17/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.17/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.17/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.17/0.99  --sup_immed_triv                        [TrivRules]
% 4.17/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.17/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.17/0.99  --sup_immed_bw_main                     []
% 4.17/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.17/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.17/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.17/0.99  --sup_input_bw                          []
% 4.17/0.99  
% 4.17/0.99  ------ Combination Options
% 4.17/0.99  
% 4.17/0.99  --comb_res_mult                         3
% 4.17/0.99  --comb_sup_mult                         2
% 4.17/0.99  --comb_inst_mult                        10
% 4.17/0.99  
% 4.17/0.99  ------ Debug Options
% 4.17/0.99  
% 4.17/0.99  --dbg_backtrace                         false
% 4.17/0.99  --dbg_dump_prop_clauses                 false
% 4.17/0.99  --dbg_dump_prop_clauses_file            -
% 4.17/0.99  --dbg_out_stat                          false
% 4.17/0.99  ------ Parsing...
% 4.17/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.17/0.99  
% 4.17/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.17/0.99  
% 4.17/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.17/0.99  
% 4.17/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.17/0.99  ------ Proving...
% 4.17/0.99  ------ Problem Properties 
% 4.17/0.99  
% 4.17/0.99  
% 4.17/0.99  clauses                                 22
% 4.17/0.99  conjectures                             2
% 4.17/0.99  EPR                                     3
% 4.17/0.99  Horn                                    20
% 4.17/0.99  unary                                   10
% 4.17/0.99  binary                                  11
% 4.17/1.00  lits                                    35
% 4.17/1.00  lits eq                                 10
% 4.17/1.00  fd_pure                                 0
% 4.17/1.00  fd_pseudo                               0
% 4.17/1.00  fd_cond                                 1
% 4.17/1.00  fd_pseudo_cond                          0
% 4.17/1.00  AC symbols                              0
% 4.17/1.00  
% 4.17/1.00  ------ Schedule dynamic 5 is on 
% 4.17/1.00  
% 4.17/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.17/1.00  
% 4.17/1.00  
% 4.17/1.00  ------ 
% 4.17/1.00  Current options:
% 4.17/1.00  ------ 
% 4.17/1.00  
% 4.17/1.00  ------ Input Options
% 4.17/1.00  
% 4.17/1.00  --out_options                           all
% 4.17/1.00  --tptp_safe_out                         true
% 4.17/1.00  --problem_path                          ""
% 4.17/1.00  --include_path                          ""
% 4.17/1.00  --clausifier                            res/vclausify_rel
% 4.17/1.00  --clausifier_options                    ""
% 4.17/1.00  --stdin                                 false
% 4.17/1.00  --stats_out                             all
% 4.17/1.00  
% 4.17/1.00  ------ General Options
% 4.17/1.00  
% 4.17/1.00  --fof                                   false
% 4.17/1.00  --time_out_real                         305.
% 4.17/1.00  --time_out_virtual                      -1.
% 4.17/1.00  --symbol_type_check                     false
% 4.17/1.00  --clausify_out                          false
% 4.17/1.00  --sig_cnt_out                           false
% 4.17/1.00  --trig_cnt_out                          false
% 4.17/1.00  --trig_cnt_out_tolerance                1.
% 4.17/1.00  --trig_cnt_out_sk_spl                   false
% 4.17/1.00  --abstr_cl_out                          false
% 4.17/1.00  
% 4.17/1.00  ------ Global Options
% 4.17/1.00  
% 4.17/1.00  --schedule                              default
% 4.17/1.00  --add_important_lit                     false
% 4.17/1.00  --prop_solver_per_cl                    1000
% 4.17/1.00  --min_unsat_core                        false
% 4.17/1.00  --soft_assumptions                      false
% 4.17/1.00  --soft_lemma_size                       3
% 4.17/1.00  --prop_impl_unit_size                   0
% 4.17/1.00  --prop_impl_unit                        []
% 4.17/1.00  --share_sel_clauses                     true
% 4.17/1.00  --reset_solvers                         false
% 4.17/1.00  --bc_imp_inh                            [conj_cone]
% 4.17/1.00  --conj_cone_tolerance                   3.
% 4.17/1.00  --extra_neg_conj                        none
% 4.17/1.00  --large_theory_mode                     true
% 4.17/1.00  --prolific_symb_bound                   200
% 4.17/1.00  --lt_threshold                          2000
% 4.17/1.00  --clause_weak_htbl                      true
% 4.17/1.00  --gc_record_bc_elim                     false
% 4.17/1.00  
% 4.17/1.00  ------ Preprocessing Options
% 4.17/1.00  
% 4.17/1.00  --preprocessing_flag                    true
% 4.17/1.00  --time_out_prep_mult                    0.1
% 4.17/1.00  --splitting_mode                        input
% 4.17/1.00  --splitting_grd                         true
% 4.17/1.00  --splitting_cvd                         false
% 4.17/1.00  --splitting_cvd_svl                     false
% 4.17/1.00  --splitting_nvd                         32
% 4.17/1.00  --sub_typing                            true
% 4.17/1.00  --prep_gs_sim                           true
% 4.17/1.00  --prep_unflatten                        true
% 4.17/1.00  --prep_res_sim                          true
% 4.17/1.00  --prep_upred                            true
% 4.17/1.00  --prep_sem_filter                       exhaustive
% 4.17/1.00  --prep_sem_filter_out                   false
% 4.17/1.00  --pred_elim                             true
% 4.17/1.00  --res_sim_input                         true
% 4.17/1.00  --eq_ax_congr_red                       true
% 4.17/1.00  --pure_diseq_elim                       true
% 4.17/1.00  --brand_transform                       false
% 4.17/1.00  --non_eq_to_eq                          false
% 4.17/1.00  --prep_def_merge                        true
% 4.17/1.00  --prep_def_merge_prop_impl              false
% 4.17/1.00  --prep_def_merge_mbd                    true
% 4.17/1.00  --prep_def_merge_tr_red                 false
% 4.17/1.00  --prep_def_merge_tr_cl                  false
% 4.17/1.00  --smt_preprocessing                     true
% 4.17/1.00  --smt_ac_axioms                         fast
% 4.17/1.00  --preprocessed_out                      false
% 4.17/1.00  --preprocessed_stats                    false
% 4.17/1.00  
% 4.17/1.00  ------ Abstraction refinement Options
% 4.17/1.00  
% 4.17/1.00  --abstr_ref                             []
% 4.17/1.00  --abstr_ref_prep                        false
% 4.17/1.00  --abstr_ref_until_sat                   false
% 4.17/1.00  --abstr_ref_sig_restrict                funpre
% 4.17/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.17/1.00  --abstr_ref_under                       []
% 4.17/1.00  
% 4.17/1.00  ------ SAT Options
% 4.17/1.00  
% 4.17/1.00  --sat_mode                              false
% 4.17/1.00  --sat_fm_restart_options                ""
% 4.17/1.00  --sat_gr_def                            false
% 4.17/1.00  --sat_epr_types                         true
% 4.17/1.00  --sat_non_cyclic_types                  false
% 4.17/1.00  --sat_finite_models                     false
% 4.17/1.00  --sat_fm_lemmas                         false
% 4.17/1.00  --sat_fm_prep                           false
% 4.17/1.00  --sat_fm_uc_incr                        true
% 4.17/1.00  --sat_out_model                         small
% 4.17/1.00  --sat_out_clauses                       false
% 4.17/1.00  
% 4.17/1.00  ------ QBF Options
% 4.17/1.00  
% 4.17/1.00  --qbf_mode                              false
% 4.17/1.00  --qbf_elim_univ                         false
% 4.17/1.00  --qbf_dom_inst                          none
% 4.17/1.00  --qbf_dom_pre_inst                      false
% 4.17/1.00  --qbf_sk_in                             false
% 4.17/1.00  --qbf_pred_elim                         true
% 4.17/1.00  --qbf_split                             512
% 4.17/1.00  
% 4.17/1.00  ------ BMC1 Options
% 4.17/1.00  
% 4.17/1.00  --bmc1_incremental                      false
% 4.17/1.00  --bmc1_axioms                           reachable_all
% 4.17/1.00  --bmc1_min_bound                        0
% 4.17/1.00  --bmc1_max_bound                        -1
% 4.17/1.00  --bmc1_max_bound_default                -1
% 4.17/1.00  --bmc1_symbol_reachability              true
% 4.17/1.00  --bmc1_property_lemmas                  false
% 4.17/1.00  --bmc1_k_induction                      false
% 4.17/1.00  --bmc1_non_equiv_states                 false
% 4.17/1.00  --bmc1_deadlock                         false
% 4.17/1.00  --bmc1_ucm                              false
% 4.17/1.00  --bmc1_add_unsat_core                   none
% 4.17/1.00  --bmc1_unsat_core_children              false
% 4.17/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.17/1.00  --bmc1_out_stat                         full
% 4.17/1.00  --bmc1_ground_init                      false
% 4.17/1.00  --bmc1_pre_inst_next_state              false
% 4.17/1.00  --bmc1_pre_inst_state                   false
% 4.17/1.00  --bmc1_pre_inst_reach_state             false
% 4.17/1.00  --bmc1_out_unsat_core                   false
% 4.17/1.00  --bmc1_aig_witness_out                  false
% 4.17/1.00  --bmc1_verbose                          false
% 4.17/1.00  --bmc1_dump_clauses_tptp                false
% 4.17/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.17/1.00  --bmc1_dump_file                        -
% 4.17/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.17/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.17/1.00  --bmc1_ucm_extend_mode                  1
% 4.17/1.00  --bmc1_ucm_init_mode                    2
% 4.17/1.00  --bmc1_ucm_cone_mode                    none
% 4.17/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.17/1.00  --bmc1_ucm_relax_model                  4
% 4.17/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.17/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.17/1.00  --bmc1_ucm_layered_model                none
% 4.17/1.00  --bmc1_ucm_max_lemma_size               10
% 4.17/1.00  
% 4.17/1.00  ------ AIG Options
% 4.17/1.00  
% 4.17/1.00  --aig_mode                              false
% 4.17/1.00  
% 4.17/1.00  ------ Instantiation Options
% 4.17/1.00  
% 4.17/1.00  --instantiation_flag                    true
% 4.17/1.00  --inst_sos_flag                         true
% 4.17/1.00  --inst_sos_phase                        true
% 4.17/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.17/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.17/1.00  --inst_lit_sel_side                     none
% 4.17/1.00  --inst_solver_per_active                1400
% 4.17/1.00  --inst_solver_calls_frac                1.
% 4.17/1.00  --inst_passive_queue_type               priority_queues
% 4.17/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.17/1.00  --inst_passive_queues_freq              [25;2]
% 4.17/1.00  --inst_dismatching                      true
% 4.17/1.00  --inst_eager_unprocessed_to_passive     true
% 4.17/1.00  --inst_prop_sim_given                   true
% 4.17/1.00  --inst_prop_sim_new                     false
% 4.17/1.00  --inst_subs_new                         false
% 4.17/1.00  --inst_eq_res_simp                      false
% 4.17/1.00  --inst_subs_given                       false
% 4.17/1.00  --inst_orphan_elimination               true
% 4.17/1.00  --inst_learning_loop_flag               true
% 4.17/1.00  --inst_learning_start                   3000
% 4.17/1.00  --inst_learning_factor                  2
% 4.17/1.00  --inst_start_prop_sim_after_learn       3
% 4.17/1.00  --inst_sel_renew                        solver
% 4.17/1.00  --inst_lit_activity_flag                true
% 4.17/1.00  --inst_restr_to_given                   false
% 4.17/1.00  --inst_activity_threshold               500
% 4.17/1.00  --inst_out_proof                        true
% 4.17/1.00  
% 4.17/1.00  ------ Resolution Options
% 4.17/1.00  
% 4.17/1.00  --resolution_flag                       false
% 4.17/1.00  --res_lit_sel                           adaptive
% 4.17/1.00  --res_lit_sel_side                      none
% 4.17/1.00  --res_ordering                          kbo
% 4.17/1.00  --res_to_prop_solver                    active
% 4.17/1.00  --res_prop_simpl_new                    false
% 4.17/1.00  --res_prop_simpl_given                  true
% 4.17/1.00  --res_passive_queue_type                priority_queues
% 4.17/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.17/1.00  --res_passive_queues_freq               [15;5]
% 4.17/1.00  --res_forward_subs                      full
% 4.17/1.00  --res_backward_subs                     full
% 4.17/1.00  --res_forward_subs_resolution           true
% 4.17/1.00  --res_backward_subs_resolution          true
% 4.17/1.00  --res_orphan_elimination                true
% 4.17/1.00  --res_time_limit                        2.
% 4.17/1.00  --res_out_proof                         true
% 4.17/1.00  
% 4.17/1.00  ------ Superposition Options
% 4.17/1.00  
% 4.17/1.00  --superposition_flag                    true
% 4.17/1.00  --sup_passive_queue_type                priority_queues
% 4.17/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.17/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.17/1.00  --demod_completeness_check              fast
% 4.17/1.00  --demod_use_ground                      true
% 4.17/1.00  --sup_to_prop_solver                    passive
% 4.17/1.00  --sup_prop_simpl_new                    true
% 4.17/1.00  --sup_prop_simpl_given                  true
% 4.17/1.00  --sup_fun_splitting                     true
% 4.17/1.00  --sup_smt_interval                      50000
% 4.17/1.00  
% 4.17/1.00  ------ Superposition Simplification Setup
% 4.17/1.00  
% 4.17/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.17/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.17/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.17/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.17/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.17/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.17/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.17/1.00  --sup_immed_triv                        [TrivRules]
% 4.17/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.17/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.17/1.00  --sup_immed_bw_main                     []
% 4.17/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.17/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.17/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.17/1.00  --sup_input_bw                          []
% 4.17/1.00  
% 4.17/1.00  ------ Combination Options
% 4.17/1.00  
% 4.17/1.00  --comb_res_mult                         3
% 4.17/1.00  --comb_sup_mult                         2
% 4.17/1.00  --comb_inst_mult                        10
% 4.17/1.00  
% 4.17/1.00  ------ Debug Options
% 4.17/1.00  
% 4.17/1.00  --dbg_backtrace                         false
% 4.17/1.00  --dbg_dump_prop_clauses                 false
% 4.17/1.00  --dbg_dump_prop_clauses_file            -
% 4.17/1.00  --dbg_out_stat                          false
% 4.17/1.00  
% 4.17/1.00  
% 4.17/1.00  
% 4.17/1.00  
% 4.17/1.00  ------ Proving...
% 4.17/1.00  
% 4.17/1.00  
% 4.17/1.00  % SZS status Theorem for theBenchmark.p
% 4.17/1.00  
% 4.17/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.17/1.00  
% 4.17/1.00  fof(f11,axiom,(
% 4.17/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f47,plain,(
% 4.17/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f11])).
% 4.17/1.00  
% 4.17/1.00  fof(f13,axiom,(
% 4.17/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f49,plain,(
% 4.17/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.17/1.00    inference(cnf_transformation,[],[f13])).
% 4.17/1.00  
% 4.17/1.00  fof(f2,axiom,(
% 4.17/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f36,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f2])).
% 4.17/1.00  
% 4.17/1.00  fof(f14,axiom,(
% 4.17/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f50,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.17/1.00    inference(cnf_transformation,[],[f14])).
% 4.17/1.00  
% 4.17/1.00  fof(f59,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 4.17/1.00    inference(definition_unfolding,[],[f36,f50,f50])).
% 4.17/1.00  
% 4.17/1.00  fof(f17,axiom,(
% 4.17/1.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 4.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f55,plain,(
% 4.17/1.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f17])).
% 4.17/1.00  
% 4.17/1.00  fof(f4,axiom,(
% 4.17/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 4.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f21,plain,(
% 4.17/1.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 4.17/1.00    inference(ennf_transformation,[],[f4])).
% 4.17/1.00  
% 4.17/1.00  fof(f39,plain,(
% 4.17/1.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f21])).
% 4.17/1.00  
% 4.17/1.00  fof(f3,axiom,(
% 4.17/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 4.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f28,plain,(
% 4.17/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 4.17/1.00    inference(nnf_transformation,[],[f3])).
% 4.17/1.00  
% 4.17/1.00  fof(f37,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f28])).
% 4.17/1.00  
% 4.17/1.00  fof(f61,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 4.17/1.00    inference(definition_unfolding,[],[f37,f50])).
% 4.17/1.00  
% 4.17/1.00  fof(f12,axiom,(
% 4.17/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f48,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.17/1.00    inference(cnf_transformation,[],[f12])).
% 4.17/1.00  
% 4.17/1.00  fof(f9,axiom,(
% 4.17/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f45,plain,(
% 4.17/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.17/1.00    inference(cnf_transformation,[],[f9])).
% 4.17/1.00  
% 4.17/1.00  fof(f1,axiom,(
% 4.17/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f35,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f1])).
% 4.17/1.00  
% 4.17/1.00  fof(f16,axiom,(
% 4.17/1.00    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 4.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f26,plain,(
% 4.17/1.00    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 4.17/1.00    inference(ennf_transformation,[],[f16])).
% 4.17/1.00  
% 4.17/1.00  fof(f53,plain,(
% 4.17/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f26])).
% 4.17/1.00  
% 4.17/1.00  fof(f10,axiom,(
% 4.17/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f25,plain,(
% 4.17/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.17/1.00    inference(ennf_transformation,[],[f10])).
% 4.17/1.00  
% 4.17/1.00  fof(f46,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f25])).
% 4.17/1.00  
% 4.17/1.00  fof(f64,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 4.17/1.00    inference(definition_unfolding,[],[f46,f50])).
% 4.17/1.00  
% 4.17/1.00  fof(f7,axiom,(
% 4.17/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f43,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.17/1.00    inference(cnf_transformation,[],[f7])).
% 4.17/1.00  
% 4.17/1.00  fof(f58,plain,(
% 4.17/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 4.17/1.00    inference(definition_unfolding,[],[f43,f50])).
% 4.17/1.00  
% 4.17/1.00  fof(f18,conjecture,(
% 4.17/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 4.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f19,negated_conjecture,(
% 4.17/1.00    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 4.17/1.00    inference(negated_conjecture,[],[f18])).
% 4.17/1.00  
% 4.17/1.00  fof(f27,plain,(
% 4.17/1.00    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 4.17/1.00    inference(ennf_transformation,[],[f19])).
% 4.17/1.00  
% 4.17/1.00  fof(f33,plain,(
% 4.17/1.00    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)) & r1_tarski(sK2,k4_xboole_0(sK3,sK4)))),
% 4.17/1.00    introduced(choice_axiom,[])).
% 4.17/1.00  
% 4.17/1.00  fof(f34,plain,(
% 4.17/1.00    (~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)) & r1_tarski(sK2,k4_xboole_0(sK3,sK4))),
% 4.17/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f33])).
% 4.17/1.00  
% 4.17/1.00  fof(f56,plain,(
% 4.17/1.00    r1_tarski(sK2,k4_xboole_0(sK3,sK4))),
% 4.17/1.00    inference(cnf_transformation,[],[f34])).
% 4.17/1.00  
% 4.17/1.00  fof(f8,axiom,(
% 4.17/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 4.17/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.17/1.00  
% 4.17/1.00  fof(f24,plain,(
% 4.17/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 4.17/1.00    inference(ennf_transformation,[],[f8])).
% 4.17/1.00  
% 4.17/1.00  fof(f44,plain,(
% 4.17/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f24])).
% 4.17/1.00  
% 4.17/1.00  fof(f54,plain,(
% 4.17/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 4.17/1.00    inference(cnf_transformation,[],[f26])).
% 4.17/1.00  
% 4.17/1.00  fof(f57,plain,(
% 4.17/1.00    ~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)),
% 4.17/1.00    inference(cnf_transformation,[],[f34])).
% 4.17/1.00  
% 4.17/1.00  cnf(c_12,plain,
% 4.17/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 4.17/1.00      inference(cnf_transformation,[],[f47]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_654,plain,
% 4.17/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_14,plain,
% 4.17/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.17/1.00      inference(cnf_transformation,[],[f49]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_2,plain,
% 4.17/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.17/1.00      inference(cnf_transformation,[],[f59]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1064,plain,
% 4.17/1.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_14,c_2]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_19,plain,
% 4.17/1.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 4.17/1.00      inference(cnf_transformation,[],[f55]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_649,plain,
% 4.17/1.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1071,plain,
% 4.17/1.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_2,c_649]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1538,plain,
% 4.17/1.00      ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_1064,c_1071]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1545,plain,
% 4.17/1.00      ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,X0)) = iProver_top ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_1538,c_14]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_5,plain,
% 4.17/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 4.17/1.00      inference(cnf_transformation,[],[f39]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_660,plain,
% 4.17/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 4.17/1.00      | r1_xboole_0(X1,X0) = iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_2020,plain,
% 4.17/1.00      ( r1_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_1545,c_660]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_4,plain,
% 4.17/1.00      ( ~ r1_xboole_0(X0,X1)
% 4.17/1.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 4.17/1.00      inference(cnf_transformation,[],[f61]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_661,plain,
% 4.17/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 4.17/1.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_6759,plain,
% 4.17/1.00      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)))) = k1_xboole_0 ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_2020,c_661]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_13,plain,
% 4.17/1.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 4.17/1.00      inference(cnf_transformation,[],[f48]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1206,plain,
% 4.17/1.00      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_1064,c_13]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_10,plain,
% 4.17/1.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.17/1.00      inference(cnf_transformation,[],[f45]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1214,plain,
% 4.17/1.00      ( k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_1206,c_10]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1,plain,
% 4.17/1.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 4.17/1.00      inference(cnf_transformation,[],[f35]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1762,plain,
% 4.17/1.00      ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_1214,c_1]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_17,plain,
% 4.17/1.00      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 4.17/1.00      inference(cnf_transformation,[],[f53]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_651,plain,
% 4.17/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 4.17/1.00      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) != iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_2165,plain,
% 4.17/1.00      ( r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X1) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_649,c_651]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_2776,plain,
% 4.17/1.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)),k4_xboole_0(X1,X1)) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_1762,c_2165]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_3813,plain,
% 4.17/1.00      ( r1_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_1064,c_2776]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_6780,plain,
% 4.17/1.00      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) = k1_xboole_0 ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_3813,c_661]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1201,plain,
% 4.17/1.00      ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_1064,c_654]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_11,plain,
% 4.17/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 4.17/1.00      inference(cnf_transformation,[],[f64]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_655,plain,
% 4.17/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 4.17/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_4091,plain,
% 4.17/1.00      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_1201,c_655]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_4094,plain,
% 4.17/1.00      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_4091,c_14]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_6807,plain,
% 4.17/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.17/1.00      inference(light_normalisation,[status(thm)],[c_6780,c_4094]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_6810,plain,
% 4.17/1.00      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = k1_xboole_0 ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_6759,c_6807]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_4087,plain,
% 4.17/1.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_654,c_655]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_6811,plain,
% 4.17/1.00      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_6810,c_14,c_4087]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_0,plain,
% 4.17/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 4.17/1.00      inference(cnf_transformation,[],[f58]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1072,plain,
% 4.17/1.00      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_7139,plain,
% 4.17/1.00      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_6811,c_1072]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_7187,plain,
% 4.17/1.00      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0)) = k1_xboole_0 ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_7139,c_6811]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1567,plain,
% 4.17/1.00      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_1064,c_1072]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1568,plain,
% 4.17/1.00      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_1567,c_14]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_4258,plain,
% 4.17/1.00      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)),k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_4094,c_1568]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1205,plain,
% 4.17/1.00      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_1064,c_0]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_4264,plain,
% 4.17/1.00      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_4094,c_1205]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_4271,plain,
% 4.17/1.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 4.17/1.00      inference(light_normalisation,[status(thm)],[c_4264,c_1205]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_4279,plain,
% 4.17/1.00      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_4258,c_4271]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_7188,plain,
% 4.17/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_7187,c_14,c_4279]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_1209,plain,
% 4.17/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) = k4_xboole_0(X0,X0) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_1064,c_0]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_7197,plain,
% 4.17/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) = k4_xboole_0(X0,X0) ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_7188,c_1209]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_7240,plain,
% 4.17/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) = k1_xboole_0 ),
% 4.17/1.00      inference(light_normalisation,[status(thm)],[c_7197,c_6807]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_7241,plain,
% 4.17/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_7240,c_14,c_7188]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_21,negated_conjecture,
% 4.17/1.00      ( r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
% 4.17/1.00      inference(cnf_transformation,[],[f56]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_647,plain,
% 4.17/1.00      ( r1_tarski(sK2,k4_xboole_0(sK3,sK4)) = iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_4088,plain,
% 4.17/1.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = sK2 ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_647,c_655]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_4636,plain,
% 4.17/1.00      ( k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k5_xboole_0(sK2,sK2) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_4088,c_0]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_4855,plain,
% 4.17/1.00      ( k2_xboole_0(k4_xboole_0(sK3,sK4),k5_xboole_0(sK2,sK2)) = k2_xboole_0(k4_xboole_0(sK3,sK4),sK2) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_4636,c_13]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_7588,plain,
% 4.17/1.00      ( k2_xboole_0(k4_xboole_0(sK3,sK4),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK3,sK4),sK2) ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_7241,c_4855]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_7602,plain,
% 4.17/1.00      ( k2_xboole_0(k4_xboole_0(sK3,sK4),sK2) = k4_xboole_0(sK3,sK4) ),
% 4.17/1.00      inference(demodulation,[status(thm)],[c_7588,c_10]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_8030,plain,
% 4.17/1.00      ( k2_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK3,sK4) ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_7602,c_1]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_9,plain,
% 4.17/1.00      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 4.17/1.00      inference(cnf_transformation,[],[f44]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_656,plain,
% 4.17/1.00      ( r1_tarski(X0,X1) = iProver_top
% 4.17/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_8090,plain,
% 4.17/1.00      ( r1_tarski(k4_xboole_0(sK3,sK4),X0) != iProver_top
% 4.17/1.00      | r1_tarski(sK2,X0) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_8030,c_656]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_16674,plain,
% 4.17/1.00      ( r1_tarski(sK2,sK3) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_654,c_8090]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_2016,plain,
% 4.17/1.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_649,c_660]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_16,plain,
% 4.17/1.00      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 4.17/1.00      inference(cnf_transformation,[],[f54]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_652,plain,
% 4.17/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 4.17/1.00      | r1_xboole_0(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_8044,plain,
% 4.17/1.00      ( r1_xboole_0(X0,k4_xboole_0(sK3,sK4)) != iProver_top
% 4.17/1.00      | r1_xboole_0(X0,sK2) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_7602,c_652]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_13745,plain,
% 4.17/1.00      ( r1_xboole_0(sK4,sK2) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_2016,c_8044]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_15377,plain,
% 4.17/1.00      ( r1_xboole_0(sK2,sK4) = iProver_top ),
% 4.17/1.00      inference(superposition,[status(thm)],[c_13745,c_660]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_20,negated_conjecture,
% 4.17/1.00      ( ~ r1_tarski(sK2,sK3) | ~ r1_xboole_0(sK2,sK4) ),
% 4.17/1.00      inference(cnf_transformation,[],[f57]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(c_23,plain,
% 4.17/1.00      ( r1_tarski(sK2,sK3) != iProver_top
% 4.17/1.00      | r1_xboole_0(sK2,sK4) != iProver_top ),
% 4.17/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.17/1.00  
% 4.17/1.00  cnf(contradiction,plain,
% 4.17/1.00      ( $false ),
% 4.17/1.00      inference(minisat,[status(thm)],[c_16674,c_15377,c_23]) ).
% 4.17/1.00  
% 4.17/1.00  
% 4.17/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.17/1.00  
% 4.17/1.00  ------                               Statistics
% 4.17/1.00  
% 4.17/1.00  ------ General
% 4.17/1.00  
% 4.17/1.00  abstr_ref_over_cycles:                  0
% 4.17/1.00  abstr_ref_under_cycles:                 0
% 4.17/1.00  gc_basic_clause_elim:                   0
% 4.17/1.00  forced_gc_time:                         0
% 4.17/1.00  parsing_time:                           0.006
% 4.17/1.00  unif_index_cands_time:                  0.
% 4.17/1.00  unif_index_add_time:                    0.
% 4.17/1.00  orderings_time:                         0.
% 4.17/1.00  out_proof_time:                         0.01
% 4.17/1.00  total_time:                             0.433
% 4.17/1.00  num_of_symbols:                         43
% 4.17/1.00  num_of_terms:                           15822
% 4.17/1.00  
% 4.17/1.00  ------ Preprocessing
% 4.17/1.00  
% 4.17/1.00  num_of_splits:                          0
% 4.17/1.00  num_of_split_atoms:                     0
% 4.17/1.00  num_of_reused_defs:                     0
% 4.17/1.00  num_eq_ax_congr_red:                    10
% 4.17/1.00  num_of_sem_filtered_clauses:            1
% 4.17/1.00  num_of_subtypes:                        0
% 4.17/1.00  monotx_restored_types:                  0
% 4.17/1.00  sat_num_of_epr_types:                   0
% 4.17/1.00  sat_num_of_non_cyclic_types:            0
% 4.17/1.00  sat_guarded_non_collapsed_types:        0
% 4.17/1.00  num_pure_diseq_elim:                    0
% 4.17/1.00  simp_replaced_by:                       0
% 4.17/1.00  res_preprocessed:                       83
% 4.17/1.00  prep_upred:                             0
% 4.17/1.00  prep_unflattend:                        3
% 4.17/1.00  smt_new_axioms:                         0
% 4.17/1.00  pred_elim_cands:                        3
% 4.17/1.00  pred_elim:                              0
% 4.17/1.00  pred_elim_cl:                           0
% 4.17/1.00  pred_elim_cycles:                       1
% 4.17/1.00  merged_defs:                            6
% 4.17/1.00  merged_defs_ncl:                        0
% 4.17/1.00  bin_hyper_res:                          6
% 4.17/1.00  prep_cycles:                            3
% 4.17/1.00  pred_elim_time:                         0.
% 4.17/1.00  splitting_time:                         0.
% 4.17/1.00  sem_filter_time:                        0.
% 4.17/1.00  monotx_time:                            0.
% 4.17/1.00  subtype_inf_time:                       0.
% 4.17/1.00  
% 4.17/1.00  ------ Problem properties
% 4.17/1.00  
% 4.17/1.00  clauses:                                22
% 4.17/1.00  conjectures:                            2
% 4.17/1.00  epr:                                    3
% 4.17/1.00  horn:                                   20
% 4.17/1.00  ground:                                 2
% 4.17/1.00  unary:                                  10
% 4.17/1.00  binary:                                 11
% 4.17/1.00  lits:                                   35
% 4.17/1.00  lits_eq:                                10
% 4.17/1.00  fd_pure:                                0
% 4.17/1.00  fd_pseudo:                              0
% 4.17/1.00  fd_cond:                                1
% 4.17/1.00  fd_pseudo_cond:                         0
% 4.17/1.00  ac_symbols:                             0
% 4.17/1.00  
% 4.17/1.00  ------ Propositional Solver
% 4.17/1.00  
% 4.17/1.00  prop_solver_calls:                      29
% 4.17/1.00  prop_fast_solver_calls:                 645
% 4.17/1.00  smt_solver_calls:                       0
% 4.17/1.00  smt_fast_solver_calls:                  0
% 4.17/1.00  prop_num_of_clauses:                    6336
% 4.17/1.00  prop_preprocess_simplified:             12538
% 4.17/1.00  prop_fo_subsumed:                       2
% 4.17/1.00  prop_solver_time:                       0.
% 4.17/1.00  smt_solver_time:                        0.
% 4.17/1.00  smt_fast_solver_time:                   0.
% 4.17/1.00  prop_fast_solver_time:                  0.
% 4.17/1.00  prop_unsat_core_time:                   0.
% 4.17/1.00  
% 4.17/1.00  ------ QBF
% 4.17/1.00  
% 4.17/1.00  qbf_q_res:                              0
% 4.17/1.00  qbf_num_tautologies:                    0
% 4.17/1.00  qbf_prep_cycles:                        0
% 4.17/1.00  
% 4.17/1.00  ------ BMC1
% 4.17/1.00  
% 4.17/1.00  bmc1_current_bound:                     -1
% 4.17/1.00  bmc1_last_solved_bound:                 -1
% 4.17/1.00  bmc1_unsat_core_size:                   -1
% 4.17/1.00  bmc1_unsat_core_parents_size:           -1
% 4.17/1.00  bmc1_merge_next_fun:                    0
% 4.17/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.17/1.00  
% 4.17/1.00  ------ Instantiation
% 4.17/1.00  
% 4.17/1.00  inst_num_of_clauses:                    2207
% 4.17/1.00  inst_num_in_passive:                    457
% 4.17/1.00  inst_num_in_active:                     906
% 4.17/1.00  inst_num_in_unprocessed:                844
% 4.17/1.00  inst_num_of_loops:                      990
% 4.17/1.00  inst_num_of_learning_restarts:          0
% 4.17/1.00  inst_num_moves_active_passive:          79
% 4.17/1.00  inst_lit_activity:                      0
% 4.17/1.00  inst_lit_activity_moves:                0
% 4.17/1.00  inst_num_tautologies:                   0
% 4.17/1.00  inst_num_prop_implied:                  0
% 4.17/1.00  inst_num_existing_simplified:           0
% 4.17/1.00  inst_num_eq_res_simplified:             0
% 4.17/1.00  inst_num_child_elim:                    0
% 4.17/1.00  inst_num_of_dismatching_blockings:      1407
% 4.17/1.00  inst_num_of_non_proper_insts:           2662
% 4.17/1.00  inst_num_of_duplicates:                 0
% 4.17/1.00  inst_inst_num_from_inst_to_res:         0
% 4.17/1.00  inst_dismatching_checking_time:         0.
% 4.17/1.00  
% 4.17/1.00  ------ Resolution
% 4.17/1.00  
% 4.17/1.00  res_num_of_clauses:                     0
% 4.17/1.00  res_num_in_passive:                     0
% 4.17/1.00  res_num_in_active:                      0
% 4.17/1.00  res_num_of_loops:                       86
% 4.17/1.00  res_forward_subset_subsumed:            397
% 4.17/1.00  res_backward_subset_subsumed:           2
% 4.17/1.00  res_forward_subsumed:                   0
% 4.17/1.00  res_backward_subsumed:                  0
% 4.17/1.00  res_forward_subsumption_resolution:     0
% 4.17/1.00  res_backward_subsumption_resolution:    0
% 4.17/1.00  res_clause_to_clause_subsumption:       9716
% 4.17/1.00  res_orphan_elimination:                 0
% 4.17/1.00  res_tautology_del:                      398
% 4.17/1.00  res_num_eq_res_simplified:              0
% 4.17/1.00  res_num_sel_changes:                    0
% 4.17/1.00  res_moves_from_active_to_pass:          0
% 4.17/1.00  
% 4.17/1.00  ------ Superposition
% 4.17/1.00  
% 4.17/1.00  sup_time_total:                         0.
% 4.17/1.00  sup_time_generating:                    0.
% 4.17/1.00  sup_time_sim_full:                      0.
% 4.17/1.00  sup_time_sim_immed:                     0.
% 4.17/1.00  
% 4.17/1.00  sup_num_of_clauses:                     599
% 4.17/1.00  sup_num_in_active:                      130
% 4.17/1.00  sup_num_in_passive:                     469
% 4.17/1.00  sup_num_of_loops:                       196
% 4.17/1.00  sup_fw_superposition:                   1340
% 4.17/1.00  sup_bw_superposition:                   1088
% 4.17/1.00  sup_immediate_simplified:               966
% 4.17/1.00  sup_given_eliminated:                   5
% 4.17/1.00  comparisons_done:                       0
% 4.17/1.00  comparisons_avoided:                    0
% 4.17/1.00  
% 4.17/1.00  ------ Simplifications
% 4.17/1.00  
% 4.17/1.00  
% 4.17/1.00  sim_fw_subset_subsumed:                 24
% 4.17/1.00  sim_bw_subset_subsumed:                 2
% 4.17/1.00  sim_fw_subsumed:                        356
% 4.17/1.00  sim_bw_subsumed:                        6
% 4.17/1.00  sim_fw_subsumption_res:                 0
% 4.17/1.00  sim_bw_subsumption_res:                 0
% 4.17/1.00  sim_tautology_del:                      49
% 4.17/1.00  sim_eq_tautology_del:                   57
% 4.17/1.00  sim_eq_res_simp:                        1
% 4.17/1.00  sim_fw_demodulated:                     680
% 4.17/1.00  sim_bw_demodulated:                     93
% 4.17/1.00  sim_light_normalised:                   526
% 4.17/1.00  sim_joinable_taut:                      0
% 4.17/1.00  sim_joinable_simp:                      0
% 4.17/1.00  sim_ac_normalised:                      0
% 4.17/1.00  sim_smt_subsumption:                    0
% 4.17/1.00  
%------------------------------------------------------------------------------
