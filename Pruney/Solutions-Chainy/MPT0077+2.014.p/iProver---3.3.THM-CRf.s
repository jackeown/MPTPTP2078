%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:38 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 942 expanded)
%              Number of clauses        :   97 ( 367 expanded)
%              Number of leaves         :   15 ( 227 expanded)
%              Depth                    :   27
%              Number of atoms          :  230 (1899 expanded)
%              Number of equality atoms :  112 ( 609 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
        & ( ~ r1_xboole_0(sK1,sK3)
          | ~ r1_xboole_0(sK1,sK2) ) )
      | ( r1_xboole_0(sK1,sK3)
        & r1_xboole_0(sK1,sK2)
        & ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
      & ( ~ r1_xboole_0(sK1,sK3)
        | ~ r1_xboole_0(sK1,sK2) ) )
    | ( r1_xboole_0(sK1,sK3)
      & r1_xboole_0(sK1,sK2)
      & ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f26])).

fof(f49,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f39])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ r1_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_10,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_896,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_10])).

cnf(c_1923,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_896,c_8])).

cnf(c_1928,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1923,c_8])).

cnf(c_2725,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1928,c_10])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_539,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_9])).

cnf(c_2736,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2725,c_539])).

cnf(c_2786,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_2736])).

cnf(c_2848,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2786,c_8])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2854,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2848,c_6])).

cnf(c_4126,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_2854])).

cnf(c_4985,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_8,c_4126])).

cnf(c_5054,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_4985,c_4126])).

cnf(c_6334,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5054,c_896])).

cnf(c_12,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1096,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_12,c_8])).

cnf(c_1101,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_1096,c_9,c_539])).

cnf(c_1619,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_1101,c_0])).

cnf(c_2808,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_2736,c_12])).

cnf(c_2810,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2808,c_9,c_1101])).

cnf(c_3454,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1619,c_2810])).

cnf(c_6368,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_6334,c_3454])).

cnf(c_6748,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_10,c_6368])).

cnf(c_900,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_8])).

cnf(c_902,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_900,c_8])).

cnf(c_2727,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1928,c_902])).

cnf(c_861,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_539,c_8])).

cnf(c_862,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_861,c_6])).

cnf(c_2731,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2727,c_862])).

cnf(c_3880,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_2731])).

cnf(c_6854,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6748,c_3880])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_525,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top
    | r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_530,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8204,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) = iProver_top
    | r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_525,c_530])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_830,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2459,plain,
    ( r1_xboole_0(sK1,sK3)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2460,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k1_xboole_0
    | r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2459])).

cnf(c_247,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_1958,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(resolution,[status(thm)],[c_247,c_0])).

cnf(c_14,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2601,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(resolution,[status(thm)],[c_1958,c_14])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_663,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1)
    | r1_xboole_0(sK1,sK3) ),
    inference(resolution,[status(thm)],[c_3,c_15])).

cnf(c_808,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(sK2,sK3))
    | r1_xboole_0(X0,sK1)
    | r1_xboole_0(sK1,sK3) ),
    inference(resolution,[status(thm)],[c_13,c_663])).

cnf(c_2611,plain,
    ( r1_xboole_0(sK3,sK1)
    | r1_xboole_0(sK1,sK3) ),
    inference(resolution,[status(thm)],[c_2601,c_808])).

cnf(c_2475,plain,
    ( ~ r1_xboole_0(sK3,sK1)
    | r1_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2748,plain,
    ( r1_xboole_0(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2611,c_2475])).

cnf(c_9145,plain,
    ( r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8204,c_830,c_2460,c_2475,c_2611])).

cnf(c_531,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10322,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9145,c_531])).

cnf(c_10766,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
    inference(superposition,[status(thm)],[c_10322,c_8])).

cnf(c_10784,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_10766,c_6,c_1101])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_524,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8205,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) = iProver_top
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_524,c_530])).

cnf(c_888,plain,
    ( r1_xboole_0(sK2,sK1)
    | r1_xboole_0(sK1,sK3) ),
    inference(resolution,[status(thm)],[c_808,c_14])).

cnf(c_842,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_664,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1)
    | r1_xboole_0(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_3,c_16])).

cnf(c_809,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(sK2,sK3))
    | r1_xboole_0(X0,sK1)
    | r1_xboole_0(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_13,c_664])).

cnf(c_1169,plain,
    ( r1_xboole_0(sK2,sK1)
    | r1_xboole_0(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_809,c_14])).

cnf(c_1277,plain,
    ( r1_xboole_0(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_888,c_842,c_1169])).

cnf(c_1289,plain,
    ( r1_xboole_0(sK1,sK2) ),
    inference(resolution,[status(thm)],[c_1277,c_3])).

cnf(c_1290,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1289])).

cnf(c_9153,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8205,c_1290])).

cnf(c_10325,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9153,c_531])).

cnf(c_10963,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,sK2)) = k2_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10325,c_12])).

cnf(c_11541,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_10963,c_6])).

cnf(c_1913,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_8,c_896])).

cnf(c_1942,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1913,c_896])).

cnf(c_13401,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(X0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(X0,sK2)) ),
    inference(superposition,[status(thm)],[c_11541,c_1942])).

cnf(c_13478,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(X0,sK2)) = k4_xboole_0(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_13401,c_11541])).

cnf(c_19039,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_10784,c_13478])).

cnf(c_19199,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK3,sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_19039,c_10784])).

cnf(c_20234,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(sK3,sK2))) = k2_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_19199,c_12])).

cnf(c_20267,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(sK3,sK2))) = k4_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_20234,c_6,c_539])).

cnf(c_25165,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_6854,c_20267])).

cnf(c_10961,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_10325,c_8])).

cnf(c_10979,plain,
    ( k4_xboole_0(sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_10961,c_6,c_1101])).

cnf(c_25339,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_25165,c_10979])).

cnf(c_532,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_26023,plain,
    ( k4_xboole_0(sK1,sK1) != k1_xboole_0
    | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_25339,c_532])).

cnf(c_26134,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_26023,c_539])).

cnf(c_26135,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_26134])).

cnf(c_743,plain,
    ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_639,plain,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_640,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) = k1_xboole_0
    | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_20,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
    | ~ r1_xboole_0(sK1,sK3)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26135,c_2748,c_1289,c_743,c_640,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.59/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/1.50  
% 7.59/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.59/1.50  
% 7.59/1.50  ------  iProver source info
% 7.59/1.50  
% 7.59/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.59/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.59/1.50  git: non_committed_changes: false
% 7.59/1.50  git: last_make_outside_of_git: false
% 7.59/1.50  
% 7.59/1.50  ------ 
% 7.59/1.50  ------ Parsing...
% 7.59/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.59/1.50  
% 7.59/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.59/1.50  
% 7.59/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.59/1.50  
% 7.59/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.59/1.50  ------ Proving...
% 7.59/1.50  ------ Problem Properties 
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  clauses                                 18
% 7.59/1.50  conjectures                             3
% 7.59/1.50  EPR                                     2
% 7.59/1.50  Horn                                    15
% 7.59/1.50  unary                                   9
% 7.59/1.50  binary                                  7
% 7.59/1.50  lits                                    29
% 7.59/1.50  lits eq                                 10
% 7.59/1.50  fd_pure                                 0
% 7.59/1.50  fd_pseudo                               0
% 7.59/1.50  fd_cond                                 0
% 7.59/1.50  fd_pseudo_cond                          0
% 7.59/1.50  AC symbols                              0
% 7.59/1.50  
% 7.59/1.50  ------ Input Options Time Limit: Unbounded
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  ------ 
% 7.59/1.50  Current options:
% 7.59/1.50  ------ 
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  ------ Proving...
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  % SZS status Theorem for theBenchmark.p
% 7.59/1.50  
% 7.59/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.59/1.50  
% 7.59/1.50  fof(f9,axiom,(
% 7.59/1.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f38,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f9])).
% 7.59/1.50  
% 7.59/1.50  fof(f7,axiom,(
% 7.59/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f36,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.59/1.50    inference(cnf_transformation,[],[f7])).
% 7.59/1.50  
% 7.59/1.50  fof(f1,axiom,(
% 7.59/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f28,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f1])).
% 7.59/1.50  
% 7.59/1.50  fof(f6,axiom,(
% 7.59/1.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f35,plain,(
% 7.59/1.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.59/1.50    inference(cnf_transformation,[],[f6])).
% 7.59/1.50  
% 7.59/1.50  fof(f10,axiom,(
% 7.59/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f39,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.59/1.50    inference(cnf_transformation,[],[f10])).
% 7.59/1.50  
% 7.59/1.50  fof(f54,plain,(
% 7.59/1.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.59/1.50    inference(definition_unfolding,[],[f35,f39])).
% 7.59/1.50  
% 7.59/1.50  fof(f8,axiom,(
% 7.59/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f37,plain,(
% 7.59/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.59/1.50    inference(cnf_transformation,[],[f8])).
% 7.59/1.50  
% 7.59/1.50  fof(f5,axiom,(
% 7.59/1.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f34,plain,(
% 7.59/1.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.59/1.50    inference(cnf_transformation,[],[f5])).
% 7.59/1.50  
% 7.59/1.50  fof(f12,axiom,(
% 7.59/1.50    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f41,plain,(
% 7.59/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 7.59/1.50    inference(cnf_transformation,[],[f12])).
% 7.59/1.50  
% 7.59/1.50  fof(f56,plain,(
% 7.59/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 7.59/1.50    inference(definition_unfolding,[],[f41,f39])).
% 7.59/1.50  
% 7.59/1.50  fof(f15,conjecture,(
% 7.59/1.50    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f16,negated_conjecture,(
% 7.59/1.50    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.59/1.50    inference(negated_conjecture,[],[f15])).
% 7.59/1.50  
% 7.59/1.50  fof(f22,plain,(
% 7.59/1.50    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 7.59/1.50    inference(ennf_transformation,[],[f16])).
% 7.59/1.50  
% 7.59/1.50  fof(f26,plain,(
% 7.59/1.50    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) & (~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2))) | (r1_xboole_0(sK1,sK3) & r1_xboole_0(sK1,sK2) & ~r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))))),
% 7.59/1.50    introduced(choice_axiom,[])).
% 7.59/1.50  
% 7.59/1.50  fof(f27,plain,(
% 7.59/1.50    (r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) & (~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2))) | (r1_xboole_0(sK1,sK3) & r1_xboole_0(sK1,sK2) & ~r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)))),
% 7.59/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f26])).
% 7.59/1.50  
% 7.59/1.50  fof(f49,plain,(
% 7.59/1.50    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | r1_xboole_0(sK1,sK3)),
% 7.59/1.50    inference(cnf_transformation,[],[f27])).
% 7.59/1.50  
% 7.59/1.50  fof(f3,axiom,(
% 7.59/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f18,plain,(
% 7.59/1.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.59/1.50    inference(ennf_transformation,[],[f3])).
% 7.59/1.50  
% 7.59/1.50  fof(f31,plain,(
% 7.59/1.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f18])).
% 7.59/1.50  
% 7.59/1.50  fof(f2,axiom,(
% 7.59/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f23,plain,(
% 7.59/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.59/1.50    inference(nnf_transformation,[],[f2])).
% 7.59/1.50  
% 7.59/1.50  fof(f29,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f23])).
% 7.59/1.50  
% 7.59/1.50  fof(f51,plain,(
% 7.59/1.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.59/1.50    inference(definition_unfolding,[],[f29,f39])).
% 7.59/1.50  
% 7.59/1.50  fof(f30,plain,(
% 7.59/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.59/1.50    inference(cnf_transformation,[],[f23])).
% 7.59/1.50  
% 7.59/1.50  fof(f50,plain,(
% 7.59/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.59/1.50    inference(definition_unfolding,[],[f30,f39])).
% 7.59/1.50  
% 7.59/1.50  fof(f14,axiom,(
% 7.59/1.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f43,plain,(
% 7.59/1.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.59/1.50    inference(cnf_transformation,[],[f14])).
% 7.59/1.50  
% 7.59/1.50  fof(f13,axiom,(
% 7.59/1.50    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 7.59/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.50  
% 7.59/1.50  fof(f20,plain,(
% 7.59/1.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.59/1.50    inference(ennf_transformation,[],[f13])).
% 7.59/1.50  
% 7.59/1.50  fof(f21,plain,(
% 7.59/1.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 7.59/1.50    inference(flattening,[],[f20])).
% 7.59/1.50  
% 7.59/1.50  fof(f42,plain,(
% 7.59/1.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.59/1.50    inference(cnf_transformation,[],[f21])).
% 7.59/1.50  
% 7.59/1.50  fof(f48,plain,(
% 7.59/1.50    r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | r1_xboole_0(sK1,sK2)),
% 7.59/1.50    inference(cnf_transformation,[],[f27])).
% 7.59/1.50  
% 7.59/1.50  fof(f44,plain,(
% 7.59/1.50    ~r1_xboole_0(sK1,sK3) | ~r1_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))),
% 7.59/1.50    inference(cnf_transformation,[],[f27])).
% 7.59/1.50  
% 7.59/1.50  cnf(c_10,plain,
% 7.59/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.59/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_8,plain,
% 7.59/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.59/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_0,plain,
% 7.59/1.50      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f28]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_896,plain,
% 7.59/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_0,c_10]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1923,plain,
% 7.59/1.50      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_896,c_8]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1928,plain,
% 7.59/1.50      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_1923,c_8]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2725,plain,
% 7.59/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_1928,c_10]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_7,plain,
% 7.59/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.59/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_9,plain,
% 7.59/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.59/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_539,plain,
% 7.59/1.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_7,c_9]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2736,plain,
% 7.59/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_2725,c_539]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2786,plain,
% 7.59/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_0,c_2736]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2848,plain,
% 7.59/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_2786,c_8]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_6,plain,
% 7.59/1.50      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.59/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2854,plain,
% 7.59/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_2848,c_6]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_4126,plain,
% 7.59/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_0,c_2854]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_4985,plain,
% 7.59/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_8,c_4126]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_5054,plain,
% 7.59/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_4985,c_4126]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_6334,plain,
% 7.59/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_5054,c_896]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_12,plain,
% 7.59/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.59/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1096,plain,
% 7.59/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_12,c_8]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1101,plain,
% 7.59/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_1096,c_9,c_539]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1619,plain,
% 7.59/1.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_1101,c_0]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2808,plain,
% 7.59/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_2736,c_12]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2810,plain,
% 7.59/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = X0 ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_2808,c_9,c_1101]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3454,plain,
% 7.59/1.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_1619,c_2810]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_6368,plain,
% 7.59/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_6334,c_3454]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_6748,plain,
% 7.59/1.50      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = X1 ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_10,c_6368]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_900,plain,
% 7.59/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_10,c_8]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_902,plain,
% 7.59/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_900,c_8]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2727,plain,
% 7.59/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_1928,c_902]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_861,plain,
% 7.59/1.50      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_539,c_8]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_862,plain,
% 7.59/1.50      ( k2_xboole_0(X0,X0) = X0 ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_861,c_6]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2731,plain,
% 7.59/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_2727,c_862]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3880,plain,
% 7.59/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_0,c_2731]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_6854,plain,
% 7.59/1.50      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_6748,c_3880]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_15,negated_conjecture,
% 7.59/1.50      ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | r1_xboole_0(sK1,sK3) ),
% 7.59/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_525,plain,
% 7.59/1.50      ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top
% 7.59/1.50      | r1_xboole_0(sK1,sK3) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_3,plain,
% 7.59/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.59/1.50      inference(cnf_transformation,[],[f31]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_530,plain,
% 7.59/1.50      ( r1_xboole_0(X0,X1) != iProver_top
% 7.59/1.50      | r1_xboole_0(X1,X0) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_8204,plain,
% 7.59/1.50      ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) = iProver_top
% 7.59/1.50      | r1_xboole_0(sK1,sK3) = iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_525,c_530]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2,plain,
% 7.59/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.59/1.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.59/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_830,plain,
% 7.59/1.50      ( ~ r1_xboole_0(sK1,sK3)
% 7.59/1.50      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1,plain,
% 7.59/1.50      ( r1_xboole_0(X0,X1)
% 7.59/1.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 7.59/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2459,plain,
% 7.59/1.50      ( r1_xboole_0(sK1,sK3)
% 7.59/1.50      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k1_xboole_0 ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2460,plain,
% 7.59/1.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k1_xboole_0
% 7.59/1.50      | r1_xboole_0(sK1,sK3) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_2459]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_247,plain,
% 7.59/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X2) | X2 != X1 ),
% 7.59/1.50      theory(equality) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1958,plain,
% 7.59/1.50      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 7.59/1.50      | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 7.59/1.50      inference(resolution,[status(thm)],[c_247,c_0]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_14,plain,
% 7.59/1.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.59/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2601,plain,
% 7.59/1.50      ( r1_tarski(X0,k2_xboole_0(X1,X0)) ),
% 7.59/1.50      inference(resolution,[status(thm)],[c_1958,c_14]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_13,plain,
% 7.59/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 7.59/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_663,plain,
% 7.59/1.50      ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) | r1_xboole_0(sK1,sK3) ),
% 7.59/1.50      inference(resolution,[status(thm)],[c_3,c_15]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_808,plain,
% 7.59/1.50      ( ~ r1_tarski(X0,k2_xboole_0(sK2,sK3))
% 7.59/1.50      | r1_xboole_0(X0,sK1)
% 7.59/1.50      | r1_xboole_0(sK1,sK3) ),
% 7.59/1.50      inference(resolution,[status(thm)],[c_13,c_663]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2611,plain,
% 7.59/1.50      ( r1_xboole_0(sK3,sK1) | r1_xboole_0(sK1,sK3) ),
% 7.59/1.50      inference(resolution,[status(thm)],[c_2601,c_808]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2475,plain,
% 7.59/1.50      ( ~ r1_xboole_0(sK3,sK1) | r1_xboole_0(sK1,sK3) ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_2748,plain,
% 7.59/1.50      ( r1_xboole_0(sK1,sK3) ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_2611,c_2475]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_9145,plain,
% 7.59/1.50      ( r1_xboole_0(sK1,sK3) = iProver_top ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_8204,c_830,c_2460,c_2475,c_2611]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_531,plain,
% 7.59/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.59/1.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_10322,plain,
% 7.59/1.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_9145,c_531]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_10766,plain,
% 7.59/1.50      ( k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_10322,c_8]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_10784,plain,
% 7.59/1.50      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_10766,c_6,c_1101]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_16,negated_conjecture,
% 7.59/1.50      ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) | r1_xboole_0(sK1,sK2) ),
% 7.59/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_524,plain,
% 7.59/1.50      ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top
% 7.59/1.50      | r1_xboole_0(sK1,sK2) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_8205,plain,
% 7.59/1.50      ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) = iProver_top
% 7.59/1.50      | r1_xboole_0(sK1,sK2) = iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_524,c_530]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_888,plain,
% 7.59/1.50      ( r1_xboole_0(sK2,sK1) | r1_xboole_0(sK1,sK3) ),
% 7.59/1.50      inference(resolution,[status(thm)],[c_808,c_14]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_842,plain,
% 7.59/1.50      ( r1_xboole_0(sK2,sK1) | ~ r1_xboole_0(sK1,sK2) ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_664,plain,
% 7.59/1.50      ( r1_xboole_0(k2_xboole_0(sK2,sK3),sK1) | r1_xboole_0(sK1,sK2) ),
% 7.59/1.50      inference(resolution,[status(thm)],[c_3,c_16]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_809,plain,
% 7.59/1.50      ( ~ r1_tarski(X0,k2_xboole_0(sK2,sK3))
% 7.59/1.50      | r1_xboole_0(X0,sK1)
% 7.59/1.50      | r1_xboole_0(sK1,sK2) ),
% 7.59/1.50      inference(resolution,[status(thm)],[c_13,c_664]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1169,plain,
% 7.59/1.50      ( r1_xboole_0(sK2,sK1) | r1_xboole_0(sK1,sK2) ),
% 7.59/1.50      inference(resolution,[status(thm)],[c_809,c_14]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1277,plain,
% 7.59/1.50      ( r1_xboole_0(sK2,sK1) ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_888,c_842,c_1169]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1289,plain,
% 7.59/1.50      ( r1_xboole_0(sK1,sK2) ),
% 7.59/1.50      inference(resolution,[status(thm)],[c_1277,c_3]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1290,plain,
% 7.59/1.50      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_1289]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_9153,plain,
% 7.59/1.50      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 7.59/1.50      inference(global_propositional_subsumption,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_8205,c_1290]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_10325,plain,
% 7.59/1.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_9153,c_531]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_10963,plain,
% 7.59/1.50      ( k4_xboole_0(sK1,k4_xboole_0(X0,sK2)) = k2_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_10325,c_12]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_11541,plain,
% 7.59/1.50      ( k4_xboole_0(sK1,k4_xboole_0(X0,sK2)) = k4_xboole_0(sK1,X0) ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_10963,c_6]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1913,plain,
% 7.59/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_8,c_896]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_1942,plain,
% 7.59/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_1913,c_896]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_13401,plain,
% 7.59/1.50      ( k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(X0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(X0,sK2)) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_11541,c_1942]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_13478,plain,
% 7.59/1.50      ( k4_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(X0,sK2)) = k4_xboole_0(sK1,X0) ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_13401,c_11541]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_19039,plain,
% 7.59/1.50      ( k4_xboole_0(sK1,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK1,sK3) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_10784,c_13478]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_19199,plain,
% 7.59/1.50      ( k4_xboole_0(sK1,k4_xboole_0(sK3,sK2)) = sK1 ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_19039,c_10784]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_20234,plain,
% 7.59/1.50      ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(sK3,sK2))) = k2_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,sK1)) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_19199,c_12]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_20267,plain,
% 7.59/1.50      ( k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(sK3,sK2))) = k4_xboole_0(sK1,X0) ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_20234,c_6,c_539]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_25165,plain,
% 7.59/1.50      ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,sK2) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_6854,c_20267]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_10961,plain,
% 7.59/1.50      ( k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_10325,c_8]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_10979,plain,
% 7.59/1.50      ( k4_xboole_0(sK1,sK2) = sK1 ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_10961,c_6,c_1101]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_25339,plain,
% 7.59/1.50      ( k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = sK1 ),
% 7.59/1.50      inference(light_normalisation,[status(thm)],[c_25165,c_10979]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_532,plain,
% 7.59/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 7.59/1.50      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_26023,plain,
% 7.59/1.50      ( k4_xboole_0(sK1,sK1) != k1_xboole_0
% 7.59/1.50      | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
% 7.59/1.50      inference(superposition,[status(thm)],[c_25339,c_532]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_26134,plain,
% 7.59/1.50      ( k1_xboole_0 != k1_xboole_0
% 7.59/1.50      | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
% 7.59/1.50      inference(demodulation,[status(thm)],[c_26023,c_539]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_26135,plain,
% 7.59/1.50      ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) = iProver_top ),
% 7.59/1.50      inference(equality_resolution_simp,[status(thm)],[c_26134]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_743,plain,
% 7.59/1.50      ( r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
% 7.59/1.50      | k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) != k1_xboole_0 ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_639,plain,
% 7.59/1.50      ( ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
% 7.59/1.50      | k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) = k1_xboole_0 ),
% 7.59/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_640,plain,
% 7.59/1.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) = k1_xboole_0
% 7.59/1.50      | r1_xboole_0(sK1,k2_xboole_0(sK2,sK3)) != iProver_top ),
% 7.59/1.50      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(c_20,negated_conjecture,
% 7.59/1.50      ( ~ r1_xboole_0(sK1,k2_xboole_0(sK2,sK3))
% 7.59/1.50      | ~ r1_xboole_0(sK1,sK3)
% 7.59/1.50      | ~ r1_xboole_0(sK1,sK2) ),
% 7.59/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.59/1.50  
% 7.59/1.50  cnf(contradiction,plain,
% 7.59/1.50      ( $false ),
% 7.59/1.50      inference(minisat,
% 7.59/1.50                [status(thm)],
% 7.59/1.50                [c_26135,c_2748,c_1289,c_743,c_640,c_20]) ).
% 7.59/1.50  
% 7.59/1.50  
% 7.59/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.59/1.50  
% 7.59/1.50  ------                               Statistics
% 7.59/1.50  
% 7.59/1.50  ------ Selected
% 7.59/1.50  
% 7.59/1.50  total_time:                             0.845
% 7.59/1.50  
%------------------------------------------------------------------------------
