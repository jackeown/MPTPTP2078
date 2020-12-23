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
% DateTime   : Thu Dec  3 11:23:56 EST 2020

% Result     : Theorem 12.00s
% Output     : CNFRefutation 12.00s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 221 expanded)
%              Number of clauses        :   53 (  92 expanded)
%              Number of leaves         :   14 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  163 ( 383 expanded)
%              Number of equality atoms :   65 ( 158 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f21])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK2,sK3)
      & r1_xboole_0(sK2,sK4)
      & r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_tarski(sK2,sK3)
    & r1_xboole_0(sK2,sK4)
    & r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f29])).

fof(f45,plain,(
    r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f27])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f36,f44])).

fof(f46,plain,(
    r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_413,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_415,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1597,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_415])).

cnf(c_45261,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_413,c_1597])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_419,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_146,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK4 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_147,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))) ),
    inference(unflattening,[status(thm)],[c_146])).

cnf(c_411,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_147])).

cnf(c_7237,plain,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_419,c_411])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_417,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8046,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X0) = X0 ),
    inference(superposition,[status(thm)],[c_7237,c_417])).

cnf(c_9,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_867,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_12,c_9])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_873,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_867,c_7])).

cnf(c_1169,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_873])).

cnf(c_1448,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_9,c_1169])).

cnf(c_760,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_12])).

cnf(c_1055,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_760])).

cnf(c_1282,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1055,c_9])).

cnf(c_1285,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1282,c_7])).

cnf(c_1473,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1448,c_1285])).

cnf(c_8931,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK4),sK2) = k4_xboole_0(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_8046,c_1473])).

cnf(c_1059,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_760,c_9])).

cnf(c_1061,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1059,c_7])).

cnf(c_1315,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1061,c_0])).

cnf(c_1990,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_9,c_1315])).

cnf(c_2015,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_1990,c_9])).

cnf(c_6035,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_2015])).

cnf(c_8933,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_xboole_0(k4_xboole_0(sK2,sK4),sK2) ),
    inference(superposition,[status(thm)],[c_8046,c_6035])).

cnf(c_10,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_883,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_10,c_9])).

cnf(c_7686,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1055,c_883])).

cnf(c_7833,plain,
    ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7686,c_7])).

cnf(c_7834,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_7833,c_10])).

cnf(c_762,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_12])).

cnf(c_868,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_762,c_9])).

cnf(c_872,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_868,c_7])).

cnf(c_7835,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_7834,c_872])).

cnf(c_8936,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK4),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_8933,c_7835])).

cnf(c_8937,plain,
    ( k4_xboole_0(sK2,sK4) = sK2 ),
    inference(demodulation,[status(thm)],[c_8931,c_8936])).

cnf(c_45362,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_45261,c_8937])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_18,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_45362,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:31:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 12.00/2.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.00/2.04  
% 12.00/2.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.00/2.04  
% 12.00/2.04  ------  iProver source info
% 12.00/2.04  
% 12.00/2.04  git: date: 2020-06-30 10:37:57 +0100
% 12.00/2.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.00/2.04  git: non_committed_changes: false
% 12.00/2.04  git: last_make_outside_of_git: false
% 12.00/2.04  
% 12.00/2.04  ------ 
% 12.00/2.04  
% 12.00/2.04  ------ Input Options
% 12.00/2.04  
% 12.00/2.04  --out_options                           all
% 12.00/2.04  --tptp_safe_out                         true
% 12.00/2.04  --problem_path                          ""
% 12.00/2.04  --include_path                          ""
% 12.00/2.04  --clausifier                            res/vclausify_rel
% 12.00/2.04  --clausifier_options                    ""
% 12.00/2.04  --stdin                                 false
% 12.00/2.04  --stats_out                             all
% 12.00/2.04  
% 12.00/2.04  ------ General Options
% 12.00/2.04  
% 12.00/2.04  --fof                                   false
% 12.00/2.04  --time_out_real                         305.
% 12.00/2.04  --time_out_virtual                      -1.
% 12.00/2.04  --symbol_type_check                     false
% 12.00/2.04  --clausify_out                          false
% 12.00/2.04  --sig_cnt_out                           false
% 12.00/2.04  --trig_cnt_out                          false
% 12.00/2.04  --trig_cnt_out_tolerance                1.
% 12.00/2.04  --trig_cnt_out_sk_spl                   false
% 12.00/2.04  --abstr_cl_out                          false
% 12.00/2.04  
% 12.00/2.04  ------ Global Options
% 12.00/2.04  
% 12.00/2.04  --schedule                              default
% 12.00/2.04  --add_important_lit                     false
% 12.00/2.04  --prop_solver_per_cl                    1000
% 12.00/2.04  --min_unsat_core                        false
% 12.00/2.04  --soft_assumptions                      false
% 12.00/2.04  --soft_lemma_size                       3
% 12.00/2.04  --prop_impl_unit_size                   0
% 12.00/2.04  --prop_impl_unit                        []
% 12.00/2.04  --share_sel_clauses                     true
% 12.00/2.04  --reset_solvers                         false
% 12.00/2.04  --bc_imp_inh                            [conj_cone]
% 12.00/2.04  --conj_cone_tolerance                   3.
% 12.00/2.04  --extra_neg_conj                        none
% 12.00/2.04  --large_theory_mode                     true
% 12.00/2.04  --prolific_symb_bound                   200
% 12.00/2.04  --lt_threshold                          2000
% 12.00/2.04  --clause_weak_htbl                      true
% 12.00/2.04  --gc_record_bc_elim                     false
% 12.00/2.04  
% 12.00/2.04  ------ Preprocessing Options
% 12.00/2.04  
% 12.00/2.04  --preprocessing_flag                    true
% 12.00/2.04  --time_out_prep_mult                    0.1
% 12.00/2.04  --splitting_mode                        input
% 12.00/2.04  --splitting_grd                         true
% 12.00/2.04  --splitting_cvd                         false
% 12.00/2.04  --splitting_cvd_svl                     false
% 12.00/2.04  --splitting_nvd                         32
% 12.00/2.04  --sub_typing                            true
% 12.00/2.04  --prep_gs_sim                           true
% 12.00/2.04  --prep_unflatten                        true
% 12.00/2.04  --prep_res_sim                          true
% 12.00/2.04  --prep_upred                            true
% 12.00/2.04  --prep_sem_filter                       exhaustive
% 12.00/2.04  --prep_sem_filter_out                   false
% 12.00/2.04  --pred_elim                             true
% 12.00/2.04  --res_sim_input                         true
% 12.00/2.04  --eq_ax_congr_red                       true
% 12.00/2.04  --pure_diseq_elim                       true
% 12.00/2.04  --brand_transform                       false
% 12.00/2.04  --non_eq_to_eq                          false
% 12.00/2.04  --prep_def_merge                        true
% 12.00/2.04  --prep_def_merge_prop_impl              false
% 12.00/2.04  --prep_def_merge_mbd                    true
% 12.00/2.04  --prep_def_merge_tr_red                 false
% 12.00/2.04  --prep_def_merge_tr_cl                  false
% 12.00/2.04  --smt_preprocessing                     true
% 12.00/2.04  --smt_ac_axioms                         fast
% 12.00/2.04  --preprocessed_out                      false
% 12.00/2.04  --preprocessed_stats                    false
% 12.00/2.04  
% 12.00/2.04  ------ Abstraction refinement Options
% 12.00/2.04  
% 12.00/2.04  --abstr_ref                             []
% 12.00/2.04  --abstr_ref_prep                        false
% 12.00/2.04  --abstr_ref_until_sat                   false
% 12.00/2.04  --abstr_ref_sig_restrict                funpre
% 12.00/2.04  --abstr_ref_af_restrict_to_split_sk     false
% 12.00/2.04  --abstr_ref_under                       []
% 12.00/2.04  
% 12.00/2.04  ------ SAT Options
% 12.00/2.04  
% 12.00/2.04  --sat_mode                              false
% 12.00/2.04  --sat_fm_restart_options                ""
% 12.00/2.04  --sat_gr_def                            false
% 12.00/2.04  --sat_epr_types                         true
% 12.00/2.04  --sat_non_cyclic_types                  false
% 12.00/2.04  --sat_finite_models                     false
% 12.00/2.04  --sat_fm_lemmas                         false
% 12.00/2.04  --sat_fm_prep                           false
% 12.00/2.04  --sat_fm_uc_incr                        true
% 12.00/2.04  --sat_out_model                         small
% 12.00/2.04  --sat_out_clauses                       false
% 12.00/2.04  
% 12.00/2.04  ------ QBF Options
% 12.00/2.04  
% 12.00/2.04  --qbf_mode                              false
% 12.00/2.04  --qbf_elim_univ                         false
% 12.00/2.04  --qbf_dom_inst                          none
% 12.00/2.04  --qbf_dom_pre_inst                      false
% 12.00/2.04  --qbf_sk_in                             false
% 12.00/2.04  --qbf_pred_elim                         true
% 12.00/2.04  --qbf_split                             512
% 12.00/2.04  
% 12.00/2.04  ------ BMC1 Options
% 12.00/2.04  
% 12.00/2.04  --bmc1_incremental                      false
% 12.00/2.04  --bmc1_axioms                           reachable_all
% 12.00/2.04  --bmc1_min_bound                        0
% 12.00/2.04  --bmc1_max_bound                        -1
% 12.00/2.04  --bmc1_max_bound_default                -1
% 12.00/2.04  --bmc1_symbol_reachability              true
% 12.00/2.04  --bmc1_property_lemmas                  false
% 12.00/2.04  --bmc1_k_induction                      false
% 12.00/2.04  --bmc1_non_equiv_states                 false
% 12.00/2.04  --bmc1_deadlock                         false
% 12.00/2.04  --bmc1_ucm                              false
% 12.00/2.04  --bmc1_add_unsat_core                   none
% 12.00/2.04  --bmc1_unsat_core_children              false
% 12.00/2.04  --bmc1_unsat_core_extrapolate_axioms    false
% 12.00/2.04  --bmc1_out_stat                         full
% 12.00/2.04  --bmc1_ground_init                      false
% 12.00/2.04  --bmc1_pre_inst_next_state              false
% 12.00/2.04  --bmc1_pre_inst_state                   false
% 12.00/2.04  --bmc1_pre_inst_reach_state             false
% 12.00/2.04  --bmc1_out_unsat_core                   false
% 12.00/2.04  --bmc1_aig_witness_out                  false
% 12.00/2.04  --bmc1_verbose                          false
% 12.00/2.04  --bmc1_dump_clauses_tptp                false
% 12.00/2.04  --bmc1_dump_unsat_core_tptp             false
% 12.00/2.04  --bmc1_dump_file                        -
% 12.00/2.04  --bmc1_ucm_expand_uc_limit              128
% 12.00/2.04  --bmc1_ucm_n_expand_iterations          6
% 12.00/2.04  --bmc1_ucm_extend_mode                  1
% 12.00/2.04  --bmc1_ucm_init_mode                    2
% 12.00/2.04  --bmc1_ucm_cone_mode                    none
% 12.00/2.04  --bmc1_ucm_reduced_relation_type        0
% 12.00/2.04  --bmc1_ucm_relax_model                  4
% 12.00/2.04  --bmc1_ucm_full_tr_after_sat            true
% 12.00/2.04  --bmc1_ucm_expand_neg_assumptions       false
% 12.00/2.04  --bmc1_ucm_layered_model                none
% 12.00/2.04  --bmc1_ucm_max_lemma_size               10
% 12.00/2.04  
% 12.00/2.04  ------ AIG Options
% 12.00/2.04  
% 12.00/2.04  --aig_mode                              false
% 12.00/2.04  
% 12.00/2.04  ------ Instantiation Options
% 12.00/2.04  
% 12.00/2.04  --instantiation_flag                    true
% 12.00/2.04  --inst_sos_flag                         true
% 12.00/2.04  --inst_sos_phase                        true
% 12.00/2.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.00/2.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.00/2.04  --inst_lit_sel_side                     num_symb
% 12.00/2.04  --inst_solver_per_active                1400
% 12.00/2.04  --inst_solver_calls_frac                1.
% 12.00/2.04  --inst_passive_queue_type               priority_queues
% 12.00/2.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.00/2.04  --inst_passive_queues_freq              [25;2]
% 12.00/2.04  --inst_dismatching                      true
% 12.00/2.04  --inst_eager_unprocessed_to_passive     true
% 12.00/2.04  --inst_prop_sim_given                   true
% 12.00/2.04  --inst_prop_sim_new                     false
% 12.00/2.04  --inst_subs_new                         false
% 12.00/2.04  --inst_eq_res_simp                      false
% 12.00/2.04  --inst_subs_given                       false
% 12.00/2.04  --inst_orphan_elimination               true
% 12.00/2.04  --inst_learning_loop_flag               true
% 12.00/2.04  --inst_learning_start                   3000
% 12.00/2.04  --inst_learning_factor                  2
% 12.00/2.04  --inst_start_prop_sim_after_learn       3
% 12.00/2.04  --inst_sel_renew                        solver
% 12.00/2.04  --inst_lit_activity_flag                true
% 12.00/2.04  --inst_restr_to_given                   false
% 12.00/2.04  --inst_activity_threshold               500
% 12.00/2.04  --inst_out_proof                        true
% 12.00/2.04  
% 12.00/2.04  ------ Resolution Options
% 12.00/2.04  
% 12.00/2.04  --resolution_flag                       true
% 12.00/2.04  --res_lit_sel                           adaptive
% 12.00/2.04  --res_lit_sel_side                      none
% 12.00/2.04  --res_ordering                          kbo
% 12.00/2.04  --res_to_prop_solver                    active
% 12.00/2.04  --res_prop_simpl_new                    false
% 12.00/2.04  --res_prop_simpl_given                  true
% 12.00/2.04  --res_passive_queue_type                priority_queues
% 12.00/2.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.00/2.04  --res_passive_queues_freq               [15;5]
% 12.00/2.04  --res_forward_subs                      full
% 12.00/2.04  --res_backward_subs                     full
% 12.00/2.04  --res_forward_subs_resolution           true
% 12.00/2.04  --res_backward_subs_resolution          true
% 12.00/2.04  --res_orphan_elimination                true
% 12.00/2.04  --res_time_limit                        2.
% 12.00/2.04  --res_out_proof                         true
% 12.00/2.04  
% 12.00/2.04  ------ Superposition Options
% 12.00/2.04  
% 12.00/2.04  --superposition_flag                    true
% 12.00/2.04  --sup_passive_queue_type                priority_queues
% 12.00/2.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.00/2.04  --sup_passive_queues_freq               [8;1;4]
% 12.00/2.04  --demod_completeness_check              fast
% 12.00/2.04  --demod_use_ground                      true
% 12.00/2.04  --sup_to_prop_solver                    passive
% 12.00/2.04  --sup_prop_simpl_new                    true
% 12.00/2.04  --sup_prop_simpl_given                  true
% 12.00/2.04  --sup_fun_splitting                     true
% 12.00/2.04  --sup_smt_interval                      50000
% 12.00/2.04  
% 12.00/2.04  ------ Superposition Simplification Setup
% 12.00/2.04  
% 12.00/2.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.00/2.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.00/2.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.00/2.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.00/2.04  --sup_full_triv                         [TrivRules;PropSubs]
% 12.00/2.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.00/2.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.00/2.04  --sup_immed_triv                        [TrivRules]
% 12.00/2.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.00/2.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.00/2.04  --sup_immed_bw_main                     []
% 12.00/2.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.00/2.04  --sup_input_triv                        [Unflattening;TrivRules]
% 12.00/2.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.00/2.04  --sup_input_bw                          []
% 12.00/2.04  
% 12.00/2.04  ------ Combination Options
% 12.00/2.04  
% 12.00/2.04  --comb_res_mult                         3
% 12.00/2.04  --comb_sup_mult                         2
% 12.00/2.04  --comb_inst_mult                        10
% 12.00/2.04  
% 12.00/2.04  ------ Debug Options
% 12.00/2.04  
% 12.00/2.04  --dbg_backtrace                         false
% 12.00/2.04  --dbg_dump_prop_clauses                 false
% 12.00/2.04  --dbg_dump_prop_clauses_file            -
% 12.00/2.04  --dbg_out_stat                          false
% 12.00/2.04  ------ Parsing...
% 12.00/2.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.00/2.04  
% 12.00/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 12.00/2.04  
% 12.00/2.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.00/2.04  
% 12.00/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.00/2.04  ------ Proving...
% 12.00/2.04  ------ Problem Properties 
% 12.00/2.04  
% 12.00/2.04  
% 12.00/2.04  clauses                                 15
% 12.00/2.04  conjectures                             2
% 12.00/2.04  EPR                                     3
% 12.00/2.04  Horn                                    14
% 12.00/2.04  unary                                   8
% 12.00/2.04  binary                                  5
% 12.00/2.04  lits                                    24
% 12.00/2.04  lits eq                                 6
% 12.00/2.04  fd_pure                                 0
% 12.00/2.04  fd_pseudo                               0
% 12.00/2.04  fd_cond                                 0
% 12.00/2.04  fd_pseudo_cond                          0
% 12.00/2.04  AC symbols                              0
% 12.00/2.04  
% 12.00/2.04  ------ Schedule dynamic 5 is on 
% 12.00/2.04  
% 12.00/2.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 12.00/2.04  
% 12.00/2.04  
% 12.00/2.04  ------ 
% 12.00/2.04  Current options:
% 12.00/2.04  ------ 
% 12.00/2.04  
% 12.00/2.04  ------ Input Options
% 12.00/2.04  
% 12.00/2.04  --out_options                           all
% 12.00/2.04  --tptp_safe_out                         true
% 12.00/2.04  --problem_path                          ""
% 12.00/2.04  --include_path                          ""
% 12.00/2.04  --clausifier                            res/vclausify_rel
% 12.00/2.04  --clausifier_options                    ""
% 12.00/2.04  --stdin                                 false
% 12.00/2.04  --stats_out                             all
% 12.00/2.04  
% 12.00/2.04  ------ General Options
% 12.00/2.04  
% 12.00/2.04  --fof                                   false
% 12.00/2.04  --time_out_real                         305.
% 12.00/2.04  --time_out_virtual                      -1.
% 12.00/2.04  --symbol_type_check                     false
% 12.00/2.04  --clausify_out                          false
% 12.00/2.04  --sig_cnt_out                           false
% 12.00/2.04  --trig_cnt_out                          false
% 12.00/2.04  --trig_cnt_out_tolerance                1.
% 12.00/2.04  --trig_cnt_out_sk_spl                   false
% 12.00/2.04  --abstr_cl_out                          false
% 12.00/2.04  
% 12.00/2.04  ------ Global Options
% 12.00/2.04  
% 12.00/2.04  --schedule                              default
% 12.00/2.04  --add_important_lit                     false
% 12.00/2.04  --prop_solver_per_cl                    1000
% 12.00/2.04  --min_unsat_core                        false
% 12.00/2.04  --soft_assumptions                      false
% 12.00/2.04  --soft_lemma_size                       3
% 12.00/2.04  --prop_impl_unit_size                   0
% 12.00/2.04  --prop_impl_unit                        []
% 12.00/2.04  --share_sel_clauses                     true
% 12.00/2.04  --reset_solvers                         false
% 12.00/2.04  --bc_imp_inh                            [conj_cone]
% 12.00/2.04  --conj_cone_tolerance                   3.
% 12.00/2.04  --extra_neg_conj                        none
% 12.00/2.04  --large_theory_mode                     true
% 12.00/2.04  --prolific_symb_bound                   200
% 12.00/2.04  --lt_threshold                          2000
% 12.00/2.04  --clause_weak_htbl                      true
% 12.00/2.04  --gc_record_bc_elim                     false
% 12.00/2.04  
% 12.00/2.04  ------ Preprocessing Options
% 12.00/2.04  
% 12.00/2.04  --preprocessing_flag                    true
% 12.00/2.04  --time_out_prep_mult                    0.1
% 12.00/2.04  --splitting_mode                        input
% 12.00/2.04  --splitting_grd                         true
% 12.00/2.04  --splitting_cvd                         false
% 12.00/2.04  --splitting_cvd_svl                     false
% 12.00/2.04  --splitting_nvd                         32
% 12.00/2.04  --sub_typing                            true
% 12.00/2.04  --prep_gs_sim                           true
% 12.00/2.04  --prep_unflatten                        true
% 12.00/2.04  --prep_res_sim                          true
% 12.00/2.04  --prep_upred                            true
% 12.00/2.04  --prep_sem_filter                       exhaustive
% 12.00/2.04  --prep_sem_filter_out                   false
% 12.00/2.04  --pred_elim                             true
% 12.00/2.04  --res_sim_input                         true
% 12.00/2.04  --eq_ax_congr_red                       true
% 12.00/2.04  --pure_diseq_elim                       true
% 12.00/2.04  --brand_transform                       false
% 12.00/2.04  --non_eq_to_eq                          false
% 12.00/2.04  --prep_def_merge                        true
% 12.00/2.04  --prep_def_merge_prop_impl              false
% 12.00/2.04  --prep_def_merge_mbd                    true
% 12.00/2.04  --prep_def_merge_tr_red                 false
% 12.00/2.04  --prep_def_merge_tr_cl                  false
% 12.00/2.04  --smt_preprocessing                     true
% 12.00/2.04  --smt_ac_axioms                         fast
% 12.00/2.04  --preprocessed_out                      false
% 12.00/2.04  --preprocessed_stats                    false
% 12.00/2.04  
% 12.00/2.04  ------ Abstraction refinement Options
% 12.00/2.04  
% 12.00/2.04  --abstr_ref                             []
% 12.00/2.04  --abstr_ref_prep                        false
% 12.00/2.04  --abstr_ref_until_sat                   false
% 12.00/2.04  --abstr_ref_sig_restrict                funpre
% 12.00/2.04  --abstr_ref_af_restrict_to_split_sk     false
% 12.00/2.04  --abstr_ref_under                       []
% 12.00/2.04  
% 12.00/2.04  ------ SAT Options
% 12.00/2.04  
% 12.00/2.04  --sat_mode                              false
% 12.00/2.04  --sat_fm_restart_options                ""
% 12.00/2.04  --sat_gr_def                            false
% 12.00/2.04  --sat_epr_types                         true
% 12.00/2.04  --sat_non_cyclic_types                  false
% 12.00/2.04  --sat_finite_models                     false
% 12.00/2.04  --sat_fm_lemmas                         false
% 12.00/2.04  --sat_fm_prep                           false
% 12.00/2.04  --sat_fm_uc_incr                        true
% 12.00/2.04  --sat_out_model                         small
% 12.00/2.04  --sat_out_clauses                       false
% 12.00/2.04  
% 12.00/2.04  ------ QBF Options
% 12.00/2.04  
% 12.00/2.04  --qbf_mode                              false
% 12.00/2.04  --qbf_elim_univ                         false
% 12.00/2.04  --qbf_dom_inst                          none
% 12.00/2.04  --qbf_dom_pre_inst                      false
% 12.00/2.04  --qbf_sk_in                             false
% 12.00/2.04  --qbf_pred_elim                         true
% 12.00/2.04  --qbf_split                             512
% 12.00/2.04  
% 12.00/2.04  ------ BMC1 Options
% 12.00/2.04  
% 12.00/2.04  --bmc1_incremental                      false
% 12.00/2.04  --bmc1_axioms                           reachable_all
% 12.00/2.04  --bmc1_min_bound                        0
% 12.00/2.04  --bmc1_max_bound                        -1
% 12.00/2.04  --bmc1_max_bound_default                -1
% 12.00/2.04  --bmc1_symbol_reachability              true
% 12.00/2.04  --bmc1_property_lemmas                  false
% 12.00/2.04  --bmc1_k_induction                      false
% 12.00/2.04  --bmc1_non_equiv_states                 false
% 12.00/2.04  --bmc1_deadlock                         false
% 12.00/2.04  --bmc1_ucm                              false
% 12.00/2.04  --bmc1_add_unsat_core                   none
% 12.00/2.04  --bmc1_unsat_core_children              false
% 12.00/2.04  --bmc1_unsat_core_extrapolate_axioms    false
% 12.00/2.04  --bmc1_out_stat                         full
% 12.00/2.04  --bmc1_ground_init                      false
% 12.00/2.04  --bmc1_pre_inst_next_state              false
% 12.00/2.04  --bmc1_pre_inst_state                   false
% 12.00/2.04  --bmc1_pre_inst_reach_state             false
% 12.00/2.04  --bmc1_out_unsat_core                   false
% 12.00/2.04  --bmc1_aig_witness_out                  false
% 12.00/2.04  --bmc1_verbose                          false
% 12.00/2.04  --bmc1_dump_clauses_tptp                false
% 12.00/2.04  --bmc1_dump_unsat_core_tptp             false
% 12.00/2.04  --bmc1_dump_file                        -
% 12.00/2.04  --bmc1_ucm_expand_uc_limit              128
% 12.00/2.04  --bmc1_ucm_n_expand_iterations          6
% 12.00/2.04  --bmc1_ucm_extend_mode                  1
% 12.00/2.04  --bmc1_ucm_init_mode                    2
% 12.00/2.04  --bmc1_ucm_cone_mode                    none
% 12.00/2.04  --bmc1_ucm_reduced_relation_type        0
% 12.00/2.04  --bmc1_ucm_relax_model                  4
% 12.00/2.04  --bmc1_ucm_full_tr_after_sat            true
% 12.00/2.04  --bmc1_ucm_expand_neg_assumptions       false
% 12.00/2.04  --bmc1_ucm_layered_model                none
% 12.00/2.04  --bmc1_ucm_max_lemma_size               10
% 12.00/2.04  
% 12.00/2.04  ------ AIG Options
% 12.00/2.04  
% 12.00/2.04  --aig_mode                              false
% 12.00/2.04  
% 12.00/2.04  ------ Instantiation Options
% 12.00/2.04  
% 12.00/2.04  --instantiation_flag                    true
% 12.00/2.04  --inst_sos_flag                         true
% 12.00/2.04  --inst_sos_phase                        true
% 12.00/2.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.00/2.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.00/2.04  --inst_lit_sel_side                     none
% 12.00/2.04  --inst_solver_per_active                1400
% 12.00/2.04  --inst_solver_calls_frac                1.
% 12.00/2.04  --inst_passive_queue_type               priority_queues
% 12.00/2.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.00/2.04  --inst_passive_queues_freq              [25;2]
% 12.00/2.04  --inst_dismatching                      true
% 12.00/2.04  --inst_eager_unprocessed_to_passive     true
% 12.00/2.04  --inst_prop_sim_given                   true
% 12.00/2.04  --inst_prop_sim_new                     false
% 12.00/2.04  --inst_subs_new                         false
% 12.00/2.04  --inst_eq_res_simp                      false
% 12.00/2.04  --inst_subs_given                       false
% 12.00/2.04  --inst_orphan_elimination               true
% 12.00/2.04  --inst_learning_loop_flag               true
% 12.00/2.04  --inst_learning_start                   3000
% 12.00/2.04  --inst_learning_factor                  2
% 12.00/2.04  --inst_start_prop_sim_after_learn       3
% 12.00/2.04  --inst_sel_renew                        solver
% 12.00/2.04  --inst_lit_activity_flag                true
% 12.00/2.04  --inst_restr_to_given                   false
% 12.00/2.04  --inst_activity_threshold               500
% 12.00/2.04  --inst_out_proof                        true
% 12.00/2.04  
% 12.00/2.04  ------ Resolution Options
% 12.00/2.04  
% 12.00/2.04  --resolution_flag                       false
% 12.00/2.04  --res_lit_sel                           adaptive
% 12.00/2.04  --res_lit_sel_side                      none
% 12.00/2.04  --res_ordering                          kbo
% 12.00/2.04  --res_to_prop_solver                    active
% 12.00/2.04  --res_prop_simpl_new                    false
% 12.00/2.04  --res_prop_simpl_given                  true
% 12.00/2.04  --res_passive_queue_type                priority_queues
% 12.00/2.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.00/2.04  --res_passive_queues_freq               [15;5]
% 12.00/2.04  --res_forward_subs                      full
% 12.00/2.04  --res_backward_subs                     full
% 12.00/2.04  --res_forward_subs_resolution           true
% 12.00/2.04  --res_backward_subs_resolution          true
% 12.00/2.04  --res_orphan_elimination                true
% 12.00/2.04  --res_time_limit                        2.
% 12.00/2.04  --res_out_proof                         true
% 12.00/2.04  
% 12.00/2.04  ------ Superposition Options
% 12.00/2.04  
% 12.00/2.04  --superposition_flag                    true
% 12.00/2.04  --sup_passive_queue_type                priority_queues
% 12.00/2.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.00/2.04  --sup_passive_queues_freq               [8;1;4]
% 12.00/2.04  --demod_completeness_check              fast
% 12.00/2.04  --demod_use_ground                      true
% 12.00/2.04  --sup_to_prop_solver                    passive
% 12.00/2.04  --sup_prop_simpl_new                    true
% 12.00/2.04  --sup_prop_simpl_given                  true
% 12.00/2.04  --sup_fun_splitting                     true
% 12.00/2.04  --sup_smt_interval                      50000
% 12.00/2.04  
% 12.00/2.04  ------ Superposition Simplification Setup
% 12.00/2.04  
% 12.00/2.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.00/2.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.00/2.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.00/2.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.00/2.04  --sup_full_triv                         [TrivRules;PropSubs]
% 12.00/2.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.00/2.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.00/2.04  --sup_immed_triv                        [TrivRules]
% 12.00/2.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.00/2.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.00/2.04  --sup_immed_bw_main                     []
% 12.00/2.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.00/2.04  --sup_input_triv                        [Unflattening;TrivRules]
% 12.00/2.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.00/2.04  --sup_input_bw                          []
% 12.00/2.04  
% 12.00/2.04  ------ Combination Options
% 12.00/2.04  
% 12.00/2.04  --comb_res_mult                         3
% 12.00/2.04  --comb_sup_mult                         2
% 12.00/2.04  --comb_inst_mult                        10
% 12.00/2.04  
% 12.00/2.04  ------ Debug Options
% 12.00/2.04  
% 12.00/2.04  --dbg_backtrace                         false
% 12.00/2.04  --dbg_dump_prop_clauses                 false
% 12.00/2.04  --dbg_dump_prop_clauses_file            -
% 12.00/2.04  --dbg_out_stat                          false
% 12.00/2.04  
% 12.00/2.04  
% 12.00/2.04  
% 12.00/2.04  
% 12.00/2.04  ------ Proving...
% 12.00/2.04  
% 12.00/2.04  
% 12.00/2.04  % SZS status Theorem for theBenchmark.p
% 12.00/2.04  
% 12.00/2.04  % SZS output start CNFRefutation for theBenchmark.p
% 12.00/2.04  
% 12.00/2.04  fof(f12,conjecture,(
% 12.00/2.04    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 12.00/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/2.04  
% 12.00/2.04  fof(f13,negated_conjecture,(
% 12.00/2.04    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 12.00/2.04    inference(negated_conjecture,[],[f12])).
% 12.00/2.04  
% 12.00/2.04  fof(f21,plain,(
% 12.00/2.04    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 12.00/2.04    inference(ennf_transformation,[],[f13])).
% 12.00/2.04  
% 12.00/2.04  fof(f22,plain,(
% 12.00/2.04    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 12.00/2.04    inference(flattening,[],[f21])).
% 12.00/2.04  
% 12.00/2.04  fof(f29,plain,(
% 12.00/2.04    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK2,sK3) & r1_xboole_0(sK2,sK4) & r1_tarski(sK2,k2_xboole_0(sK3,sK4)))),
% 12.00/2.04    introduced(choice_axiom,[])).
% 12.00/2.04  
% 12.00/2.04  fof(f30,plain,(
% 12.00/2.04    ~r1_tarski(sK2,sK3) & r1_xboole_0(sK2,sK4) & r1_tarski(sK2,k2_xboole_0(sK3,sK4))),
% 12.00/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f29])).
% 12.00/2.04  
% 12.00/2.04  fof(f45,plain,(
% 12.00/2.04    r1_tarski(sK2,k2_xboole_0(sK3,sK4))),
% 12.00/2.04    inference(cnf_transformation,[],[f30])).
% 12.00/2.04  
% 12.00/2.04  fof(f1,axiom,(
% 12.00/2.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 12.00/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/2.04  
% 12.00/2.04  fof(f31,plain,(
% 12.00/2.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 12.00/2.04    inference(cnf_transformation,[],[f1])).
% 12.00/2.04  
% 12.00/2.04  fof(f9,axiom,(
% 12.00/2.04    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 12.00/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/2.04  
% 12.00/2.04  fof(f20,plain,(
% 12.00/2.04    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 12.00/2.04    inference(ennf_transformation,[],[f9])).
% 12.00/2.04  
% 12.00/2.04  fof(f42,plain,(
% 12.00/2.04    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 12.00/2.04    inference(cnf_transformation,[],[f20])).
% 12.00/2.04  
% 12.00/2.04  fof(f2,axiom,(
% 12.00/2.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 12.00/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/2.04  
% 12.00/2.04  fof(f15,plain,(
% 12.00/2.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 12.00/2.04    inference(ennf_transformation,[],[f2])).
% 12.00/2.04  
% 12.00/2.04  fof(f23,plain,(
% 12.00/2.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 12.00/2.04    inference(nnf_transformation,[],[f15])).
% 12.00/2.04  
% 12.00/2.04  fof(f24,plain,(
% 12.00/2.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.00/2.04    inference(rectify,[],[f23])).
% 12.00/2.04  
% 12.00/2.04  fof(f25,plain,(
% 12.00/2.04    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 12.00/2.04    introduced(choice_axiom,[])).
% 12.00/2.04  
% 12.00/2.04  fof(f26,plain,(
% 12.00/2.04    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.00/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 12.00/2.04  
% 12.00/2.04  fof(f33,plain,(
% 12.00/2.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 12.00/2.04    inference(cnf_transformation,[],[f26])).
% 12.00/2.04  
% 12.00/2.04  fof(f3,axiom,(
% 12.00/2.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 12.00/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/2.04  
% 12.00/2.04  fof(f14,plain,(
% 12.00/2.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 12.00/2.04    inference(rectify,[],[f3])).
% 12.00/2.04  
% 12.00/2.04  fof(f16,plain,(
% 12.00/2.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 12.00/2.04    inference(ennf_transformation,[],[f14])).
% 12.00/2.04  
% 12.00/2.04  fof(f27,plain,(
% 12.00/2.04    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 12.00/2.04    introduced(choice_axiom,[])).
% 12.00/2.04  
% 12.00/2.04  fof(f28,plain,(
% 12.00/2.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 12.00/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f27])).
% 12.00/2.04  
% 12.00/2.04  fof(f36,plain,(
% 12.00/2.04    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 12.00/2.04    inference(cnf_transformation,[],[f28])).
% 12.00/2.04  
% 12.00/2.04  fof(f11,axiom,(
% 12.00/2.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.00/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/2.04  
% 12.00/2.04  fof(f44,plain,(
% 12.00/2.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.00/2.04    inference(cnf_transformation,[],[f11])).
% 12.00/2.04  
% 12.00/2.04  fof(f48,plain,(
% 12.00/2.04    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 12.00/2.04    inference(definition_unfolding,[],[f36,f44])).
% 12.00/2.04  
% 12.00/2.04  fof(f46,plain,(
% 12.00/2.04    r1_xboole_0(sK2,sK4)),
% 12.00/2.04    inference(cnf_transformation,[],[f30])).
% 12.00/2.04  
% 12.00/2.04  fof(f4,axiom,(
% 12.00/2.04    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 12.00/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/2.04  
% 12.00/2.04  fof(f17,plain,(
% 12.00/2.04    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 12.00/2.04    inference(ennf_transformation,[],[f4])).
% 12.00/2.04  
% 12.00/2.04  fof(f37,plain,(
% 12.00/2.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 12.00/2.04    inference(cnf_transformation,[],[f17])).
% 12.00/2.04  
% 12.00/2.04  fof(f7,axiom,(
% 12.00/2.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 12.00/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/2.04  
% 12.00/2.04  fof(f40,plain,(
% 12.00/2.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 12.00/2.04    inference(cnf_transformation,[],[f7])).
% 12.00/2.04  
% 12.00/2.04  fof(f10,axiom,(
% 12.00/2.04    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 12.00/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/2.04  
% 12.00/2.04  fof(f43,plain,(
% 12.00/2.04    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 12.00/2.04    inference(cnf_transformation,[],[f10])).
% 12.00/2.04  
% 12.00/2.04  fof(f5,axiom,(
% 12.00/2.04    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 12.00/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/2.04  
% 12.00/2.04  fof(f38,plain,(
% 12.00/2.04    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.00/2.04    inference(cnf_transformation,[],[f5])).
% 12.00/2.04  
% 12.00/2.04  fof(f8,axiom,(
% 12.00/2.04    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 12.00/2.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 12.00/2.04  
% 12.00/2.04  fof(f41,plain,(
% 12.00/2.04    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 12.00/2.04    inference(cnf_transformation,[],[f8])).
% 12.00/2.04  
% 12.00/2.04  fof(f47,plain,(
% 12.00/2.04    ~r1_tarski(sK2,sK3)),
% 12.00/2.04    inference(cnf_transformation,[],[f30])).
% 12.00/2.04  
% 12.00/2.04  cnf(c_15,negated_conjecture,
% 12.00/2.04      ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
% 12.00/2.04      inference(cnf_transformation,[],[f45]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_413,plain,
% 12.00/2.04      ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) = iProver_top ),
% 12.00/2.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_0,plain,
% 12.00/2.04      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 12.00/2.04      inference(cnf_transformation,[],[f31]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_11,plain,
% 12.00/2.04      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 12.00/2.04      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 12.00/2.04      inference(cnf_transformation,[],[f42]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_415,plain,
% 12.00/2.04      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 12.00/2.04      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 12.00/2.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_1597,plain,
% 12.00/2.04      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 12.00/2.04      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_0,c_415]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_45261,plain,
% 12.00/2.04      ( r1_tarski(k4_xboole_0(sK2,sK4),sK3) = iProver_top ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_413,c_1597]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_2,plain,
% 12.00/2.04      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 12.00/2.04      inference(cnf_transformation,[],[f33]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_419,plain,
% 12.00/2.04      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 12.00/2.04      | r1_tarski(X0,X1) = iProver_top ),
% 12.00/2.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_4,plain,
% 12.00/2.04      ( ~ r1_xboole_0(X0,X1)
% 12.00/2.04      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 12.00/2.04      inference(cnf_transformation,[],[f48]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_14,negated_conjecture,
% 12.00/2.04      ( r1_xboole_0(sK2,sK4) ),
% 12.00/2.04      inference(cnf_transformation,[],[f46]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_146,plain,
% 12.00/2.04      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 12.00/2.04      | sK4 != X2
% 12.00/2.04      | sK2 != X1 ),
% 12.00/2.04      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_147,plain,
% 12.00/2.04      ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))) ),
% 12.00/2.04      inference(unflattening,[status(thm)],[c_146]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_411,plain,
% 12.00/2.04      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK4))) != iProver_top ),
% 12.00/2.04      inference(predicate_to_equality,[status(thm)],[c_147]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_7237,plain,
% 12.00/2.04      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X0) = iProver_top ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_419,c_411]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_6,plain,
% 12.00/2.04      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 12.00/2.04      inference(cnf_transformation,[],[f37]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_417,plain,
% 12.00/2.04      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 12.00/2.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_8046,plain,
% 12.00/2.04      ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)),X0) = X0 ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_7237,c_417]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_9,plain,
% 12.00/2.04      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 12.00/2.04      inference(cnf_transformation,[],[f40]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_12,plain,
% 12.00/2.04      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 12.00/2.04      inference(cnf_transformation,[],[f43]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_867,plain,
% 12.00/2.04      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_12,c_9]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_7,plain,
% 12.00/2.04      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 12.00/2.04      inference(cnf_transformation,[],[f38]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_873,plain,
% 12.00/2.04      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 12.00/2.04      inference(demodulation,[status(thm)],[c_867,c_7]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_1169,plain,
% 12.00/2.04      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_0,c_873]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_1448,plain,
% 12.00/2.04      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_9,c_1169]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_760,plain,
% 12.00/2.04      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_0,c_12]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_1055,plain,
% 12.00/2.04      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_9,c_760]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_1282,plain,
% 12.00/2.04      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_1055,c_9]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_1285,plain,
% 12.00/2.04      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 12.00/2.04      inference(demodulation,[status(thm)],[c_1282,c_7]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_1473,plain,
% 12.00/2.04      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 12.00/2.04      inference(light_normalisation,[status(thm)],[c_1448,c_1285]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_8931,plain,
% 12.00/2.04      ( k2_xboole_0(k4_xboole_0(sK2,sK4),sK2) = k4_xboole_0(sK2,sK4) ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_8046,c_1473]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_1059,plain,
% 12.00/2.04      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_760,c_9]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_1061,plain,
% 12.00/2.04      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 12.00/2.04      inference(demodulation,[status(thm)],[c_1059,c_7]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_1315,plain,
% 12.00/2.04      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_1061,c_0]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_1990,plain,
% 12.00/2.04      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_9,c_1315]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_2015,plain,
% 12.00/2.04      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 12.00/2.04      inference(demodulation,[status(thm)],[c_1990,c_9]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_6035,plain,
% 12.00/2.04      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_0,c_2015]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_8933,plain,
% 12.00/2.04      ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k2_xboole_0(k4_xboole_0(sK2,sK4),sK2) ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_8046,c_6035]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_10,plain,
% 12.00/2.04      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 12.00/2.04      inference(cnf_transformation,[],[f41]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_883,plain,
% 12.00/2.04      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_10,c_9]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_7686,plain,
% 12.00/2.04      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_1055,c_883]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_7833,plain,
% 12.00/2.04      ( k2_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X1)) = X0 ),
% 12.00/2.04      inference(light_normalisation,[status(thm)],[c_7686,c_7]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_7834,plain,
% 12.00/2.04      ( k2_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X1))) = X0 ),
% 12.00/2.04      inference(demodulation,[status(thm)],[c_7833,c_10]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_762,plain,
% 12.00/2.04      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_7,c_12]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_868,plain,
% 12.00/2.04      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 12.00/2.04      inference(superposition,[status(thm)],[c_762,c_9]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_872,plain,
% 12.00/2.04      ( k2_xboole_0(X0,X0) = X0 ),
% 12.00/2.04      inference(light_normalisation,[status(thm)],[c_868,c_7]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_7835,plain,
% 12.00/2.04      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 12.00/2.04      inference(demodulation,[status(thm)],[c_7834,c_872]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_8936,plain,
% 12.00/2.04      ( k2_xboole_0(k4_xboole_0(sK2,sK4),sK2) = sK2 ),
% 12.00/2.04      inference(demodulation,[status(thm)],[c_8933,c_7835]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_8937,plain,
% 12.00/2.04      ( k4_xboole_0(sK2,sK4) = sK2 ),
% 12.00/2.04      inference(demodulation,[status(thm)],[c_8931,c_8936]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_45362,plain,
% 12.00/2.04      ( r1_tarski(sK2,sK3) = iProver_top ),
% 12.00/2.04      inference(light_normalisation,[status(thm)],[c_45261,c_8937]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_13,negated_conjecture,
% 12.00/2.04      ( ~ r1_tarski(sK2,sK3) ),
% 12.00/2.04      inference(cnf_transformation,[],[f47]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(c_18,plain,
% 12.00/2.04      ( r1_tarski(sK2,sK3) != iProver_top ),
% 12.00/2.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 12.00/2.04  
% 12.00/2.04  cnf(contradiction,plain,
% 12.00/2.04      ( $false ),
% 12.00/2.04      inference(minisat,[status(thm)],[c_45362,c_18]) ).
% 12.00/2.04  
% 12.00/2.04  
% 12.00/2.04  % SZS output end CNFRefutation for theBenchmark.p
% 12.00/2.04  
% 12.00/2.04  ------                               Statistics
% 12.00/2.04  
% 12.00/2.04  ------ General
% 12.00/2.04  
% 12.00/2.04  abstr_ref_over_cycles:                  0
% 12.00/2.04  abstr_ref_under_cycles:                 0
% 12.00/2.04  gc_basic_clause_elim:                   0
% 12.00/2.04  forced_gc_time:                         0
% 12.00/2.04  parsing_time:                           0.006
% 12.00/2.04  unif_index_cands_time:                  0.
% 12.00/2.04  unif_index_add_time:                    0.
% 12.00/2.04  orderings_time:                         0.
% 12.00/2.04  out_proof_time:                         0.01
% 12.00/2.04  total_time:                             1.199
% 12.00/2.04  num_of_symbols:                         42
% 12.00/2.04  num_of_terms:                           57392
% 12.00/2.04  
% 12.00/2.04  ------ Preprocessing
% 12.00/2.04  
% 12.00/2.04  num_of_splits:                          0
% 12.00/2.04  num_of_split_atoms:                     0
% 12.00/2.04  num_of_reused_defs:                     0
% 12.00/2.04  num_eq_ax_congr_red:                    12
% 12.00/2.04  num_of_sem_filtered_clauses:            1
% 12.00/2.04  num_of_subtypes:                        0
% 12.00/2.04  monotx_restored_types:                  0
% 12.00/2.04  sat_num_of_epr_types:                   0
% 12.00/2.04  sat_num_of_non_cyclic_types:            0
% 12.00/2.04  sat_guarded_non_collapsed_types:        0
% 12.00/2.04  num_pure_diseq_elim:                    0
% 12.00/2.04  simp_replaced_by:                       0
% 12.00/2.04  res_preprocessed:                       74
% 12.00/2.04  prep_upred:                             0
% 12.00/2.04  prep_unflattend:                        2
% 12.00/2.04  smt_new_axioms:                         0
% 12.00/2.04  pred_elim_cands:                        2
% 12.00/2.04  pred_elim:                              1
% 12.00/2.04  pred_elim_cl:                           1
% 12.00/2.04  pred_elim_cycles:                       3
% 12.00/2.04  merged_defs:                            0
% 12.00/2.04  merged_defs_ncl:                        0
% 12.00/2.04  bin_hyper_res:                          0
% 12.00/2.04  prep_cycles:                            4
% 12.00/2.04  pred_elim_time:                         0.
% 12.00/2.04  splitting_time:                         0.
% 12.00/2.04  sem_filter_time:                        0.
% 12.00/2.04  monotx_time:                            0.
% 12.00/2.04  subtype_inf_time:                       0.
% 12.00/2.04  
% 12.00/2.04  ------ Problem properties
% 12.00/2.04  
% 12.00/2.04  clauses:                                15
% 12.00/2.04  conjectures:                            2
% 12.00/2.04  epr:                                    3
% 12.00/2.04  horn:                                   14
% 12.00/2.04  ground:                                 2
% 12.00/2.04  unary:                                  8
% 12.00/2.04  binary:                                 5
% 12.00/2.04  lits:                                   24
% 12.00/2.04  lits_eq:                                6
% 12.00/2.04  fd_pure:                                0
% 12.00/2.04  fd_pseudo:                              0
% 12.00/2.04  fd_cond:                                0
% 12.00/2.04  fd_pseudo_cond:                         0
% 12.00/2.04  ac_symbols:                             0
% 12.00/2.04  
% 12.00/2.04  ------ Propositional Solver
% 12.00/2.04  
% 12.00/2.04  prop_solver_calls:                      33
% 12.00/2.04  prop_fast_solver_calls:                 565
% 12.00/2.04  smt_solver_calls:                       0
% 12.00/2.04  smt_fast_solver_calls:                  0
% 12.00/2.04  prop_num_of_clauses:                    12386
% 12.00/2.04  prop_preprocess_simplified:             18125
% 12.00/2.04  prop_fo_subsumed:                       4
% 12.00/2.04  prop_solver_time:                       0.
% 12.00/2.04  smt_solver_time:                        0.
% 12.00/2.04  smt_fast_solver_time:                   0.
% 12.00/2.04  prop_fast_solver_time:                  0.
% 12.00/2.04  prop_unsat_core_time:                   0.001
% 12.00/2.04  
% 12.00/2.04  ------ QBF
% 12.00/2.04  
% 12.00/2.04  qbf_q_res:                              0
% 12.00/2.04  qbf_num_tautologies:                    0
% 12.00/2.04  qbf_prep_cycles:                        0
% 12.00/2.04  
% 12.00/2.04  ------ BMC1
% 12.00/2.04  
% 12.00/2.04  bmc1_current_bound:                     -1
% 12.00/2.04  bmc1_last_solved_bound:                 -1
% 12.00/2.04  bmc1_unsat_core_size:                   -1
% 12.00/2.04  bmc1_unsat_core_parents_size:           -1
% 12.00/2.04  bmc1_merge_next_fun:                    0
% 12.00/2.04  bmc1_unsat_core_clauses_time:           0.
% 12.00/2.04  
% 12.00/2.04  ------ Instantiation
% 12.00/2.04  
% 12.00/2.04  inst_num_of_clauses:                    2822
% 12.00/2.04  inst_num_in_passive:                    748
% 12.00/2.04  inst_num_in_active:                     1010
% 12.00/2.04  inst_num_in_unprocessed:                1064
% 12.00/2.04  inst_num_of_loops:                      1190
% 12.00/2.04  inst_num_of_learning_restarts:          0
% 12.00/2.04  inst_num_moves_active_passive:          173
% 12.00/2.04  inst_lit_activity:                      0
% 12.00/2.04  inst_lit_activity_moves:                0
% 12.00/2.04  inst_num_tautologies:                   0
% 12.00/2.04  inst_num_prop_implied:                  0
% 12.00/2.04  inst_num_existing_simplified:           0
% 12.00/2.04  inst_num_eq_res_simplified:             0
% 12.00/2.04  inst_num_child_elim:                    0
% 12.00/2.04  inst_num_of_dismatching_blockings:      2001
% 12.00/2.04  inst_num_of_non_proper_insts:           3477
% 12.00/2.04  inst_num_of_duplicates:                 0
% 12.00/2.04  inst_inst_num_from_inst_to_res:         0
% 12.00/2.04  inst_dismatching_checking_time:         0.
% 12.00/2.04  
% 12.00/2.04  ------ Resolution
% 12.00/2.04  
% 12.00/2.04  res_num_of_clauses:                     0
% 12.00/2.04  res_num_in_passive:                     0
% 12.00/2.04  res_num_in_active:                      0
% 12.00/2.04  res_num_of_loops:                       78
% 12.00/2.04  res_forward_subset_subsumed:            310
% 12.00/2.04  res_backward_subset_subsumed:           8
% 12.00/2.04  res_forward_subsumed:                   0
% 12.00/2.04  res_backward_subsumed:                  0
% 12.00/2.04  res_forward_subsumption_resolution:     0
% 12.00/2.04  res_backward_subsumption_resolution:    0
% 12.00/2.04  res_clause_to_clause_subsumption:       50773
% 12.00/2.04  res_orphan_elimination:                 0
% 12.00/2.04  res_tautology_del:                      417
% 12.00/2.04  res_num_eq_res_simplified:              0
% 12.00/2.04  res_num_sel_changes:                    0
% 12.00/2.04  res_moves_from_active_to_pass:          0
% 12.00/2.04  
% 12.00/2.04  ------ Superposition
% 12.00/2.04  
% 12.00/2.04  sup_time_total:                         0.
% 12.00/2.04  sup_time_generating:                    0.
% 12.00/2.04  sup_time_sim_full:                      0.
% 12.00/2.04  sup_time_sim_immed:                     0.
% 12.00/2.04  
% 12.00/2.04  sup_num_of_clauses:                     2536
% 12.00/2.04  sup_num_in_active:                      229
% 12.00/2.04  sup_num_in_passive:                     2307
% 12.00/2.04  sup_num_of_loops:                       236
% 12.00/2.04  sup_fw_superposition:                   7676
% 12.00/2.04  sup_bw_superposition:                   6721
% 12.00/2.04  sup_immediate_simplified:               9070
% 12.00/2.04  sup_given_eliminated:                   1
% 12.00/2.04  comparisons_done:                       0
% 12.00/2.04  comparisons_avoided:                    0
% 12.00/2.04  
% 12.00/2.04  ------ Simplifications
% 12.00/2.04  
% 12.00/2.04  
% 12.00/2.04  sim_fw_subset_subsumed:                 4
% 12.00/2.04  sim_bw_subset_subsumed:                 0
% 12.00/2.04  sim_fw_subsumed:                        2330
% 12.00/2.04  sim_bw_subsumed:                        44
% 12.00/2.04  sim_fw_subsumption_res:                 0
% 12.00/2.04  sim_bw_subsumption_res:                 0
% 12.00/2.04  sim_tautology_del:                      39
% 12.00/2.04  sim_eq_tautology_del:                   2429
% 12.00/2.04  sim_eq_res_simp:                        0
% 12.00/2.04  sim_fw_demodulated:                     5673
% 12.00/2.04  sim_bw_demodulated:                     41
% 12.00/2.04  sim_light_normalised:                   2991
% 12.00/2.04  sim_joinable_taut:                      0
% 12.00/2.04  sim_joinable_simp:                      0
% 12.00/2.04  sim_ac_normalised:                      0
% 12.00/2.04  sim_smt_subsumption:                    0
% 12.00/2.04  
%------------------------------------------------------------------------------
