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
% DateTime   : Thu Dec  3 11:38:12 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 280 expanded)
%              Number of clauses        :   45 (  56 expanded)
%              Number of leaves         :   12 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  186 ( 498 expanded)
%              Number of equality atoms :   55 ( 185 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f19])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f23])).

fof(f38,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f41])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f42])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f43])).

fof(f40,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f40,f43,f43,f43])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f39,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f30,f43])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_401,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_402,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_398,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_405,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1037,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_398,c_405])).

cnf(c_1637,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_402,c_1037])).

cnf(c_2031,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,X0),X1) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1637,c_405])).

cnf(c_3476,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r1_tarski(sK2,X1) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_401,c_2031])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_403,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_400,plain,
    ( r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1205,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_403,c_400])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_771,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1385,plain,
    ( r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))
    | ~ r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_1387,plain,
    ( r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1385])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1386,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1389,plain,
    ( r1_tarski(sK5,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1386])).

cnf(c_814,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)))
    | ~ r1_tarski(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1409,plain,
    ( r1_tarski(sK4,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)))
    | ~ r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_1411,plain,
    ( r1_tarski(sK4,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) = iProver_top
    | r1_tarski(sK4,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1409])).

cnf(c_1410,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1413,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1410])).

cnf(c_721,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X0))
    | r1_tarski(X2,k2_zfmisc_1(X3,X1)) ),
    inference(resolution,[status(thm)],[c_7,c_4])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3748,plain,
    ( ~ r1_tarski(sK5,X0)
    | r1_tarski(sK1,k2_zfmisc_1(sK4,X0)) ),
    inference(resolution,[status(thm)],[c_721,c_10])).

cnf(c_912,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,k2_zfmisc_1(X0,X3))
    | r1_tarski(X2,k2_zfmisc_1(X1,X3)) ),
    inference(resolution,[status(thm)],[c_8,c_4])).

cnf(c_4224,plain,
    ( ~ r1_tarski(sK5,X0)
    | ~ r1_tarski(sK4,X1)
    | r1_tarski(sK1,k2_zfmisc_1(X1,X0)) ),
    inference(resolution,[status(thm)],[c_3748,c_912])).

cnf(c_1233,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    inference(resolution,[status(thm)],[c_6,c_9])).

cnf(c_5260,plain,
    ( ~ r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))
    | ~ r1_tarski(sK4,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    inference(resolution,[status(thm)],[c_4224,c_1233])).

cnf(c_5261,plain,
    ( r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))) != iProver_top
    | r1_tarski(sK4,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5260])).

cnf(c_7850,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1205,c_1387,c_1389,c_1411,c_1413,c_5261])).

cnf(c_7863,plain,
    ( r1_tarski(sK3,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))) != iProver_top
    | r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3476,c_7850])).

cnf(c_5,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_823,plain,
    ( r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_826,plain,
    ( r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_823])).

cnf(c_780,plain,
    ( r1_tarski(sK3,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_783,plain,
    ( r1_tarski(sK3,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_780])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7863,c_826,c_783])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:17:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.85/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/0.98  
% 3.85/0.98  ------  iProver source info
% 3.85/0.98  
% 3.85/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.85/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/0.98  git: non_committed_changes: false
% 3.85/0.98  git: last_make_outside_of_git: false
% 3.85/0.98  
% 3.85/0.98  ------ 
% 3.85/0.98  ------ Parsing...
% 3.85/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  ------ Proving...
% 3.85/0.98  ------ Problem Properties 
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  clauses                                 11
% 3.85/0.98  conjectures                             3
% 3.85/0.98  EPR                                     3
% 3.85/0.98  Horn                                    11
% 3.85/0.98  unary                                   5
% 3.85/0.98  binary                                  3
% 3.85/0.98  lits                                    20
% 3.85/0.98  lits eq                                 1
% 3.85/0.98  fd_pure                                 0
% 3.85/0.98  fd_pseudo                               0
% 3.85/0.98  fd_cond                                 0
% 3.85/0.98  fd_pseudo_cond                          1
% 3.85/0.98  AC symbols                              0
% 3.85/0.98  
% 3.85/0.98  ------ Input Options Time Limit: Unbounded
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ 
% 3.85/0.98  Current options:
% 3.85/0.98  ------ 
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  % SZS status Theorem for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  fof(f10,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f18,plain,(
% 3.85/0.98    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 3.85/0.98    inference(ennf_transformation,[],[f10])).
% 3.85/0.98  
% 3.85/0.98  fof(f36,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f18])).
% 3.85/0.98  
% 3.85/0.98  fof(f37,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f18])).
% 3.85/0.98  
% 3.85/0.98  fof(f11,conjecture,(
% 3.85/0.98    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f12,negated_conjecture,(
% 3.85/0.98    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 3.85/0.98    inference(negated_conjecture,[],[f11])).
% 3.85/0.98  
% 3.85/0.98  fof(f19,plain,(
% 3.85/0.98    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 3.85/0.98    inference(ennf_transformation,[],[f12])).
% 3.85/0.98  
% 3.85/0.98  fof(f20,plain,(
% 3.85/0.98    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 3.85/0.98    inference(flattening,[],[f19])).
% 3.85/0.98  
% 3.85/0.98  fof(f23,plain,(
% 3.85/0.98    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 3.85/0.98    introduced(choice_axiom,[])).
% 3.85/0.98  
% 3.85/0.98  fof(f24,plain,(
% 3.85/0.98    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 3.85/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f23])).
% 3.85/0.98  
% 3.85/0.98  fof(f38,plain,(
% 3.85/0.98    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 3.85/0.98    inference(cnf_transformation,[],[f24])).
% 3.85/0.98  
% 3.85/0.98  fof(f3,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f14,plain,(
% 3.85/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.85/0.98    inference(ennf_transformation,[],[f3])).
% 3.85/0.98  
% 3.85/0.98  fof(f15,plain,(
% 3.85/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.85/0.98    inference(flattening,[],[f14])).
% 3.85/0.98  
% 3.85/0.98  fof(f29,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f15])).
% 3.85/0.98  
% 3.85/0.98  fof(f5,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f16,plain,(
% 3.85/0.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.85/0.98    inference(ennf_transformation,[],[f5])).
% 3.85/0.98  
% 3.85/0.98  fof(f17,plain,(
% 3.85/0.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.85/0.98    inference(flattening,[],[f16])).
% 3.85/0.98  
% 3.85/0.98  fof(f31,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f17])).
% 3.85/0.98  
% 3.85/0.98  fof(f9,axiom,(
% 3.85/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f35,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f9])).
% 3.85/0.98  
% 3.85/0.98  fof(f6,axiom,(
% 3.85/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f32,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f6])).
% 3.85/0.98  
% 3.85/0.98  fof(f7,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f33,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f7])).
% 3.85/0.98  
% 3.85/0.98  fof(f8,axiom,(
% 3.85/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f34,plain,(
% 3.85/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f8])).
% 3.85/0.98  
% 3.85/0.98  fof(f41,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f33,f34])).
% 3.85/0.98  
% 3.85/0.98  fof(f42,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f32,f41])).
% 3.85/0.98  
% 3.85/0.98  fof(f43,plain,(
% 3.85/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 3.85/0.98    inference(definition_unfolding,[],[f35,f42])).
% 3.85/0.98  
% 3.85/0.98  fof(f46,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f31,f43])).
% 3.85/0.98  
% 3.85/0.98  fof(f40,plain,(
% 3.85/0.98    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 3.85/0.98    inference(cnf_transformation,[],[f24])).
% 3.85/0.98  
% 3.85/0.98  fof(f47,plain,(
% 3.85/0.98    ~r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 3.85/0.98    inference(definition_unfolding,[],[f40,f43,f43,f43])).
% 3.85/0.98  
% 3.85/0.98  fof(f2,axiom,(
% 3.85/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f13,plain,(
% 3.85/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.85/0.98    inference(ennf_transformation,[],[f2])).
% 3.85/0.98  
% 3.85/0.98  fof(f28,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.85/0.98    inference(cnf_transformation,[],[f13])).
% 3.85/0.98  
% 3.85/0.98  fof(f44,plain,(
% 3.85/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 3.85/0.98    inference(definition_unfolding,[],[f28,f43])).
% 3.85/0.98  
% 3.85/0.98  fof(f1,axiom,(
% 3.85/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f21,plain,(
% 3.85/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.85/0.98    inference(nnf_transformation,[],[f1])).
% 3.85/0.98  
% 3.85/0.98  fof(f22,plain,(
% 3.85/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.85/0.98    inference(flattening,[],[f21])).
% 3.85/0.98  
% 3.85/0.98  fof(f26,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.85/0.98    inference(cnf_transformation,[],[f22])).
% 3.85/0.98  
% 3.85/0.98  fof(f48,plain,(
% 3.85/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.85/0.98    inference(equality_resolution,[],[f26])).
% 3.85/0.98  
% 3.85/0.98  fof(f39,plain,(
% 3.85/0.98    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 3.85/0.98    inference(cnf_transformation,[],[f24])).
% 3.85/0.98  
% 3.85/0.98  fof(f4,axiom,(
% 3.85/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.85/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f30,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.85/0.98    inference(cnf_transformation,[],[f4])).
% 3.85/0.98  
% 3.85/0.98  fof(f45,plain,(
% 3.85/0.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 3.85/0.98    inference(definition_unfolding,[],[f30,f43])).
% 3.85/0.98  
% 3.85/0.98  cnf(c_8,plain,
% 3.85/0.98      ( ~ r1_tarski(X0,X1)
% 3.85/0.98      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_401,plain,
% 3.85/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.85/0.98      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_7,plain,
% 3.85/0.98      ( ~ r1_tarski(X0,X1)
% 3.85/0.98      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_402,plain,
% 3.85/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.85/0.98      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_11,negated_conjecture,
% 3.85/0.98      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
% 3.85/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_398,plain,
% 3.85/0.98      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_4,plain,
% 3.85/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.85/0.98      inference(cnf_transformation,[],[f29]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_405,plain,
% 3.85/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.85/0.98      | r1_tarski(X1,X2) != iProver_top
% 3.85/0.98      | r1_tarski(X0,X2) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1037,plain,
% 3.85/0.98      ( r1_tarski(k2_zfmisc_1(sK2,sK3),X0) != iProver_top
% 3.85/0.98      | r1_tarski(sK0,X0) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_398,c_405]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1637,plain,
% 3.85/0.98      ( r1_tarski(sK3,X0) != iProver_top
% 3.85/0.98      | r1_tarski(sK0,k2_zfmisc_1(sK2,X0)) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_402,c_1037]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_2031,plain,
% 3.85/0.98      ( r1_tarski(k2_zfmisc_1(sK2,X0),X1) != iProver_top
% 3.85/0.98      | r1_tarski(sK3,X0) != iProver_top
% 3.85/0.98      | r1_tarski(sK0,X1) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_1637,c_405]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3476,plain,
% 3.85/0.98      ( r1_tarski(sK3,X0) != iProver_top
% 3.85/0.98      | r1_tarski(sK2,X1) != iProver_top
% 3.85/0.98      | r1_tarski(sK0,k2_zfmisc_1(X1,X0)) = iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_401,c_2031]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_6,plain,
% 3.85/0.98      ( ~ r1_tarski(X0,X1)
% 3.85/0.98      | ~ r1_tarski(X2,X1)
% 3.85/0.98      | r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) ),
% 3.85/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_403,plain,
% 3.85/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.85/0.98      | r1_tarski(X2,X1) != iProver_top
% 3.85/0.98      | r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) = iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_9,negated_conjecture,
% 3.85/0.98      ( ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
% 3.85/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_400,plain,
% 3.85/0.98      ( r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1205,plain,
% 3.85/0.98      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top
% 3.85/0.98      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top ),
% 3.85/0.98      inference(superposition,[status(thm)],[c_403,c_400]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_3,plain,
% 3.85/0.98      ( ~ r1_tarski(X0,X1)
% 3.85/0.98      | r1_tarski(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
% 3.85/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_771,plain,
% 3.85/0.98      ( r1_tarski(X0,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))
% 3.85/0.98      | ~ r1_tarski(X0,sK5) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1385,plain,
% 3.85/0.98      ( r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))
% 3.85/0.98      | ~ r1_tarski(sK5,sK5) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_771]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1387,plain,
% 3.85/0.98      ( r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))) = iProver_top
% 3.85/0.98      | r1_tarski(sK5,sK5) != iProver_top ),
% 3.85/0.98      inference(predicate_to_equality,[status(thm)],[c_1385]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1,plain,
% 3.85/0.98      ( r1_tarski(X0,X0) ),
% 3.85/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1386,plain,
% 3.85/0.98      ( r1_tarski(sK5,sK5) ),
% 3.85/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.85/0.98  
% 3.85/0.98  cnf(c_1389,plain,
% 3.85/0.99      ( r1_tarski(sK5,sK5) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1386]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_814,plain,
% 3.85/0.99      ( r1_tarski(X0,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)))
% 3.85/0.99      | ~ r1_tarski(X0,sK4) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1409,plain,
% 3.85/0.99      ( r1_tarski(sK4,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)))
% 3.85/0.99      | ~ r1_tarski(sK4,sK4) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_814]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1411,plain,
% 3.85/0.99      ( r1_tarski(sK4,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) = iProver_top
% 3.85/0.99      | r1_tarski(sK4,sK4) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1409]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1410,plain,
% 3.85/0.99      ( r1_tarski(sK4,sK4) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1413,plain,
% 3.85/0.99      ( r1_tarski(sK4,sK4) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1410]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_721,plain,
% 3.85/0.99      ( ~ r1_tarski(X0,X1)
% 3.85/0.99      | ~ r1_tarski(X2,k2_zfmisc_1(X3,X0))
% 3.85/0.99      | r1_tarski(X2,k2_zfmisc_1(X3,X1)) ),
% 3.85/0.99      inference(resolution,[status(thm)],[c_7,c_4]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_10,negated_conjecture,
% 3.85/0.99      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
% 3.85/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3748,plain,
% 3.85/0.99      ( ~ r1_tarski(sK5,X0) | r1_tarski(sK1,k2_zfmisc_1(sK4,X0)) ),
% 3.85/0.99      inference(resolution,[status(thm)],[c_721,c_10]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_912,plain,
% 3.85/0.99      ( ~ r1_tarski(X0,X1)
% 3.85/0.99      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X3))
% 3.85/0.99      | r1_tarski(X2,k2_zfmisc_1(X1,X3)) ),
% 3.85/0.99      inference(resolution,[status(thm)],[c_8,c_4]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_4224,plain,
% 3.85/0.99      ( ~ r1_tarski(sK5,X0)
% 3.85/0.99      | ~ r1_tarski(sK4,X1)
% 3.85/0.99      | r1_tarski(sK1,k2_zfmisc_1(X1,X0)) ),
% 3.85/0.99      inference(resolution,[status(thm)],[c_3748,c_912]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1233,plain,
% 3.85/0.99      ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))
% 3.85/0.99      | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
% 3.85/0.99      inference(resolution,[status(thm)],[c_6,c_9]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_5260,plain,
% 3.85/0.99      ( ~ r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))
% 3.85/0.99      | ~ r1_tarski(sK4,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)))
% 3.85/0.99      | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
% 3.85/0.99      inference(resolution,[status(thm)],[c_4224,c_1233]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_5261,plain,
% 3.85/0.99      ( r1_tarski(sK5,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))) != iProver_top
% 3.85/0.99      | r1_tarski(sK4,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) != iProver_top
% 3.85/0.99      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_5260]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7850,plain,
% 3.85/0.99      ( r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) != iProver_top ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_1205,c_1387,c_1389,c_1411,c_1413,c_5261]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7863,plain,
% 3.85/0.99      ( r1_tarski(sK3,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))) != iProver_top
% 3.85/0.99      | r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_3476,c_7850]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_5,plain,
% 3.85/0.99      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 3.85/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_823,plain,
% 3.85/0.99      ( r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_826,plain,
% 3.85/0.99      ( r1_tarski(sK2,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4))) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_823]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_780,plain,
% 3.85/0.99      ( r1_tarski(sK3,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_783,plain,
% 3.85/0.99      ( r1_tarski(sK3,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_780]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(contradiction,plain,
% 3.85/0.99      ( $false ),
% 3.85/0.99      inference(minisat,[status(thm)],[c_7863,c_826,c_783]) ).
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  ------                               Statistics
% 3.85/0.99  
% 3.85/0.99  ------ Selected
% 3.85/0.99  
% 3.85/0.99  total_time:                             0.425
% 3.85/0.99  
%------------------------------------------------------------------------------
