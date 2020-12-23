%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:40 EST 2020

% Result     : Theorem 15.33s
% Output     : CNFRefutation 15.33s
% Verified   : 
% Statistics : Number of formulae       :  165 (9944 expanded)
%              Number of clauses        :  119 (3196 expanded)
%              Number of leaves         :   14 (2472 expanded)
%              Depth                    :   47
%              Number of atoms          :  283 (25199 expanded)
%              Number of equality atoms :  258 (24797 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f23])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK3 != sK5
        | sK2 != sK4 )
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( sK3 != sK5
      | sK2 != sK4 )
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f35])).

fof(f61,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
      & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f50,f50])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(definition_unfolding,[],[f58,f50,f50,f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f33])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f63,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,
    ( sK3 != sK5
    | sK2 != sK4 ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_26,negated_conjecture,
    ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_21,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1159,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK4,X0),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(sK4,k4_xboole_0(X0,sK5)) ),
    inference(superposition,[status(thm)],[c_26,c_21])).

cnf(c_22,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1525,plain,
    ( k2_zfmisc_1(sK4,k4_xboole_0(sK3,sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_1159,c_22])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_659,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9,c_12])).

cnf(c_1360,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X0,sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5) ),
    inference(superposition,[status(thm)],[c_26,c_22])).

cnf(c_1550,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK5) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5)) ),
    inference(superposition,[status(thm)],[c_1360,c_21])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1367,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k4_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k4_xboole_0(X2,X0),X1)) ),
    inference(superposition,[status(thm)],[c_22,c_0])).

cnf(c_1371,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k4_xboole_0(X0,X2),X1)) = k4_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k4_xboole_0(X2,X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_1367,c_22])).

cnf(c_15606,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5))) = k4_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(k4_xboole_0(sK2,sK4),sK5)) ),
    inference(superposition,[status(thm)],[c_1550,c_1371])).

cnf(c_1363,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_26,c_22])).

cnf(c_1789,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK2,sK4),sK5) = k2_zfmisc_1(sK2,k4_xboole_0(sK5,sK3)) ),
    inference(superposition,[status(thm)],[c_1363,c_21])).

cnf(c_15729,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK5,sK3))) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5))) ),
    inference(light_normalisation,[status(thm)],[c_15606,c_26,c_1789])).

cnf(c_15730,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) ),
    inference(demodulation,[status(thm)],[c_15729,c_21])).

cnf(c_11,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_635,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2722,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_635])).

cnf(c_3817,plain,
    ( r1_tarski(k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k4_xboole_0(X0,X2),X1)),k2_zfmisc_1(X2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_2722])).

cnf(c_3841,plain,
    ( r1_tarski(k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3817,c_22])).

cnf(c_17236,plain,
    ( r1_tarski(k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_15730,c_3841])).

cnf(c_20,plain,
    ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_17240,plain,
    ( r1_tarski(k4_xboole_0(k2_zfmisc_1(X0,sK5),k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(sK2,sK3))),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17236,c_20])).

cnf(c_1788,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X0,sK5))) = k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5)) ),
    inference(superposition,[status(thm)],[c_1363,c_0])).

cnf(c_1794,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5)) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5)) ),
    inference(light_normalisation,[status(thm)],[c_1788,c_1360])).

cnf(c_1795,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),sK5) ),
    inference(demodulation,[status(thm)],[c_1794,c_22,c_1360])).

cnf(c_17241,plain,
    ( r1_tarski(k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17240,c_1363,c_1795])).

cnf(c_17691,plain,
    ( r1_tarski(k2_zfmisc_1(k4_xboole_0(sK4,k1_xboole_0),sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_659,c_17241])).

cnf(c_17696,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17691,c_12,c_26])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_637,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_17717,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17696,c_637])).

cnf(c_18024,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17717,c_21])).

cnf(c_17,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_18742,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18024,c_17])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_34,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_35,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_305,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_796,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_797,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_19012,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18742,c_25,c_34,c_35,c_797])).

cnf(c_19033,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK3),k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,k4_xboole_0(sK3,sK5)))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_19012,c_20])).

cnf(c_15,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_19049,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,sK3),k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19033,c_15])).

cnf(c_35066,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK4,k4_xboole_0(sK3,sK5)),k4_xboole_0(k2_zfmisc_1(sK4,k4_xboole_0(sK3,sK5)),k2_zfmisc_1(X0,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1525,c_19049])).

cnf(c_35158,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35066,c_22])).

cnf(c_35432,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,X0)) = k1_xboole_0
    | k4_xboole_0(sK3,sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_35158,c_17])).

cnf(c_3813,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2722])).

cnf(c_9741,plain,
    ( r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k2_zfmisc_1(X0,sK5),k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(sK2,sK3)))),k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1360,c_3813])).

cnf(c_9788,plain,
    ( r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),sK5)),k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9741,c_1363,c_1795])).

cnf(c_9789,plain,
    ( r1_tarski(k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK4,X0))),sK5),k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9788,c_1360])).

cnf(c_45424,plain,
    ( k4_xboole_0(sK3,sK5) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(k4_xboole_0(sK4,k1_xboole_0),sK5),k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_35432,c_9789])).

cnf(c_45563,plain,
    ( k4_xboole_0(sK3,sK5) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_45424,c_12,c_26])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_778,plain,
    ( k2_zfmisc_1(X0,sK3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_924,plain,
    ( k2_zfmisc_1(sK2,sK3) != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1258,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK3))
    | k2_zfmisc_1(sK2,sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1259,plain,
    ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK2,sK3),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1258])).

cnf(c_1156,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,X0)) = k2_zfmisc_1(sK4,k4_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_26,c_21])).

cnf(c_2728,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,k4_xboole_0(sK5,X0)),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1156,c_635])).

cnf(c_4146,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,k1_xboole_0),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_659,c_2728])).

cnf(c_4151,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4146,c_15])).

cnf(c_3346,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5))) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),sK5) ),
    inference(superposition,[status(thm)],[c_1550,c_1360])).

cnf(c_3348,plain,
    ( k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),sK5) ),
    inference(demodulation,[status(thm)],[c_3346,c_21])).

cnf(c_15841,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),X0)) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(sK5,X0)) ),
    inference(superposition,[status(thm)],[c_3348,c_21])).

cnf(c_1163,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,k4_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_21,c_0])).

cnf(c_1164,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,k4_xboole_0(X2,X1))) ),
    inference(light_normalisation,[status(thm)],[c_1163,c_21])).

cnf(c_15843,plain,
    ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),X0),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(X0,sK5))) = k4_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(sK5,X0))) ),
    inference(superposition,[status(thm)],[c_3348,c_1164])).

cnf(c_15959,plain,
    ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),X0),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(X0,sK5))) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(sK5,k4_xboole_0(sK5,X0))) ),
    inference(demodulation,[status(thm)],[c_15841,c_15843])).

cnf(c_15962,plain,
    ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),X0),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(X0,sK5))) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) ),
    inference(demodulation,[status(thm)],[c_15959,c_20,c_21,c_26])).

cnf(c_16898,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15962,c_635])).

cnf(c_17340,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK3,k1_xboole_0)),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_659,c_16898])).

cnf(c_17360,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17340,c_12])).

cnf(c_45439,plain,
    ( k4_xboole_0(sK3,sK5) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k1_xboole_0,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_35432,c_17360])).

cnf(c_45517,plain,
    ( k4_xboole_0(sK3,sK5) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK2,sK3),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_45439,c_16])).

cnf(c_46864,plain,
    ( k4_xboole_0(sK3,sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_45563,c_25,c_24,c_924,c_1259,c_4151,c_45517])).

cnf(c_47008,plain,
    ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),sK3),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k1_xboole_0)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_46864,c_15962])).

cnf(c_47029,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),sK3) = k2_zfmisc_1(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_47008,c_12,c_15,c_21,c_659])).

cnf(c_46903,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK5) = k2_zfmisc_1(sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_46864,c_1550])).

cnf(c_46905,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK5) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_46903,c_15])).

cnf(c_47850,plain,
    ( k4_xboole_0(sK4,sK2) = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_46905,c_17])).

cnf(c_794,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_305])).

cnf(c_795,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_3270,plain,
    ( k2_zfmisc_1(sK4,k4_xboole_0(sK3,sK5)) != k1_xboole_0
    | k4_xboole_0(sK4,sK2) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1525,c_17])).

cnf(c_35420,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK4,k1_xboole_0),k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_659,c_35158])).

cnf(c_35606,plain,
    ( k2_zfmisc_1(sK4,k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35420,c_12])).

cnf(c_48635,plain,
    ( k4_xboole_0(sK4,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_47850,c_24,c_34,c_35,c_795,c_3270,c_35606])).

cnf(c_54322,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK4,k1_xboole_0),sK3) = k2_zfmisc_1(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_47029,c_48635])).

cnf(c_54323,plain,
    ( k2_zfmisc_1(sK4,sK3) = k2_zfmisc_1(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_54322,c_12])).

cnf(c_54387,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) ),
    inference(superposition,[status(thm)],[c_54323,c_1156])).

cnf(c_54393,plain,
    ( k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_54387,c_15,c_21,c_659])).

cnf(c_56180,plain,
    ( k4_xboole_0(sK5,sK3) = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_54393,c_17])).

cnf(c_56408,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK5,k1_xboole_0)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_56180,c_0])).

cnf(c_56596,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0)
    | sK4 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_56408,c_46864])).

cnf(c_56597,plain,
    ( sK4 = k1_xboole_0
    | sK5 = sK3 ),
    inference(demodulation,[status(thm)],[c_56596,c_12])).

cnf(c_4796,plain,
    ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,sK4)),sK5) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),sK5) ),
    inference(superposition,[status(thm)],[c_1795,c_22])).

cnf(c_25583,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK4))),sK5) ),
    inference(superposition,[status(thm)],[c_4796,c_1360])).

cnf(c_56802,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK4))),sK5)
    | sK5 = sK3 ),
    inference(superposition,[status(thm)],[c_56597,c_25583])).

cnf(c_1033,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_12,c_0])).

cnf(c_3769,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1033,c_659])).

cnf(c_57537,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK4))),sK5) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k1_xboole_0,sK5))
    | sK5 = sK3 ),
    inference(light_normalisation,[status(thm)],[c_56802,c_3769])).

cnf(c_57538,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK4))),sK5) = k2_zfmisc_1(sK2,sK3)
    | sK5 = sK3 ),
    inference(demodulation,[status(thm)],[c_57537,c_12,c_26,c_1360])).

cnf(c_56995,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK5) = k2_zfmisc_1(sK2,sK3)
    | sK5 = sK3 ),
    inference(superposition,[status(thm)],[c_56597,c_26])).

cnf(c_56998,plain,
    ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | sK5 = sK3 ),
    inference(demodulation,[status(thm)],[c_56995,c_16])).

cnf(c_57680,plain,
    ( sK5 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_57538,c_25,c_24,c_924,c_56998])).

cnf(c_23,negated_conjecture,
    ( sK2 != sK4
    | sK3 != sK5 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_57805,plain,
    ( sK4 != sK2
    | sK3 != sK3 ),
    inference(demodulation,[status(thm)],[c_57680,c_23])).

cnf(c_57807,plain,
    ( sK4 != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_57805])).

cnf(c_10,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_48706,plain,
    ( k4_xboole_0(sK2,sK4) != k1_xboole_0
    | sK4 = sK2 ),
    inference(superposition,[status(thm)],[c_48635,c_10])).

cnf(c_1402,plain,
    ( k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) = k2_zfmisc_1(k4_xboole_0(sK2,sK4),sK3) ),
    inference(superposition,[status(thm)],[c_1156,c_22])).

cnf(c_2419,plain,
    ( k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) != k1_xboole_0
    | k4_xboole_0(sK2,sK4) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1402,c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_57807,c_54393,c_48706,c_2419,c_795,c_35,c_34,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:53:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.33/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.33/2.49  
% 15.33/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.33/2.49  
% 15.33/2.49  ------  iProver source info
% 15.33/2.49  
% 15.33/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.33/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.33/2.49  git: non_committed_changes: false
% 15.33/2.49  git: last_make_outside_of_git: false
% 15.33/2.49  
% 15.33/2.49  ------ 
% 15.33/2.49  ------ Parsing...
% 15.33/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.33/2.49  
% 15.33/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.33/2.49  
% 15.33/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.33/2.49  
% 15.33/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.33/2.49  ------ Proving...
% 15.33/2.49  ------ Problem Properties 
% 15.33/2.49  
% 15.33/2.49  
% 15.33/2.49  clauses                                 26
% 15.33/2.49  conjectures                             4
% 15.33/2.49  EPR                                     5
% 15.33/2.49  Horn                                    21
% 15.33/2.49  unary                                   13
% 15.33/2.49  binary                                  9
% 15.33/2.49  lits                                    43
% 15.33/2.49  lits eq                                 26
% 15.33/2.49  fd_pure                                 0
% 15.33/2.49  fd_pseudo                               0
% 15.33/2.49  fd_cond                                 4
% 15.33/2.49  fd_pseudo_cond                          2
% 15.33/2.49  AC symbols                              0
% 15.33/2.49  
% 15.33/2.49  ------ Input Options Time Limit: Unbounded
% 15.33/2.49  
% 15.33/2.49  
% 15.33/2.49  ------ 
% 15.33/2.49  Current options:
% 15.33/2.49  ------ 
% 15.33/2.49  
% 15.33/2.49  
% 15.33/2.49  
% 15.33/2.49  
% 15.33/2.49  ------ Proving...
% 15.33/2.49  
% 15.33/2.49  
% 15.33/2.49  % SZS status Theorem for theBenchmark.p
% 15.33/2.49  
% 15.33/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.33/2.49  
% 15.33/2.49  fof(f16,conjecture,(
% 15.33/2.49    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.33/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f17,negated_conjecture,(
% 15.33/2.49    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.33/2.49    inference(negated_conjecture,[],[f16])).
% 15.33/2.49  
% 15.33/2.49  fof(f23,plain,(
% 15.33/2.49    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 15.33/2.49    inference(ennf_transformation,[],[f17])).
% 15.33/2.49  
% 15.33/2.49  fof(f24,plain,(
% 15.33/2.49    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 15.33/2.49    inference(flattening,[],[f23])).
% 15.33/2.49  
% 15.33/2.49  fof(f35,plain,(
% 15.33/2.49    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK3 != sK5 | sK2 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5))),
% 15.33/2.49    introduced(choice_axiom,[])).
% 15.33/2.49  
% 15.33/2.49  fof(f36,plain,(
% 15.33/2.49    (sK3 != sK5 | sK2 != sK4) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5)),
% 15.33/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f24,f35])).
% 15.33/2.49  
% 15.33/2.49  fof(f61,plain,(
% 15.33/2.49    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5)),
% 15.33/2.49    inference(cnf_transformation,[],[f36])).
% 15.33/2.49  
% 15.33/2.49  fof(f15,axiom,(
% 15.33/2.49    ! [X0,X1,X2] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2))),
% 15.33/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f60,plain,(
% 15.33/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))) )),
% 15.33/2.49    inference(cnf_transformation,[],[f15])).
% 15.33/2.49  
% 15.33/2.49  fof(f59,plain,(
% 15.33/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f15])).
% 15.33/2.49  
% 15.33/2.49  fof(f6,axiom,(
% 15.33/2.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 15.33/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f46,plain,(
% 15.33/2.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 15.33/2.49    inference(cnf_transformation,[],[f6])).
% 15.33/2.49  
% 15.33/2.49  fof(f10,axiom,(
% 15.33/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 15.33/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f50,plain,(
% 15.33/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 15.33/2.49    inference(cnf_transformation,[],[f10])).
% 15.33/2.49  
% 15.33/2.49  fof(f68,plain,(
% 15.33/2.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 15.33/2.49    inference(definition_unfolding,[],[f46,f50])).
% 15.33/2.49  
% 15.33/2.49  fof(f9,axiom,(
% 15.33/2.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 15.33/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f49,plain,(
% 15.33/2.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.33/2.49    inference(cnf_transformation,[],[f9])).
% 15.33/2.49  
% 15.33/2.49  fof(f1,axiom,(
% 15.33/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.33/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f37,plain,(
% 15.33/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f1])).
% 15.33/2.49  
% 15.33/2.49  fof(f65,plain,(
% 15.33/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 15.33/2.49    inference(definition_unfolding,[],[f37,f50,f50])).
% 15.33/2.49  
% 15.33/2.49  fof(f8,axiom,(
% 15.33/2.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.33/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f48,plain,(
% 15.33/2.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f8])).
% 15.33/2.49  
% 15.33/2.49  fof(f14,axiom,(
% 15.33/2.49    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))),
% 15.33/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f58,plain,(
% 15.33/2.49    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))) )),
% 15.33/2.49    inference(cnf_transformation,[],[f14])).
% 15.33/2.49  
% 15.33/2.49  fof(f69,plain,(
% 15.33/2.49    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 15.33/2.49    inference(definition_unfolding,[],[f58,f50,f50,f50])).
% 15.33/2.49  
% 15.33/2.49  fof(f5,axiom,(
% 15.33/2.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 15.33/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f31,plain,(
% 15.33/2.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 15.33/2.49    inference(nnf_transformation,[],[f5])).
% 15.33/2.49  
% 15.33/2.49  fof(f45,plain,(
% 15.33/2.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f31])).
% 15.33/2.49  
% 15.33/2.49  fof(f12,axiom,(
% 15.33/2.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.33/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f33,plain,(
% 15.33/2.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.33/2.49    inference(nnf_transformation,[],[f12])).
% 15.33/2.49  
% 15.33/2.49  fof(f34,plain,(
% 15.33/2.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.33/2.49    inference(flattening,[],[f33])).
% 15.33/2.49  
% 15.33/2.49  fof(f53,plain,(
% 15.33/2.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f34])).
% 15.33/2.49  
% 15.33/2.49  fof(f62,plain,(
% 15.33/2.49    k1_xboole_0 != sK2),
% 15.33/2.49    inference(cnf_transformation,[],[f36])).
% 15.33/2.49  
% 15.33/2.49  fof(f54,plain,(
% 15.33/2.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 15.33/2.49    inference(cnf_transformation,[],[f34])).
% 15.33/2.49  
% 15.33/2.49  fof(f73,plain,(
% 15.33/2.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 15.33/2.49    inference(equality_resolution,[],[f54])).
% 15.33/2.49  
% 15.33/2.49  fof(f55,plain,(
% 15.33/2.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 15.33/2.49    inference(cnf_transformation,[],[f34])).
% 15.33/2.49  
% 15.33/2.49  fof(f72,plain,(
% 15.33/2.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 15.33/2.49    inference(equality_resolution,[],[f55])).
% 15.33/2.49  
% 15.33/2.49  fof(f63,plain,(
% 15.33/2.49    k1_xboole_0 != sK3),
% 15.33/2.49    inference(cnf_transformation,[],[f36])).
% 15.33/2.49  
% 15.33/2.49  fof(f4,axiom,(
% 15.33/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.33/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f29,plain,(
% 15.33/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.33/2.49    inference(nnf_transformation,[],[f4])).
% 15.33/2.49  
% 15.33/2.49  fof(f30,plain,(
% 15.33/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.33/2.49    inference(flattening,[],[f29])).
% 15.33/2.49  
% 15.33/2.49  fof(f43,plain,(
% 15.33/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f30])).
% 15.33/2.49  
% 15.33/2.49  fof(f64,plain,(
% 15.33/2.49    sK3 != sK5 | sK2 != sK4),
% 15.33/2.49    inference(cnf_transformation,[],[f36])).
% 15.33/2.49  
% 15.33/2.49  fof(f7,axiom,(
% 15.33/2.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 15.33/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f21,plain,(
% 15.33/2.49    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 15.33/2.49    inference(ennf_transformation,[],[f7])).
% 15.33/2.49  
% 15.33/2.49  fof(f47,plain,(
% 15.33/2.49    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f21])).
% 15.33/2.49  
% 15.33/2.49  cnf(c_26,negated_conjecture,
% 15.33/2.49      ( k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK4,sK5) ),
% 15.33/2.49      inference(cnf_transformation,[],[f61]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_21,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k4_xboole_0(X1,X2)) ),
% 15.33/2.49      inference(cnf_transformation,[],[f60]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1159,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(sK4,X0),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(sK4,k4_xboole_0(X0,sK5)) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_26,c_21]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_22,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k4_xboole_0(X0,X2),X1) ),
% 15.33/2.49      inference(cnf_transformation,[],[f59]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1525,plain,
% 15.33/2.49      ( k2_zfmisc_1(sK4,k4_xboole_0(sK3,sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK3) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1159,c_22]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_9,plain,
% 15.33/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 15.33/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_12,plain,
% 15.33/2.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.33/2.49      inference(cnf_transformation,[],[f49]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_659,plain,
% 15.33/2.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_9,c_12]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1360,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X0,sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_26,c_22]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1550,plain,
% 15.33/2.49      ( k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK5) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5)) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1360,c_21]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_0,plain,
% 15.33/2.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 15.33/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1367,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1))) = k4_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k4_xboole_0(X2,X0),X1)) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_22,c_0]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1371,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k4_xboole_0(X0,X2),X1)) = k4_xboole_0(k2_zfmisc_1(X2,X1),k2_zfmisc_1(k4_xboole_0(X2,X0),X1)) ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_1367,c_22]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_15606,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(sK4,sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5))) = k4_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(k4_xboole_0(sK2,sK4),sK5)) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1550,c_1371]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1363,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_26,c_22]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1789,plain,
% 15.33/2.49      ( k2_zfmisc_1(k4_xboole_0(sK2,sK4),sK5) = k2_zfmisc_1(sK2,k4_xboole_0(sK5,sK3)) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1363,c_21]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_15729,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(sK2,sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK5,sK3))) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5))) ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_15606,c_26,c_1789]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_15730,plain,
% 15.33/2.49      ( k2_zfmisc_1(sK2,k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_15729,c_21]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_11,plain,
% 15.33/2.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 15.33/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_635,plain,
% 15.33/2.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_2722,plain,
% 15.33/2.49      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_0,c_635]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_3817,plain,
% 15.33/2.49      ( r1_tarski(k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k4_xboole_0(X0,X2),X1)),k2_zfmisc_1(X2,X1)) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_22,c_2722]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_3841,plain,
% 15.33/2.49      ( r1_tarski(k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2),k2_zfmisc_1(X1,X2)) = iProver_top ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_3817,c_22]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_17236,plain,
% 15.33/2.49      ( r1_tarski(k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),k4_xboole_0(sK5,k4_xboole_0(sK5,sK3))),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_15730,c_3841]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_20,plain,
% 15.33/2.49      ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
% 15.33/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_17240,plain,
% 15.33/2.49      ( r1_tarski(k4_xboole_0(k2_zfmisc_1(X0,sK5),k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(sK2,sK3))),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = iProver_top ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_17236,c_20]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1788,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X0,sK5))) = k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5)) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1363,c_0]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1794,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5)) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5)) ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_1788,c_1360]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1795,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(k4_xboole_0(X0,sK4),sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),sK5) ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_1794,c_22,c_1360]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_17241,plain,
% 15.33/2.49      ( r1_tarski(k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = iProver_top ),
% 15.33/2.49      inference(light_normalisation,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_17240,c_1363,c_1795]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_17691,plain,
% 15.33/2.49      ( r1_tarski(k2_zfmisc_1(k4_xboole_0(sK4,k1_xboole_0),sK5),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_659,c_17241]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_17696,plain,
% 15.33/2.49      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = iProver_top ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_17691,c_12,c_26]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_7,plain,
% 15.33/2.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 15.33/2.49      inference(cnf_transformation,[],[f45]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_637,plain,
% 15.33/2.49      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 15.33/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_17717,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_17696,c_637]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_18024,plain,
% 15.33/2.49      ( k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_17717,c_21]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_17,plain,
% 15.33/2.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 15.33/2.49      | k1_xboole_0 = X0
% 15.33/2.49      | k1_xboole_0 = X1 ),
% 15.33/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_18742,plain,
% 15.33/2.49      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) = k1_xboole_0
% 15.33/2.49      | sK2 = k1_xboole_0 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_18024,c_17]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_25,negated_conjecture,
% 15.33/2.49      ( k1_xboole_0 != sK2 ),
% 15.33/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_34,plain,
% 15.33/2.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 15.33/2.49      | k1_xboole_0 = k1_xboole_0 ),
% 15.33/2.49      inference(instantiation,[status(thm)],[c_17]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_16,plain,
% 15.33/2.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.33/2.49      inference(cnf_transformation,[],[f73]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_35,plain,
% 15.33/2.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 15.33/2.49      inference(instantiation,[status(thm)],[c_16]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_305,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_796,plain,
% 15.33/2.49      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 15.33/2.49      inference(instantiation,[status(thm)],[c_305]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_797,plain,
% 15.33/2.49      ( sK2 != k1_xboole_0
% 15.33/2.49      | k1_xboole_0 = sK2
% 15.33/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.33/2.49      inference(instantiation,[status(thm)],[c_796]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_19012,plain,
% 15.33/2.49      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) = k1_xboole_0 ),
% 15.33/2.49      inference(global_propositional_subsumption,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_18742,c_25,c_34,c_35,c_797]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_19033,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(X0,sK3),k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,k4_xboole_0(sK3,sK5)))) = k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_19012,c_20]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_15,plain,
% 15.33/2.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.33/2.49      inference(cnf_transformation,[],[f72]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_19049,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(X0,sK3),k4_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(X1,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_19033,c_15]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_35066,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(sK4,k4_xboole_0(sK3,sK5)),k4_xboole_0(k2_zfmisc_1(sK4,k4_xboole_0(sK3,sK5)),k2_zfmisc_1(X0,k4_xboole_0(sK3,sK5)))) = k1_xboole_0 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1525,c_19049]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_35158,plain,
% 15.33/2.49      ( k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_35066,c_22]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_35432,plain,
% 15.33/2.49      ( k4_xboole_0(sK4,k4_xboole_0(sK4,X0)) = k1_xboole_0
% 15.33/2.49      | k4_xboole_0(sK3,sK5) = k1_xboole_0 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_35158,c_17]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_3813,plain,
% 15.33/2.49      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_0,c_2722]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_9741,plain,
% 15.33/2.49      ( r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK3),k4_xboole_0(k2_zfmisc_1(X0,sK5),k4_xboole_0(k2_zfmisc_1(X0,sK5),k2_zfmisc_1(sK2,sK3)))),k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5)) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1360,c_3813]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_9788,plain,
% 15.33/2.49      ( r1_tarski(k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),sK5)),k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5)) = iProver_top ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_9741,c_1363,c_1795]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_9789,plain,
% 15.33/2.49      ( r1_tarski(k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,k4_xboole_0(sK4,X0))),sK5),k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5)) = iProver_top ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_9788,c_1360]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_45424,plain,
% 15.33/2.49      ( k4_xboole_0(sK3,sK5) = k1_xboole_0
% 15.33/2.49      | r1_tarski(k2_zfmisc_1(k4_xboole_0(sK4,k1_xboole_0),sK5),k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5)) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_35432,c_9789]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_45563,plain,
% 15.33/2.49      ( k4_xboole_0(sK3,sK5) = k1_xboole_0
% 15.33/2.49      | r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK4,X0),sK5)) = iProver_top ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_45424,c_12,c_26]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_24,negated_conjecture,
% 15.33/2.49      ( k1_xboole_0 != sK3 ),
% 15.33/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_778,plain,
% 15.33/2.49      ( k2_zfmisc_1(X0,sK3) != k1_xboole_0
% 15.33/2.49      | k1_xboole_0 = X0
% 15.33/2.49      | k1_xboole_0 = sK3 ),
% 15.33/2.49      inference(instantiation,[status(thm)],[c_17]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_924,plain,
% 15.33/2.49      ( k2_zfmisc_1(sK2,sK3) != k1_xboole_0
% 15.33/2.49      | k1_xboole_0 = sK2
% 15.33/2.49      | k1_xboole_0 = sK3 ),
% 15.33/2.49      inference(instantiation,[status(thm)],[c_778]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_4,plain,
% 15.33/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.33/2.49      inference(cnf_transformation,[],[f43]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1258,plain,
% 15.33/2.49      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k1_xboole_0)
% 15.33/2.49      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK3))
% 15.33/2.49      | k2_zfmisc_1(sK2,sK3) = k1_xboole_0 ),
% 15.33/2.49      inference(instantiation,[status(thm)],[c_4]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1259,plain,
% 15.33/2.49      ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0
% 15.33/2.49      | r1_tarski(k2_zfmisc_1(sK2,sK3),k1_xboole_0) != iProver_top
% 15.33/2.49      | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK3)) != iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_1258]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1156,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,X0)) = k2_zfmisc_1(sK4,k4_xboole_0(sK5,X0)) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_26,c_21]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_2728,plain,
% 15.33/2.49      ( r1_tarski(k2_zfmisc_1(sK4,k4_xboole_0(sK5,X0)),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1156,c_635]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_4146,plain,
% 15.33/2.49      ( r1_tarski(k2_zfmisc_1(sK4,k1_xboole_0),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_659,c_2728]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_4151,plain,
% 15.33/2.49      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_4146,c_15]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_3346,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK5))) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),sK5) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1550,c_1360]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_3348,plain,
% 15.33/2.49      ( k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),sK5) ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_3346,c_21]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_15841,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),X0)) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(sK5,X0)) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_3348,c_21]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1163,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,k4_xboole_0(X2,X1))) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_21,c_0]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1164,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,k4_xboole_0(X2,X1))) ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_1163,c_21]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_15843,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),X0),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(X0,sK5))) = k4_xboole_0(k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK5))),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(sK5,X0))) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_3348,c_1164]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_15959,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),X0),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(X0,sK5))) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(sK5,k4_xboole_0(sK5,X0))) ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_15841,c_15843]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_15962,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),X0),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(X0,sK5))) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))) ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_15959,c_20,c_21,c_26]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_16898,plain,
% 15.33/2.49      ( r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0))),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),X0)) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_15962,c_635]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_17340,plain,
% 15.33/2.49      ( r1_tarski(k2_zfmisc_1(sK2,k4_xboole_0(sK3,k1_xboole_0)),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),sK3)) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_659,c_16898]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_17360,plain,
% 15.33/2.49      ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),sK3)) = iProver_top ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_17340,c_12]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_45439,plain,
% 15.33/2.49      ( k4_xboole_0(sK3,sK5) = k1_xboole_0
% 15.33/2.49      | r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k1_xboole_0,sK3)) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_35432,c_17360]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_45517,plain,
% 15.33/2.49      ( k4_xboole_0(sK3,sK5) = k1_xboole_0
% 15.33/2.49      | r1_tarski(k2_zfmisc_1(sK2,sK3),k1_xboole_0) = iProver_top ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_45439,c_16]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_46864,plain,
% 15.33/2.49      ( k4_xboole_0(sK3,sK5) = k1_xboole_0 ),
% 15.33/2.49      inference(global_propositional_subsumption,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_45563,c_25,c_24,c_924,c_1259,c_4151,c_45517]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_47008,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),sK3),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k1_xboole_0)) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK3))) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_46864,c_15962]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_47029,plain,
% 15.33/2.49      ( k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),sK3) = k2_zfmisc_1(sK2,sK3) ),
% 15.33/2.49      inference(demodulation,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_47008,c_12,c_15,c_21,c_659]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_46903,plain,
% 15.33/2.49      ( k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK5) = k2_zfmisc_1(sK2,k1_xboole_0) ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_46864,c_1550]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_46905,plain,
% 15.33/2.49      ( k2_zfmisc_1(k4_xboole_0(sK4,sK2),sK5) = k1_xboole_0 ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_46903,c_15]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_47850,plain,
% 15.33/2.49      ( k4_xboole_0(sK4,sK2) = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_46905,c_17]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_794,plain,
% 15.33/2.49      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 15.33/2.49      inference(instantiation,[status(thm)],[c_305]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_795,plain,
% 15.33/2.49      ( sK3 != k1_xboole_0
% 15.33/2.49      | k1_xboole_0 = sK3
% 15.33/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.33/2.49      inference(instantiation,[status(thm)],[c_794]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_3270,plain,
% 15.33/2.49      ( k2_zfmisc_1(sK4,k4_xboole_0(sK3,sK5)) != k1_xboole_0
% 15.33/2.49      | k4_xboole_0(sK4,sK2) = k1_xboole_0
% 15.33/2.49      | sK3 = k1_xboole_0 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1525,c_17]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_35420,plain,
% 15.33/2.49      ( k2_zfmisc_1(k4_xboole_0(sK4,k1_xboole_0),k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_659,c_35158]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_35606,plain,
% 15.33/2.49      ( k2_zfmisc_1(sK4,k4_xboole_0(sK3,sK5)) = k1_xboole_0 ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_35420,c_12]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_48635,plain,
% 15.33/2.49      ( k4_xboole_0(sK4,sK2) = k1_xboole_0 ),
% 15.33/2.49      inference(global_propositional_subsumption,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_47850,c_24,c_34,c_35,c_795,c_3270,c_35606]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_54322,plain,
% 15.33/2.49      ( k2_zfmisc_1(k4_xboole_0(sK4,k1_xboole_0),sK3) = k2_zfmisc_1(sK2,sK3) ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_47029,c_48635]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_54323,plain,
% 15.33/2.49      ( k2_zfmisc_1(sK4,sK3) = k2_zfmisc_1(sK2,sK3) ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_54322,c_12]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_54387,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK3)) = k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_54323,c_1156]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_54393,plain,
% 15.33/2.49      ( k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) = k1_xboole_0 ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_54387,c_15,c_21,c_659]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_56180,plain,
% 15.33/2.49      ( k4_xboole_0(sK5,sK3) = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_54393,c_17]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_56408,plain,
% 15.33/2.49      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK5)) = k4_xboole_0(sK5,k1_xboole_0)
% 15.33/2.49      | sK4 = k1_xboole_0 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_56180,c_0]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_56596,plain,
% 15.33/2.49      ( k4_xboole_0(sK5,k1_xboole_0) = k4_xboole_0(sK3,k1_xboole_0)
% 15.33/2.49      | sK4 = k1_xboole_0 ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_56408,c_46864]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_56597,plain,
% 15.33/2.49      ( sK4 = k1_xboole_0 | sK5 = sK3 ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_56596,c_12]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_4796,plain,
% 15.33/2.49      ( k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,sK4)),sK5) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),sK5) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1795,c_22]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_25583,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(sK4,X0)),sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK4))),sK5) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_4796,c_1360]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_56802,plain,
% 15.33/2.49      ( k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),sK5)) = k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK4))),sK5)
% 15.33/2.49      | sK5 = sK3 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_56597,c_25583]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1033,plain,
% 15.33/2.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_12,c_0]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_3769,plain,
% 15.33/2.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_1033,c_659]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_57537,plain,
% 15.33/2.49      ( k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK4))),sK5) = k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(k1_xboole_0,sK5))
% 15.33/2.49      | sK5 = sK3 ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_56802,c_3769]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_57538,plain,
% 15.33/2.49      ( k2_zfmisc_1(k4_xboole_0(sK4,k4_xboole_0(X0,k4_xboole_0(X0,sK4))),sK5) = k2_zfmisc_1(sK2,sK3)
% 15.33/2.49      | sK5 = sK3 ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_57537,c_12,c_26,c_1360]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_56995,plain,
% 15.33/2.49      ( k2_zfmisc_1(k1_xboole_0,sK5) = k2_zfmisc_1(sK2,sK3) | sK5 = sK3 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_56597,c_26]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_56998,plain,
% 15.33/2.49      ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0 | sK5 = sK3 ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_56995,c_16]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_57680,plain,
% 15.33/2.49      ( sK5 = sK3 ),
% 15.33/2.49      inference(global_propositional_subsumption,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_57538,c_25,c_24,c_924,c_56998]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_23,negated_conjecture,
% 15.33/2.49      ( sK2 != sK4 | sK3 != sK5 ),
% 15.33/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_57805,plain,
% 15.33/2.49      ( sK4 != sK2 | sK3 != sK3 ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_57680,c_23]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_57807,plain,
% 15.33/2.49      ( sK4 != sK2 ),
% 15.33/2.49      inference(equality_resolution_simp,[status(thm)],[c_57805]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_10,plain,
% 15.33/2.49      ( X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
% 15.33/2.49      inference(cnf_transformation,[],[f47]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_48706,plain,
% 15.33/2.49      ( k4_xboole_0(sK2,sK4) != k1_xboole_0 | sK4 = sK2 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_48635,c_10]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1402,plain,
% 15.33/2.49      ( k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) = k2_zfmisc_1(k4_xboole_0(sK2,sK4),sK3) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1156,c_22]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_2419,plain,
% 15.33/2.49      ( k2_zfmisc_1(sK4,k4_xboole_0(sK5,sK3)) != k1_xboole_0
% 15.33/2.49      | k4_xboole_0(sK2,sK4) = k1_xboole_0
% 15.33/2.49      | sK3 = k1_xboole_0 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1402,c_17]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(contradiction,plain,
% 15.33/2.49      ( $false ),
% 15.33/2.49      inference(minisat,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_57807,c_54393,c_48706,c_2419,c_795,c_35,c_34,c_24]) ).
% 15.33/2.49  
% 15.33/2.49  
% 15.33/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.33/2.49  
% 15.33/2.49  ------                               Statistics
% 15.33/2.49  
% 15.33/2.49  ------ Selected
% 15.33/2.49  
% 15.33/2.49  total_time:                             1.888
% 15.33/2.49  
%------------------------------------------------------------------------------
