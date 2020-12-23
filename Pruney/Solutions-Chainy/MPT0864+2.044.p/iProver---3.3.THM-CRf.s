%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:54 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  133 (1363 expanded)
%              Number of clauses        :   71 ( 395 expanded)
%              Number of leaves         :   17 ( 370 expanded)
%              Depth                    :   26
%              Number of atoms          :  255 (3049 expanded)
%              Number of equality atoms :  188 (2694 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK0) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f28])).

fof(f42,plain,(
    v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f19,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f27,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(sK2,sK3) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( k2_mcart_1(sK1) = sK1
        | k1_mcart_1(sK1) = sK1 )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK1 ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( k2_mcart_1(sK1) = sK1
      | k1_mcart_1(sK1) = sK1 )
    & k4_tarski(sK2,sK3) = sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f40,f39])).

fof(f76,plain,(
    k4_tarski(sK2,sK3) = sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,
    ( k2_mcart_1(sK1) = sK1
    | k1_mcart_1(sK1) = sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f90,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X2)) ),
    inference(definition_unfolding,[],[f66,f45])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f88,plain,(
    ! [X0,X1] : r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f61,f45])).

fof(f7,axiom,(
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
    inference(nnf_transformation,[],[f7])).

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

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      | k3_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | k3_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X1),X2)) != k2_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f44])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f34])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X2,X2),X3)) ) ),
    inference(definition_unfolding,[],[f55,f45])).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f91,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f65,f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X2,X2),X3)) ) ),
    inference(definition_unfolding,[],[f56,f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      | ~ r2_hidden(X1,X3)
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X2,X2),X3))
      | ~ r2_hidden(X1,X3)
      | X0 != X2 ) ),
    inference(definition_unfolding,[],[f57,f45])).

fof(f99,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k2_tarski(X2,X2),X3))
      | ~ r2_hidden(X1,X3) ) ),
    inference(equality_resolution,[],[f82])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f36])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_tarski(X3,X3))) ) ),
    inference(definition_unfolding,[],[f59,f45])).

fof(f5,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_0,plain,
    ( v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1080,plain,
    ( v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_33,negated_conjecture,
    ( k4_tarski(sK2,sK3) = sK1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( k1_mcart_1(sK1) = sK1
    | k2_mcart_1(sK1) = sK1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_31,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1294,plain,
    ( k1_mcart_1(sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_33,c_31])).

cnf(c_1651,plain,
    ( k2_mcart_1(sK1) = sK1
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_32,c_1294])).

cnf(c_30,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1258,plain,
    ( k2_mcart_1(sK1) = sK3 ),
    inference(superposition,[status(thm)],[c_33,c_30])).

cnf(c_1653,plain,
    ( sK3 = sK1
    | sK2 = sK1 ),
    inference(demodulation,[status(thm)],[c_1651,c_1258])).

cnf(c_21,plain,
    ( k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1067,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4334,plain,
    ( k2_tarski(X0,X0) = k1_xboole_0
    | r1_tarski(k2_tarski(X0,X0),k2_tarski(k4_tarski(X1,X0),k4_tarski(X2,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1067])).

cnf(c_13999,plain,
    ( k2_tarski(sK3,sK3) = k1_xboole_0
    | r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK1,k4_tarski(X0,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_4334])).

cnf(c_14206,plain,
    ( k2_tarski(sK3,sK3) = k1_xboole_0
    | r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK1,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_13999])).

cnf(c_14225,plain,
    ( k2_tarski(sK3,sK3) = k1_xboole_0
    | sK2 = sK1
    | r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1653,c_14206])).

cnf(c_17,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1076,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14458,plain,
    ( k2_tarski(sK3,sK3) = k1_xboole_0
    | sK2 = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14225,c_1076])).

cnf(c_14473,plain,
    ( k2_tarski(k4_tarski(X0,sK3),k4_tarski(X1,sK3)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_xboole_0)
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_14458,c_21])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_14620,plain,
    ( k2_tarski(k4_tarski(X0,sK3),k4_tarski(X1,sK3)) = k1_xboole_0
    | sK2 = sK1 ),
    inference(demodulation,[status(thm)],[c_14473,c_8])).

cnf(c_15511,plain,
    ( k2_tarski(sK1,k4_tarski(X0,sK3)) = k1_xboole_0
    | sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_33,c_14620])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_23,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k2_tarski(X0,X2),k4_xboole_0(k2_tarski(X0,X2),X1)) != k2_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1065,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X1),X2)) != k2_tarski(X0,X1)
    | r2_hidden(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_11560,plain,
    ( k2_tarski(X0,X1) != k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1065])).

cnf(c_15756,plain,
    ( sK2 = sK1
    | r2_hidden(sK1,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_15511,c_11560])).

cnf(c_13,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X2,X2),X3))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1071,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_tarski(X0,X0),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3144,plain,
    ( sK2 = X0
    | r2_hidden(sK1,k2_zfmisc_1(k2_tarski(X0,X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1071])).

cnf(c_3688,plain,
    ( sK2 = X0
    | r2_hidden(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_3144])).

cnf(c_16389,plain,
    ( sK2 = sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_15756,c_3688])).

cnf(c_22,plain,
    ( k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3148,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X1,X2),k2_tarski(k4_tarski(X0,X3),k4_tarski(X0,X4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1071])).

cnf(c_9109,plain,
    ( sK2 = X0
    | r2_hidden(k4_tarski(X0,X1),k2_tarski(k4_tarski(sK2,X2),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_3148])).

cnf(c_16409,plain,
    ( sK1 = X0
    | r2_hidden(k4_tarski(X0,X1),k2_tarski(k4_tarski(sK1,X2),sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16389,c_9109])).

cnf(c_16428,plain,
    ( sK1 = X0
    | r2_hidden(sK1,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16389,c_3688])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1066,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4184,plain,
    ( k2_tarski(X0,X1) = k1_xboole_0
    | r1_tarski(k2_tarski(X0,X1),k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1066])).

cnf(c_12369,plain,
    ( k2_tarski(sK2,X0) = k1_xboole_0
    | r1_tarski(k2_tarski(sK2,X0),k2_tarski(sK1,k4_tarski(X0,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_4184])).

cnf(c_12408,plain,
    ( k2_tarski(sK2,sK2) = k1_xboole_0
    | r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK1,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_12369])).

cnf(c_16398,plain,
    ( k2_tarski(sK1,sK1) = k1_xboole_0
    | r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16389,c_12408])).

cnf(c_17108,plain,
    ( k2_tarski(sK1,sK1) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16398,c_1076])).

cnf(c_17144,plain,
    ( r2_hidden(sK1,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17108,c_11560])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(k2_tarski(X3,X3),X1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1072,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(k2_tarski(X3,X3),X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4143,plain,
    ( r2_hidden(sK3,X0) = iProver_top
    | r2_hidden(sK1,k2_zfmisc_1(k2_tarski(X1,X1),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1072])).

cnf(c_17166,plain,
    ( r2_hidden(sK3,X0) = iProver_top
    | r2_hidden(sK1,k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17108,c_4143])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_17181,plain,
    ( r2_hidden(sK3,X0) = iProver_top
    | r2_hidden(sK1,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17166,c_9])).

cnf(c_17227,plain,
    ( r2_hidden(sK3,X0) = iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_17144,c_17181])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(k2_tarski(X2,X2),X1)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1073,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(k2_tarski(X2,X2),X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5188,plain,
    ( r2_hidden(sK3,X0) != iProver_top
    | r2_hidden(sK1,k2_zfmisc_1(k2_tarski(sK2,sK2),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1073])).

cnf(c_15,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_tarski(X3,X3)))
    | X3 = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1069,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(X3,k2_tarski(X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7227,plain,
    ( sK3 = X0
    | r2_hidden(sK1,k2_zfmisc_1(X1,k2_tarski(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1069])).

cnf(c_7490,plain,
    ( sK3 = X0
    | r2_hidden(sK3,k2_tarski(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5188,c_7227])).

cnf(c_17158,plain,
    ( sK3 = sK1
    | r2_hidden(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17108,c_7490])).

cnf(c_17230,plain,
    ( sK3 = sK1 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_17227,c_17158])).

cnf(c_17232,plain,
    ( r2_hidden(sK1,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17230,c_17227])).

cnf(c_17250,plain,
    ( r2_hidden(sK1,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_17232])).

cnf(c_17466,plain,
    ( sK1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16409,c_16428,c_17250])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1079,plain,
    ( v1_xboole_0(k4_tarski(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2398,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1079])).

cnf(c_17805,plain,
    ( v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17466,c_2398])).

cnf(c_17822,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1080,c_17805])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:28:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.78/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.78/1.03  
% 0.78/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.78/1.03  
% 0.78/1.03  ------  iProver source info
% 0.78/1.03  
% 0.78/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.78/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.78/1.03  git: non_committed_changes: false
% 0.78/1.03  git: last_make_outside_of_git: false
% 0.78/1.03  
% 0.78/1.03  ------ 
% 0.78/1.03  
% 0.78/1.03  ------ Input Options
% 0.78/1.03  
% 0.78/1.03  --out_options                           all
% 0.78/1.03  --tptp_safe_out                         true
% 0.78/1.03  --problem_path                          ""
% 0.78/1.03  --include_path                          ""
% 0.78/1.03  --clausifier                            res/vclausify_rel
% 0.78/1.03  --clausifier_options                    --mode clausify
% 0.78/1.03  --stdin                                 false
% 0.78/1.03  --stats_out                             all
% 0.78/1.03  
% 0.78/1.03  ------ General Options
% 0.78/1.03  
% 0.78/1.03  --fof                                   false
% 0.78/1.03  --time_out_real                         305.
% 0.78/1.03  --time_out_virtual                      -1.
% 0.78/1.03  --symbol_type_check                     false
% 0.78/1.03  --clausify_out                          false
% 0.78/1.03  --sig_cnt_out                           false
% 0.78/1.03  --trig_cnt_out                          false
% 0.78/1.03  --trig_cnt_out_tolerance                1.
% 0.78/1.03  --trig_cnt_out_sk_spl                   false
% 0.78/1.03  --abstr_cl_out                          false
% 0.78/1.03  
% 0.78/1.03  ------ Global Options
% 0.78/1.03  
% 0.78/1.03  --schedule                              default
% 0.78/1.03  --add_important_lit                     false
% 0.78/1.03  --prop_solver_per_cl                    1000
% 0.78/1.03  --min_unsat_core                        false
% 0.78/1.03  --soft_assumptions                      false
% 0.78/1.03  --soft_lemma_size                       3
% 0.78/1.03  --prop_impl_unit_size                   0
% 0.78/1.03  --prop_impl_unit                        []
% 0.78/1.03  --share_sel_clauses                     true
% 0.78/1.03  --reset_solvers                         false
% 0.78/1.03  --bc_imp_inh                            [conj_cone]
% 0.78/1.03  --conj_cone_tolerance                   3.
% 0.78/1.03  --extra_neg_conj                        none
% 0.78/1.03  --large_theory_mode                     true
% 0.78/1.03  --prolific_symb_bound                   200
% 0.78/1.03  --lt_threshold                          2000
% 0.78/1.03  --clause_weak_htbl                      true
% 0.78/1.03  --gc_record_bc_elim                     false
% 0.78/1.03  
% 0.78/1.03  ------ Preprocessing Options
% 0.78/1.03  
% 0.78/1.03  --preprocessing_flag                    true
% 0.78/1.03  --time_out_prep_mult                    0.1
% 0.78/1.03  --splitting_mode                        input
% 0.78/1.03  --splitting_grd                         true
% 0.78/1.03  --splitting_cvd                         false
% 0.78/1.03  --splitting_cvd_svl                     false
% 0.78/1.03  --splitting_nvd                         32
% 0.78/1.03  --sub_typing                            true
% 0.78/1.03  --prep_gs_sim                           true
% 0.78/1.03  --prep_unflatten                        true
% 0.78/1.03  --prep_res_sim                          true
% 0.78/1.03  --prep_upred                            true
% 0.78/1.03  --prep_sem_filter                       exhaustive
% 0.78/1.03  --prep_sem_filter_out                   false
% 0.78/1.03  --pred_elim                             true
% 0.78/1.03  --res_sim_input                         true
% 0.78/1.03  --eq_ax_congr_red                       true
% 0.78/1.03  --pure_diseq_elim                       true
% 0.78/1.03  --brand_transform                       false
% 0.78/1.03  --non_eq_to_eq                          false
% 0.78/1.03  --prep_def_merge                        true
% 0.78/1.03  --prep_def_merge_prop_impl              false
% 0.78/1.03  --prep_def_merge_mbd                    true
% 0.78/1.03  --prep_def_merge_tr_red                 false
% 0.78/1.03  --prep_def_merge_tr_cl                  false
% 0.78/1.03  --smt_preprocessing                     true
% 0.78/1.03  --smt_ac_axioms                         fast
% 0.78/1.03  --preprocessed_out                      false
% 0.78/1.03  --preprocessed_stats                    false
% 0.78/1.03  
% 0.78/1.03  ------ Abstraction refinement Options
% 0.78/1.03  
% 0.78/1.03  --abstr_ref                             []
% 0.78/1.03  --abstr_ref_prep                        false
% 0.78/1.03  --abstr_ref_until_sat                   false
% 0.78/1.03  --abstr_ref_sig_restrict                funpre
% 0.78/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.78/1.03  --abstr_ref_under                       []
% 0.78/1.03  
% 0.78/1.03  ------ SAT Options
% 0.78/1.03  
% 0.78/1.03  --sat_mode                              false
% 0.78/1.03  --sat_fm_restart_options                ""
% 0.78/1.03  --sat_gr_def                            false
% 0.78/1.03  --sat_epr_types                         true
% 0.78/1.03  --sat_non_cyclic_types                  false
% 0.78/1.03  --sat_finite_models                     false
% 0.78/1.03  --sat_fm_lemmas                         false
% 0.78/1.03  --sat_fm_prep                           false
% 0.78/1.03  --sat_fm_uc_incr                        true
% 0.78/1.03  --sat_out_model                         small
% 0.78/1.03  --sat_out_clauses                       false
% 0.78/1.03  
% 0.78/1.03  ------ QBF Options
% 0.78/1.03  
% 0.78/1.03  --qbf_mode                              false
% 0.78/1.03  --qbf_elim_univ                         false
% 0.78/1.03  --qbf_dom_inst                          none
% 0.78/1.03  --qbf_dom_pre_inst                      false
% 0.78/1.03  --qbf_sk_in                             false
% 0.78/1.03  --qbf_pred_elim                         true
% 0.78/1.03  --qbf_split                             512
% 0.78/1.03  
% 0.78/1.03  ------ BMC1 Options
% 0.78/1.03  
% 0.78/1.03  --bmc1_incremental                      false
% 0.78/1.03  --bmc1_axioms                           reachable_all
% 0.78/1.03  --bmc1_min_bound                        0
% 0.78/1.03  --bmc1_max_bound                        -1
% 0.78/1.03  --bmc1_max_bound_default                -1
% 0.78/1.03  --bmc1_symbol_reachability              true
% 0.78/1.03  --bmc1_property_lemmas                  false
% 0.78/1.03  --bmc1_k_induction                      false
% 0.78/1.03  --bmc1_non_equiv_states                 false
% 0.78/1.03  --bmc1_deadlock                         false
% 0.78/1.03  --bmc1_ucm                              false
% 0.78/1.03  --bmc1_add_unsat_core                   none
% 0.78/1.03  --bmc1_unsat_core_children              false
% 0.78/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.78/1.03  --bmc1_out_stat                         full
% 0.78/1.03  --bmc1_ground_init                      false
% 0.78/1.03  --bmc1_pre_inst_next_state              false
% 0.78/1.03  --bmc1_pre_inst_state                   false
% 0.78/1.03  --bmc1_pre_inst_reach_state             false
% 0.78/1.03  --bmc1_out_unsat_core                   false
% 0.78/1.03  --bmc1_aig_witness_out                  false
% 0.78/1.03  --bmc1_verbose                          false
% 0.78/1.03  --bmc1_dump_clauses_tptp                false
% 0.78/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.78/1.03  --bmc1_dump_file                        -
% 0.78/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.78/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.78/1.03  --bmc1_ucm_extend_mode                  1
% 0.78/1.03  --bmc1_ucm_init_mode                    2
% 0.78/1.03  --bmc1_ucm_cone_mode                    none
% 0.78/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.78/1.03  --bmc1_ucm_relax_model                  4
% 0.78/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.78/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.78/1.03  --bmc1_ucm_layered_model                none
% 0.78/1.03  --bmc1_ucm_max_lemma_size               10
% 0.78/1.03  
% 0.78/1.03  ------ AIG Options
% 0.78/1.03  
% 0.78/1.03  --aig_mode                              false
% 0.78/1.03  
% 0.78/1.03  ------ Instantiation Options
% 0.78/1.03  
% 0.78/1.03  --instantiation_flag                    true
% 0.78/1.03  --inst_sos_flag                         false
% 0.78/1.03  --inst_sos_phase                        true
% 0.78/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.78/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.78/1.03  --inst_lit_sel_side                     num_symb
% 0.78/1.03  --inst_solver_per_active                1400
% 0.78/1.03  --inst_solver_calls_frac                1.
% 0.78/1.03  --inst_passive_queue_type               priority_queues
% 0.78/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.78/1.03  --inst_passive_queues_freq              [25;2]
% 0.78/1.03  --inst_dismatching                      true
% 0.78/1.03  --inst_eager_unprocessed_to_passive     true
% 0.78/1.03  --inst_prop_sim_given                   true
% 0.78/1.03  --inst_prop_sim_new                     false
% 0.78/1.03  --inst_subs_new                         false
% 0.78/1.03  --inst_eq_res_simp                      false
% 0.78/1.03  --inst_subs_given                       false
% 0.78/1.03  --inst_orphan_elimination               true
% 0.78/1.03  --inst_learning_loop_flag               true
% 0.78/1.03  --inst_learning_start                   3000
% 0.78/1.03  --inst_learning_factor                  2
% 0.78/1.03  --inst_start_prop_sim_after_learn       3
% 0.78/1.03  --inst_sel_renew                        solver
% 0.78/1.03  --inst_lit_activity_flag                true
% 0.78/1.03  --inst_restr_to_given                   false
% 0.78/1.03  --inst_activity_threshold               500
% 0.78/1.03  --inst_out_proof                        true
% 0.78/1.03  
% 0.78/1.03  ------ Resolution Options
% 0.78/1.03  
% 0.78/1.03  --resolution_flag                       true
% 0.78/1.03  --res_lit_sel                           adaptive
% 0.78/1.03  --res_lit_sel_side                      none
% 0.78/1.03  --res_ordering                          kbo
% 0.78/1.03  --res_to_prop_solver                    active
% 0.78/1.03  --res_prop_simpl_new                    false
% 0.78/1.03  --res_prop_simpl_given                  true
% 0.78/1.03  --res_passive_queue_type                priority_queues
% 0.78/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.78/1.03  --res_passive_queues_freq               [15;5]
% 0.78/1.03  --res_forward_subs                      full
% 0.78/1.03  --res_backward_subs                     full
% 0.78/1.03  --res_forward_subs_resolution           true
% 0.78/1.03  --res_backward_subs_resolution          true
% 0.78/1.03  --res_orphan_elimination                true
% 0.78/1.03  --res_time_limit                        2.
% 0.78/1.03  --res_out_proof                         true
% 0.78/1.03  
% 0.78/1.03  ------ Superposition Options
% 0.78/1.03  
% 0.78/1.03  --superposition_flag                    true
% 0.78/1.03  --sup_passive_queue_type                priority_queues
% 0.78/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.78/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.78/1.03  --demod_completeness_check              fast
% 0.78/1.03  --demod_use_ground                      true
% 0.78/1.03  --sup_to_prop_solver                    passive
% 0.78/1.03  --sup_prop_simpl_new                    true
% 0.78/1.03  --sup_prop_simpl_given                  true
% 0.78/1.03  --sup_fun_splitting                     false
% 0.78/1.03  --sup_smt_interval                      50000
% 0.78/1.03  
% 0.78/1.03  ------ Superposition Simplification Setup
% 0.78/1.03  
% 0.78/1.03  --sup_indices_passive                   []
% 0.78/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.78/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.78/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.78/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.78/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.78/1.03  --sup_full_bw                           [BwDemod]
% 0.78/1.03  --sup_immed_triv                        [TrivRules]
% 0.78/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.78/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.78/1.03  --sup_immed_bw_main                     []
% 0.78/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.78/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.78/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.78/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.78/1.03  
% 0.78/1.03  ------ Combination Options
% 0.78/1.03  
% 0.78/1.03  --comb_res_mult                         3
% 0.78/1.03  --comb_sup_mult                         2
% 0.78/1.03  --comb_inst_mult                        10
% 0.78/1.03  
% 0.78/1.03  ------ Debug Options
% 0.78/1.03  
% 0.78/1.03  --dbg_backtrace                         false
% 0.78/1.03  --dbg_dump_prop_clauses                 false
% 0.78/1.03  --dbg_dump_prop_clauses_file            -
% 0.78/1.03  --dbg_out_stat                          false
% 0.78/1.03  ------ Parsing...
% 0.78/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.78/1.03  
% 0.78/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.78/1.03  
% 0.78/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.78/1.03  
% 0.78/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.78/1.03  ------ Proving...
% 0.78/1.03  ------ Problem Properties 
% 0.78/1.03  
% 0.78/1.03  
% 0.78/1.03  clauses                                 33
% 0.78/1.03  conjectures                             2
% 0.78/1.03  EPR                                     5
% 0.78/1.03  Horn                                    28
% 0.78/1.03  unary                                   16
% 0.78/1.03  binary                                  10
% 0.78/1.03  lits                                    59
% 0.78/1.03  lits eq                                 23
% 0.78/1.03  fd_pure                                 0
% 0.78/1.03  fd_pseudo                               0
% 0.78/1.03  fd_cond                                 3
% 0.78/1.03  fd_pseudo_cond                          3
% 0.78/1.03  AC symbols                              0
% 0.78/1.03  
% 0.78/1.03  ------ Schedule dynamic 5 is on 
% 0.78/1.03  
% 0.78/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.78/1.03  
% 0.78/1.03  
% 0.78/1.03  ------ 
% 0.78/1.03  Current options:
% 0.78/1.03  ------ 
% 0.78/1.03  
% 0.78/1.03  ------ Input Options
% 0.78/1.03  
% 0.78/1.03  --out_options                           all
% 0.78/1.03  --tptp_safe_out                         true
% 0.78/1.03  --problem_path                          ""
% 0.78/1.03  --include_path                          ""
% 0.78/1.03  --clausifier                            res/vclausify_rel
% 0.78/1.03  --clausifier_options                    --mode clausify
% 0.78/1.03  --stdin                                 false
% 0.78/1.03  --stats_out                             all
% 0.78/1.03  
% 0.78/1.03  ------ General Options
% 0.78/1.03  
% 0.78/1.03  --fof                                   false
% 0.78/1.03  --time_out_real                         305.
% 0.78/1.03  --time_out_virtual                      -1.
% 0.78/1.03  --symbol_type_check                     false
% 0.78/1.03  --clausify_out                          false
% 0.78/1.03  --sig_cnt_out                           false
% 0.78/1.03  --trig_cnt_out                          false
% 0.78/1.03  --trig_cnt_out_tolerance                1.
% 0.78/1.03  --trig_cnt_out_sk_spl                   false
% 0.78/1.03  --abstr_cl_out                          false
% 0.78/1.03  
% 0.78/1.03  ------ Global Options
% 0.78/1.03  
% 0.78/1.03  --schedule                              default
% 0.78/1.03  --add_important_lit                     false
% 0.78/1.03  --prop_solver_per_cl                    1000
% 0.78/1.03  --min_unsat_core                        false
% 0.78/1.03  --soft_assumptions                      false
% 0.78/1.03  --soft_lemma_size                       3
% 0.78/1.03  --prop_impl_unit_size                   0
% 0.78/1.03  --prop_impl_unit                        []
% 0.78/1.03  --share_sel_clauses                     true
% 0.78/1.03  --reset_solvers                         false
% 0.78/1.03  --bc_imp_inh                            [conj_cone]
% 0.78/1.03  --conj_cone_tolerance                   3.
% 0.78/1.03  --extra_neg_conj                        none
% 0.78/1.03  --large_theory_mode                     true
% 0.78/1.03  --prolific_symb_bound                   200
% 0.78/1.03  --lt_threshold                          2000
% 0.78/1.03  --clause_weak_htbl                      true
% 0.78/1.03  --gc_record_bc_elim                     false
% 0.78/1.03  
% 0.78/1.03  ------ Preprocessing Options
% 0.78/1.03  
% 0.78/1.03  --preprocessing_flag                    true
% 0.78/1.03  --time_out_prep_mult                    0.1
% 0.78/1.03  --splitting_mode                        input
% 0.78/1.03  --splitting_grd                         true
% 0.78/1.03  --splitting_cvd                         false
% 0.78/1.03  --splitting_cvd_svl                     false
% 0.78/1.03  --splitting_nvd                         32
% 0.78/1.03  --sub_typing                            true
% 0.78/1.03  --prep_gs_sim                           true
% 0.78/1.03  --prep_unflatten                        true
% 0.78/1.03  --prep_res_sim                          true
% 0.78/1.03  --prep_upred                            true
% 0.78/1.03  --prep_sem_filter                       exhaustive
% 0.78/1.03  --prep_sem_filter_out                   false
% 0.78/1.03  --pred_elim                             true
% 0.78/1.03  --res_sim_input                         true
% 0.78/1.03  --eq_ax_congr_red                       true
% 0.78/1.03  --pure_diseq_elim                       true
% 0.78/1.03  --brand_transform                       false
% 0.78/1.03  --non_eq_to_eq                          false
% 0.78/1.03  --prep_def_merge                        true
% 0.78/1.03  --prep_def_merge_prop_impl              false
% 0.78/1.03  --prep_def_merge_mbd                    true
% 0.78/1.03  --prep_def_merge_tr_red                 false
% 0.78/1.03  --prep_def_merge_tr_cl                  false
% 0.78/1.03  --smt_preprocessing                     true
% 0.78/1.03  --smt_ac_axioms                         fast
% 0.78/1.03  --preprocessed_out                      false
% 0.78/1.03  --preprocessed_stats                    false
% 0.78/1.03  
% 0.78/1.03  ------ Abstraction refinement Options
% 0.78/1.03  
% 0.78/1.03  --abstr_ref                             []
% 0.78/1.03  --abstr_ref_prep                        false
% 0.78/1.03  --abstr_ref_until_sat                   false
% 0.78/1.03  --abstr_ref_sig_restrict                funpre
% 0.78/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.78/1.03  --abstr_ref_under                       []
% 0.78/1.03  
% 0.78/1.03  ------ SAT Options
% 0.78/1.03  
% 0.78/1.03  --sat_mode                              false
% 0.78/1.03  --sat_fm_restart_options                ""
% 0.78/1.03  --sat_gr_def                            false
% 0.78/1.03  --sat_epr_types                         true
% 0.78/1.03  --sat_non_cyclic_types                  false
% 0.78/1.03  --sat_finite_models                     false
% 0.78/1.03  --sat_fm_lemmas                         false
% 0.78/1.03  --sat_fm_prep                           false
% 0.78/1.03  --sat_fm_uc_incr                        true
% 0.78/1.03  --sat_out_model                         small
% 0.78/1.03  --sat_out_clauses                       false
% 0.78/1.03  
% 0.78/1.03  ------ QBF Options
% 0.78/1.03  
% 0.78/1.03  --qbf_mode                              false
% 0.78/1.03  --qbf_elim_univ                         false
% 0.78/1.03  --qbf_dom_inst                          none
% 0.78/1.03  --qbf_dom_pre_inst                      false
% 0.78/1.03  --qbf_sk_in                             false
% 0.78/1.03  --qbf_pred_elim                         true
% 0.78/1.03  --qbf_split                             512
% 0.78/1.03  
% 0.78/1.03  ------ BMC1 Options
% 0.78/1.03  
% 0.78/1.03  --bmc1_incremental                      false
% 0.78/1.03  --bmc1_axioms                           reachable_all
% 0.78/1.03  --bmc1_min_bound                        0
% 0.78/1.03  --bmc1_max_bound                        -1
% 0.78/1.03  --bmc1_max_bound_default                -1
% 0.78/1.03  --bmc1_symbol_reachability              true
% 0.78/1.03  --bmc1_property_lemmas                  false
% 0.78/1.03  --bmc1_k_induction                      false
% 0.78/1.03  --bmc1_non_equiv_states                 false
% 0.78/1.03  --bmc1_deadlock                         false
% 0.78/1.03  --bmc1_ucm                              false
% 0.78/1.03  --bmc1_add_unsat_core                   none
% 0.78/1.03  --bmc1_unsat_core_children              false
% 0.78/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.78/1.03  --bmc1_out_stat                         full
% 0.78/1.03  --bmc1_ground_init                      false
% 0.78/1.03  --bmc1_pre_inst_next_state              false
% 0.78/1.03  --bmc1_pre_inst_state                   false
% 0.78/1.03  --bmc1_pre_inst_reach_state             false
% 0.78/1.03  --bmc1_out_unsat_core                   false
% 0.78/1.03  --bmc1_aig_witness_out                  false
% 0.78/1.03  --bmc1_verbose                          false
% 0.78/1.03  --bmc1_dump_clauses_tptp                false
% 0.78/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.78/1.03  --bmc1_dump_file                        -
% 0.78/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.78/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.78/1.03  --bmc1_ucm_extend_mode                  1
% 0.78/1.03  --bmc1_ucm_init_mode                    2
% 0.78/1.03  --bmc1_ucm_cone_mode                    none
% 0.78/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.78/1.03  --bmc1_ucm_relax_model                  4
% 0.78/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.78/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.78/1.03  --bmc1_ucm_layered_model                none
% 0.78/1.03  --bmc1_ucm_max_lemma_size               10
% 0.78/1.03  
% 0.78/1.03  ------ AIG Options
% 0.78/1.03  
% 0.78/1.03  --aig_mode                              false
% 0.78/1.03  
% 0.78/1.03  ------ Instantiation Options
% 0.78/1.03  
% 0.78/1.03  --instantiation_flag                    true
% 0.78/1.03  --inst_sos_flag                         false
% 0.78/1.03  --inst_sos_phase                        true
% 0.78/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.78/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.78/1.03  --inst_lit_sel_side                     none
% 0.78/1.03  --inst_solver_per_active                1400
% 0.78/1.03  --inst_solver_calls_frac                1.
% 0.78/1.03  --inst_passive_queue_type               priority_queues
% 0.78/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.78/1.03  --inst_passive_queues_freq              [25;2]
% 0.78/1.03  --inst_dismatching                      true
% 0.78/1.03  --inst_eager_unprocessed_to_passive     true
% 0.78/1.03  --inst_prop_sim_given                   true
% 0.78/1.03  --inst_prop_sim_new                     false
% 0.78/1.03  --inst_subs_new                         false
% 0.78/1.03  --inst_eq_res_simp                      false
% 0.78/1.03  --inst_subs_given                       false
% 0.78/1.03  --inst_orphan_elimination               true
% 0.78/1.03  --inst_learning_loop_flag               true
% 0.78/1.03  --inst_learning_start                   3000
% 0.78/1.03  --inst_learning_factor                  2
% 0.78/1.03  --inst_start_prop_sim_after_learn       3
% 0.78/1.03  --inst_sel_renew                        solver
% 0.78/1.03  --inst_lit_activity_flag                true
% 0.78/1.03  --inst_restr_to_given                   false
% 0.78/1.03  --inst_activity_threshold               500
% 0.78/1.03  --inst_out_proof                        true
% 0.78/1.03  
% 0.78/1.03  ------ Resolution Options
% 0.78/1.03  
% 0.78/1.03  --resolution_flag                       false
% 0.78/1.03  --res_lit_sel                           adaptive
% 0.78/1.03  --res_lit_sel_side                      none
% 0.78/1.03  --res_ordering                          kbo
% 0.78/1.03  --res_to_prop_solver                    active
% 0.78/1.03  --res_prop_simpl_new                    false
% 0.78/1.03  --res_prop_simpl_given                  true
% 0.78/1.03  --res_passive_queue_type                priority_queues
% 0.78/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.78/1.03  --res_passive_queues_freq               [15;5]
% 0.78/1.03  --res_forward_subs                      full
% 0.78/1.03  --res_backward_subs                     full
% 0.78/1.03  --res_forward_subs_resolution           true
% 0.78/1.03  --res_backward_subs_resolution          true
% 0.78/1.03  --res_orphan_elimination                true
% 0.78/1.03  --res_time_limit                        2.
% 0.78/1.03  --res_out_proof                         true
% 0.78/1.03  
% 0.78/1.03  ------ Superposition Options
% 0.78/1.03  
% 0.78/1.03  --superposition_flag                    true
% 0.78/1.03  --sup_passive_queue_type                priority_queues
% 0.78/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.78/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.78/1.03  --demod_completeness_check              fast
% 0.78/1.03  --demod_use_ground                      true
% 0.78/1.03  --sup_to_prop_solver                    passive
% 0.78/1.03  --sup_prop_simpl_new                    true
% 0.78/1.03  --sup_prop_simpl_given                  true
% 0.78/1.03  --sup_fun_splitting                     false
% 0.78/1.03  --sup_smt_interval                      50000
% 0.78/1.03  
% 0.78/1.03  ------ Superposition Simplification Setup
% 0.78/1.03  
% 0.78/1.03  --sup_indices_passive                   []
% 0.78/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.78/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.78/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.78/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.78/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.78/1.03  --sup_full_bw                           [BwDemod]
% 0.78/1.03  --sup_immed_triv                        [TrivRules]
% 0.78/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.78/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.78/1.03  --sup_immed_bw_main                     []
% 0.78/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.78/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.78/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.78/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.78/1.03  
% 0.78/1.03  ------ Combination Options
% 0.78/1.03  
% 0.78/1.03  --comb_res_mult                         3
% 0.78/1.03  --comb_sup_mult                         2
% 0.78/1.03  --comb_inst_mult                        10
% 0.78/1.03  
% 0.78/1.03  ------ Debug Options
% 0.78/1.03  
% 0.78/1.03  --dbg_backtrace                         false
% 0.78/1.03  --dbg_dump_prop_clauses                 false
% 0.78/1.03  --dbg_dump_prop_clauses_file            -
% 0.78/1.03  --dbg_out_stat                          false
% 0.78/1.03  
% 0.78/1.03  
% 0.78/1.03  
% 0.78/1.03  
% 0.78/1.03  ------ Proving...
% 0.78/1.03  
% 0.78/1.03  
% 0.78/1.03  % SZS status Theorem for theBenchmark.p
% 0.78/1.03  
% 0.78/1.03   Resolution empty clause
% 0.78/1.03  
% 0.78/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.78/1.03  
% 0.78/1.03  fof(f1,axiom,(
% 0.78/1.03    ? [X0] : v1_xboole_0(X0)),
% 0.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.78/1.03  
% 0.78/1.03  fof(f28,plain,(
% 0.78/1.03    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK0)),
% 0.78/1.03    introduced(choice_axiom,[])).
% 0.78/1.03  
% 0.78/1.03  fof(f29,plain,(
% 0.78/1.03    v1_xboole_0(sK0)),
% 0.78/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f28])).
% 0.78/1.03  
% 0.78/1.03  fof(f42,plain,(
% 0.78/1.03    v1_xboole_0(sK0)),
% 0.78/1.03    inference(cnf_transformation,[],[f29])).
% 0.78/1.03  
% 0.78/1.03  fof(f19,conjecture,(
% 0.78/1.03    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.78/1.03  
% 0.78/1.03  fof(f20,negated_conjecture,(
% 0.78/1.03    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.78/1.03    inference(negated_conjecture,[],[f19])).
% 0.78/1.03  
% 0.78/1.03  fof(f27,plain,(
% 0.78/1.03    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.78/1.03    inference(ennf_transformation,[],[f20])).
% 0.78/1.03  
% 0.78/1.03  fof(f40,plain,(
% 0.78/1.03    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK2,sK3) = X0) )),
% 0.78/1.03    introduced(choice_axiom,[])).
% 0.78/1.03  
% 0.78/1.03  fof(f39,plain,(
% 0.78/1.03    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK1) = sK1 | k1_mcart_1(sK1) = sK1) & ? [X2,X1] : k4_tarski(X1,X2) = sK1)),
% 0.78/1.03    introduced(choice_axiom,[])).
% 0.78/1.03  
% 0.78/1.03  fof(f41,plain,(
% 0.78/1.03    (k2_mcart_1(sK1) = sK1 | k1_mcart_1(sK1) = sK1) & k4_tarski(sK2,sK3) = sK1),
% 0.78/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f40,f39])).
% 0.78/1.03  
% 0.78/1.03  fof(f76,plain,(
% 0.78/1.03    k4_tarski(sK2,sK3) = sK1),
% 0.78/1.03    inference(cnf_transformation,[],[f41])).
% 0.78/1.03  
% 0.78/1.03  fof(f77,plain,(
% 0.78/1.03    k2_mcart_1(sK1) = sK1 | k1_mcart_1(sK1) = sK1),
% 0.78/1.03    inference(cnf_transformation,[],[f41])).
% 0.78/1.03  
% 0.78/1.03  fof(f18,axiom,(
% 0.78/1.03    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.78/1.03  
% 0.78/1.03  fof(f74,plain,(
% 0.78/1.03    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.78/1.03    inference(cnf_transformation,[],[f18])).
% 0.78/1.03  
% 0.78/1.03  fof(f75,plain,(
% 0.78/1.03    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.78/1.03    inference(cnf_transformation,[],[f18])).
% 0.78/1.03  
% 0.78/1.03  fof(f13,axiom,(
% 0.78/1.03    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.78/1.03  
% 0.78/1.03  fof(f66,plain,(
% 0.78/1.03    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.78/1.03    inference(cnf_transformation,[],[f13])).
% 0.78/1.03  
% 0.78/1.03  fof(f4,axiom,(
% 0.78/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.78/1.03  
% 0.78/1.03  fof(f45,plain,(
% 0.78/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.78/1.03    inference(cnf_transformation,[],[f4])).
% 0.78/1.03  
% 0.78/1.03  fof(f90,plain,(
% 0.78/1.03    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X2))) )),
% 0.78/1.03    inference(definition_unfolding,[],[f66,f45])).
% 0.78/1.03  
% 0.78/1.03  fof(f11,axiom,(
% 0.78/1.03    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 0.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.78/1.03  
% 0.78/1.03  fof(f22,plain,(
% 0.78/1.03    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 0.78/1.03    inference(ennf_transformation,[],[f11])).
% 0.78/1.03  
% 0.78/1.03  fof(f63,plain,(
% 0.78/1.03    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X1,X0))) )),
% 0.78/1.03    inference(cnf_transformation,[],[f22])).
% 0.78/1.03  
% 0.78/1.03  fof(f10,axiom,(
% 0.78/1.03    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.78/1.03  
% 0.78/1.03  fof(f61,plain,(
% 0.78/1.03    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.78/1.03    inference(cnf_transformation,[],[f10])).
% 0.78/1.03  
% 0.78/1.03  fof(f88,plain,(
% 0.78/1.03    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 0.78/1.03    inference(definition_unfolding,[],[f61,f45])).
% 0.78/1.03  
% 0.78/1.03  fof(f7,axiom,(
% 0.78/1.03    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.78/1.03  
% 0.78/1.03  fof(f32,plain,(
% 0.78/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.78/1.03    inference(nnf_transformation,[],[f7])).
% 0.78/1.03  
% 0.78/1.03  fof(f33,plain,(
% 0.78/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.78/1.03    inference(flattening,[],[f32])).
% 0.78/1.03  
% 0.78/1.03  fof(f54,plain,(
% 0.78/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.78/1.03    inference(cnf_transformation,[],[f33])).
% 0.78/1.03  
% 0.78/1.03  fof(f97,plain,(
% 0.78/1.03    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.78/1.03    inference(equality_resolution,[],[f54])).
% 0.78/1.03  
% 0.78/1.03  fof(f2,axiom,(
% 0.78/1.03    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.78/1.03  
% 0.78/1.03  fof(f43,plain,(
% 0.78/1.03    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.78/1.03    inference(cnf_transformation,[],[f2])).
% 0.78/1.03  
% 0.78/1.03  fof(f3,axiom,(
% 0.78/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.78/1.03  
% 0.78/1.03  fof(f44,plain,(
% 0.78/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.78/1.03    inference(cnf_transformation,[],[f3])).
% 0.78/1.03  
% 0.78/1.03  fof(f78,plain,(
% 0.78/1.03    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.78/1.03    inference(definition_unfolding,[],[f43,f44])).
% 0.78/1.03  
% 0.78/1.03  fof(f14,axiom,(
% 0.78/1.03    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) => r2_hidden(X0,X2))),
% 0.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.78/1.03  
% 0.78/1.03  fof(f23,plain,(
% 0.78/1.03    ! [X0,X1,X2] : (r2_hidden(X0,X2) | k3_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1))),
% 0.78/1.03    inference(ennf_transformation,[],[f14])).
% 0.78/1.03  
% 0.78/1.03  fof(f67,plain,(
% 0.78/1.03    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | k3_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)) )),
% 0.78/1.03    inference(cnf_transformation,[],[f23])).
% 0.78/1.03  
% 0.78/1.03  fof(f92,plain,(
% 0.78/1.03    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X1),X2)) != k2_tarski(X0,X1)) )),
% 0.78/1.03    inference(definition_unfolding,[],[f67,f44])).
% 0.78/1.03  
% 0.78/1.03  fof(f8,axiom,(
% 0.78/1.03    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.78/1.03  
% 0.78/1.03  fof(f34,plain,(
% 0.78/1.03    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 0.78/1.03    inference(nnf_transformation,[],[f8])).
% 0.78/1.03  
% 0.78/1.03  fof(f35,plain,(
% 0.78/1.03    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 0.78/1.03    inference(flattening,[],[f34])).
% 0.78/1.03  
% 0.78/1.03  fof(f55,plain,(
% 0.78/1.03    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 0.78/1.03    inference(cnf_transformation,[],[f35])).
% 0.78/1.03  
% 0.78/1.03  fof(f84,plain,(
% 0.78/1.03    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X2,X2),X3))) )),
% 0.78/1.03    inference(definition_unfolding,[],[f55,f45])).
% 0.78/1.03  
% 0.78/1.03  fof(f65,plain,(
% 0.78/1.03    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.78/1.03    inference(cnf_transformation,[],[f13])).
% 0.78/1.03  
% 0.78/1.03  fof(f91,plain,(
% 0.78/1.03    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2))) )),
% 0.78/1.03    inference(definition_unfolding,[],[f65,f45])).
% 0.78/1.03  
% 0.78/1.03  fof(f62,plain,(
% 0.78/1.03    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k2_zfmisc_1(X0,X1))) )),
% 0.78/1.03    inference(cnf_transformation,[],[f22])).
% 0.78/1.03  
% 0.78/1.03  fof(f56,plain,(
% 0.78/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 0.78/1.03    inference(cnf_transformation,[],[f35])).
% 0.78/1.03  
% 0.78/1.03  fof(f83,plain,(
% 0.78/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X2,X2),X3))) )),
% 0.78/1.03    inference(definition_unfolding,[],[f56,f45])).
% 0.78/1.03  
% 0.78/1.03  fof(f53,plain,(
% 0.78/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.78/1.03    inference(cnf_transformation,[],[f33])).
% 0.78/1.03  
% 0.78/1.03  fof(f98,plain,(
% 0.78/1.03    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.78/1.03    inference(equality_resolution,[],[f53])).
% 0.78/1.03  
% 0.78/1.03  fof(f57,plain,(
% 0.78/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) )),
% 0.78/1.03    inference(cnf_transformation,[],[f35])).
% 0.78/1.03  
% 0.78/1.03  fof(f82,plain,(
% 0.78/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X2,X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) )),
% 0.78/1.03    inference(definition_unfolding,[],[f57,f45])).
% 0.78/1.03  
% 0.78/1.03  fof(f99,plain,(
% 0.78/1.03    ( ! [X2,X3,X1] : (r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(k2_tarski(X2,X2),X3)) | ~r2_hidden(X1,X3)) )),
% 0.78/1.03    inference(equality_resolution,[],[f82])).
% 0.78/1.03  
% 0.78/1.03  fof(f9,axiom,(
% 0.78/1.03    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.78/1.03  
% 0.78/1.03  fof(f36,plain,(
% 0.78/1.03    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.78/1.03    inference(nnf_transformation,[],[f9])).
% 0.78/1.03  
% 0.78/1.03  fof(f37,plain,(
% 0.78/1.03    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.78/1.03    inference(flattening,[],[f36])).
% 0.78/1.03  
% 0.78/1.03  fof(f59,plain,(
% 0.78/1.03    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 0.78/1.03    inference(cnf_transformation,[],[f37])).
% 0.78/1.03  
% 0.78/1.03  fof(f86,plain,(
% 0.78/1.03    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_tarski(X3,X3)))) )),
% 0.78/1.03    inference(definition_unfolding,[],[f59,f45])).
% 0.78/1.03  
% 0.78/1.03  fof(f5,axiom,(
% 0.78/1.03    ! [X0,X1] : ~v1_xboole_0(k4_tarski(X0,X1))),
% 0.78/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.78/1.03  
% 0.78/1.03  fof(f46,plain,(
% 0.78/1.03    ( ! [X0,X1] : (~v1_xboole_0(k4_tarski(X0,X1))) )),
% 0.78/1.03    inference(cnf_transformation,[],[f5])).
% 0.78/1.03  
% 0.78/1.03  cnf(c_0,plain,( v1_xboole_0(sK0) ),inference(cnf_transformation,[],[f42]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_1080,plain,
% 0.78/1.03      ( v1_xboole_0(sK0) = iProver_top ),
% 0.78/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_33,negated_conjecture,
% 0.78/1.03      ( k4_tarski(sK2,sK3) = sK1 ),
% 0.78/1.03      inference(cnf_transformation,[],[f76]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_32,negated_conjecture,
% 0.78/1.03      ( k1_mcart_1(sK1) = sK1 | k2_mcart_1(sK1) = sK1 ),
% 0.78/1.03      inference(cnf_transformation,[],[f77]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_31,plain,
% 0.78/1.03      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 0.78/1.03      inference(cnf_transformation,[],[f74]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_1294,plain,
% 0.78/1.03      ( k1_mcart_1(sK1) = sK2 ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_33,c_31]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_1651,plain,
% 0.78/1.03      ( k2_mcart_1(sK1) = sK1 | sK2 = sK1 ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_32,c_1294]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_30,plain,
% 0.78/1.03      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 0.78/1.03      inference(cnf_transformation,[],[f75]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_1258,plain,
% 0.78/1.03      ( k2_mcart_1(sK1) = sK3 ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_33,c_30]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_1653,plain,
% 0.78/1.03      ( sK3 = sK1 | sK2 = sK1 ),
% 0.78/1.03      inference(demodulation,[status(thm)],[c_1651,c_1258]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_21,plain,
% 0.78/1.03      ( k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
% 0.78/1.03      inference(cnf_transformation,[],[f90]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_18,plain,
% 0.78/1.03      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0 ),
% 0.78/1.03      inference(cnf_transformation,[],[f63]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_1067,plain,
% 0.78/1.03      ( k1_xboole_0 = X0 | r1_tarski(X0,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 0.78/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_4334,plain,
% 0.78/1.03      ( k2_tarski(X0,X0) = k1_xboole_0
% 0.78/1.03      | r1_tarski(k2_tarski(X0,X0),k2_tarski(k4_tarski(X1,X0),k4_tarski(X2,X0))) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_21,c_1067]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_13999,plain,
% 0.78/1.03      ( k2_tarski(sK3,sK3) = k1_xboole_0
% 0.78/1.03      | r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK1,k4_tarski(X0,sK3))) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_33,c_4334]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_14206,plain,
% 0.78/1.03      ( k2_tarski(sK3,sK3) = k1_xboole_0
% 0.78/1.03      | r1_tarski(k2_tarski(sK3,sK3),k2_tarski(sK1,sK1)) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_33,c_13999]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_14225,plain,
% 0.78/1.03      ( k2_tarski(sK3,sK3) = k1_xboole_0
% 0.78/1.03      | sK2 = sK1
% 0.78/1.03      | r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_1653,c_14206]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_17,plain,
% 0.78/1.03      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
% 0.78/1.03      inference(cnf_transformation,[],[f88]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_1076,plain,
% 0.78/1.03      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) = iProver_top ),
% 0.78/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_14458,plain,
% 0.78/1.03      ( k2_tarski(sK3,sK3) = k1_xboole_0 | sK2 = sK1 ),
% 0.78/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_14225,c_1076]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_14473,plain,
% 0.78/1.03      ( k2_tarski(k4_tarski(X0,sK3),k4_tarski(X1,sK3)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_xboole_0)
% 0.78/1.03      | sK2 = sK1 ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_14458,c_21]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_8,plain,
% 0.78/1.03      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 0.78/1.03      inference(cnf_transformation,[],[f97]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_14620,plain,
% 0.78/1.03      ( k2_tarski(k4_tarski(X0,sK3),k4_tarski(X1,sK3)) = k1_xboole_0
% 0.78/1.03      | sK2 = sK1 ),
% 0.78/1.03      inference(demodulation,[status(thm)],[c_14473,c_8]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_15511,plain,
% 0.78/1.03      ( k2_tarski(sK1,k4_tarski(X0,sK3)) = k1_xboole_0 | sK2 = sK1 ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_33,c_14620]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_1,plain,
% 0.78/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 0.78/1.03      inference(cnf_transformation,[],[f78]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_23,plain,
% 0.78/1.03      ( r2_hidden(X0,X1)
% 0.78/1.03      | k4_xboole_0(k2_tarski(X0,X2),k4_xboole_0(k2_tarski(X0,X2),X1)) != k2_tarski(X0,X2) ),
% 0.78/1.03      inference(cnf_transformation,[],[f92]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_1065,plain,
% 0.78/1.03      ( k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X1),X2)) != k2_tarski(X0,X1)
% 0.78/1.03      | r2_hidden(X0,X2) = iProver_top ),
% 0.78/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_11560,plain,
% 0.78/1.03      ( k2_tarski(X0,X1) != k1_xboole_0
% 0.78/1.03      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_1,c_1065]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_15756,plain,
% 0.78/1.03      ( sK2 = sK1 | r2_hidden(sK1,k1_xboole_0) = iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_15511,c_11560]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_13,plain,
% 0.78/1.03      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_tarski(X2,X2),X3))
% 0.78/1.03      | X2 = X0 ),
% 0.78/1.03      inference(cnf_transformation,[],[f84]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_1071,plain,
% 0.78/1.03      ( X0 = X1
% 0.78/1.03      | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k2_tarski(X0,X0),X3)) != iProver_top ),
% 0.78/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_3144,plain,
% 0.78/1.03      ( sK2 = X0
% 0.78/1.03      | r2_hidden(sK1,k2_zfmisc_1(k2_tarski(X0,X0),X1)) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_33,c_1071]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_3688,plain,
% 0.78/1.03      ( sK2 = X0 | r2_hidden(sK1,k1_xboole_0) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_8,c_3144]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_16389,plain,
% 0.78/1.03      ( sK2 = sK1 ),
% 0.78/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_15756,c_3688]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_22,plain,
% 0.78/1.03      ( k2_zfmisc_1(k2_tarski(X0,X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
% 0.78/1.03      inference(cnf_transformation,[],[f91]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_3148,plain,
% 0.78/1.03      ( X0 = X1
% 0.78/1.03      | r2_hidden(k4_tarski(X1,X2),k2_tarski(k4_tarski(X0,X3),k4_tarski(X0,X4))) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_22,c_1071]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_9109,plain,
% 0.78/1.03      ( sK2 = X0
% 0.78/1.03      | r2_hidden(k4_tarski(X0,X1),k2_tarski(k4_tarski(sK2,X2),sK1)) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_33,c_3148]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_16409,plain,
% 0.78/1.03      ( sK1 = X0
% 0.78/1.03      | r2_hidden(k4_tarski(X0,X1),k2_tarski(k4_tarski(sK1,X2),sK1)) != iProver_top ),
% 0.78/1.03      inference(demodulation,[status(thm)],[c_16389,c_9109]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_16428,plain,
% 0.78/1.03      ( sK1 = X0 | r2_hidden(sK1,k1_xboole_0) != iProver_top ),
% 0.78/1.03      inference(demodulation,[status(thm)],[c_16389,c_3688]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_19,plain,
% 0.78/1.03      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0 ),
% 0.78/1.03      inference(cnf_transformation,[],[f62]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_1066,plain,
% 0.78/1.03      ( k1_xboole_0 = X0 | r1_tarski(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 0.78/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_4184,plain,
% 0.78/1.03      ( k2_tarski(X0,X1) = k1_xboole_0
% 0.78/1.03      | r1_tarski(k2_tarski(X0,X1),k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_21,c_1066]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_12369,plain,
% 0.78/1.03      ( k2_tarski(sK2,X0) = k1_xboole_0
% 0.78/1.03      | r1_tarski(k2_tarski(sK2,X0),k2_tarski(sK1,k4_tarski(X0,sK3))) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_33,c_4184]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_12408,plain,
% 0.78/1.03      ( k2_tarski(sK2,sK2) = k1_xboole_0
% 0.78/1.03      | r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK1,sK1)) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_33,c_12369]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_16398,plain,
% 0.78/1.03      ( k2_tarski(sK1,sK1) = k1_xboole_0
% 0.78/1.03      | r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)) != iProver_top ),
% 0.78/1.03      inference(demodulation,[status(thm)],[c_16389,c_12408]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_17108,plain,
% 0.78/1.03      ( k2_tarski(sK1,sK1) = k1_xboole_0 ),
% 0.78/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_16398,c_1076]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_17144,plain,
% 0.78/1.03      ( r2_hidden(sK1,k1_xboole_0) = iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_17108,c_11560]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_12,plain,
% 0.78/1.03      ( r2_hidden(X0,X1)
% 0.78/1.03      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(k2_tarski(X3,X3),X1)) ),
% 0.78/1.03      inference(cnf_transformation,[],[f83]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_1072,plain,
% 0.78/1.03      ( r2_hidden(X0,X1) = iProver_top
% 0.78/1.03      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(k2_tarski(X3,X3),X1)) != iProver_top ),
% 0.78/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_4143,plain,
% 0.78/1.03      ( r2_hidden(sK3,X0) = iProver_top
% 0.78/1.03      | r2_hidden(sK1,k2_zfmisc_1(k2_tarski(X1,X1),X0)) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_33,c_1072]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_17166,plain,
% 0.78/1.03      ( r2_hidden(sK3,X0) = iProver_top
% 0.78/1.03      | r2_hidden(sK1,k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_17108,c_4143]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_9,plain,
% 0.78/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.78/1.03      inference(cnf_transformation,[],[f98]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_17181,plain,
% 0.78/1.03      ( r2_hidden(sK3,X0) = iProver_top
% 0.78/1.03      | r2_hidden(sK1,k1_xboole_0) != iProver_top ),
% 0.78/1.03      inference(light_normalisation,[status(thm)],[c_17166,c_9]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_17227,plain,
% 0.78/1.03      ( r2_hidden(sK3,X0) = iProver_top ),
% 0.78/1.03      inference(backward_subsumption_resolution,
% 0.78/1.03                [status(thm)],
% 0.78/1.03                [c_17144,c_17181]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_11,plain,
% 0.78/1.03      ( ~ r2_hidden(X0,X1)
% 0.78/1.03      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(k2_tarski(X2,X2),X1)) ),
% 0.78/1.03      inference(cnf_transformation,[],[f99]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_1073,plain,
% 0.78/1.03      ( r2_hidden(X0,X1) != iProver_top
% 0.78/1.03      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(k2_tarski(X2,X2),X1)) = iProver_top ),
% 0.78/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_5188,plain,
% 0.78/1.03      ( r2_hidden(sK3,X0) != iProver_top
% 0.78/1.03      | r2_hidden(sK1,k2_zfmisc_1(k2_tarski(sK2,sK2),X0)) = iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_33,c_1073]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_15,plain,
% 0.78/1.03      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_tarski(X3,X3)))
% 0.78/1.03      | X3 = X1 ),
% 0.78/1.03      inference(cnf_transformation,[],[f86]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_1069,plain,
% 0.78/1.03      ( X0 = X1
% 0.78/1.03      | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(X3,k2_tarski(X0,X0))) != iProver_top ),
% 0.78/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_7227,plain,
% 0.78/1.03      ( sK3 = X0
% 0.78/1.03      | r2_hidden(sK1,k2_zfmisc_1(X1,k2_tarski(X0,X0))) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_33,c_1069]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_7490,plain,
% 0.78/1.03      ( sK3 = X0 | r2_hidden(sK3,k2_tarski(X0,X0)) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_5188,c_7227]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_17158,plain,
% 0.78/1.03      ( sK3 = sK1 | r2_hidden(sK3,k1_xboole_0) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_17108,c_7490]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_17230,plain,
% 0.78/1.03      ( sK3 = sK1 ),
% 0.78/1.03      inference(backward_subsumption_resolution,
% 0.78/1.03                [status(thm)],
% 0.78/1.03                [c_17227,c_17158]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_17232,plain,
% 0.78/1.03      ( r2_hidden(sK1,X0) = iProver_top ),
% 0.78/1.03      inference(demodulation,[status(thm)],[c_17230,c_17227]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_17250,plain,
% 0.78/1.03      ( r2_hidden(sK1,k1_xboole_0) = iProver_top ),
% 0.78/1.03      inference(instantiation,[status(thm)],[c_17232]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_17466,plain,
% 0.78/1.03      ( sK1 = X0 ),
% 0.78/1.03      inference(global_propositional_subsumption,
% 0.78/1.03                [status(thm)],
% 0.78/1.03                [c_16409,c_16428,c_17250]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_2,plain,
% 0.78/1.03      ( ~ v1_xboole_0(k4_tarski(X0,X1)) ),
% 0.78/1.03      inference(cnf_transformation,[],[f46]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_1079,plain,
% 0.78/1.03      ( v1_xboole_0(k4_tarski(X0,X1)) != iProver_top ),
% 0.78/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_2398,plain,
% 0.78/1.03      ( v1_xboole_0(sK1) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_33,c_1079]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_17805,plain,
% 0.78/1.03      ( v1_xboole_0(X0) != iProver_top ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_17466,c_2398]) ).
% 0.78/1.03  
% 0.78/1.03  cnf(c_17822,plain,
% 0.78/1.03      ( $false ),
% 0.78/1.03      inference(superposition,[status(thm)],[c_1080,c_17805]) ).
% 0.78/1.03  
% 0.78/1.03  
% 0.78/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.78/1.03  
% 0.78/1.03  ------                               Statistics
% 0.78/1.03  
% 0.78/1.03  ------ General
% 0.78/1.03  
% 0.78/1.03  abstr_ref_over_cycles:                  0
% 0.78/1.03  abstr_ref_under_cycles:                 0
% 0.78/1.03  gc_basic_clause_elim:                   0
% 0.78/1.03  forced_gc_time:                         0
% 0.78/1.03  parsing_time:                           0.008
% 0.78/1.03  unif_index_cands_time:                  0.
% 0.78/1.03  unif_index_add_time:                    0.
% 0.78/1.03  orderings_time:                         0.
% 0.78/1.03  out_proof_time:                         0.009
% 0.78/1.03  total_time:                             0.432
% 0.78/1.03  num_of_symbols:                         47
% 0.78/1.03  num_of_terms:                           23578
% 0.78/1.03  
% 0.78/1.03  ------ Preprocessing
% 0.78/1.03  
% 0.78/1.03  num_of_splits:                          0
% 0.78/1.03  num_of_split_atoms:                     0
% 0.78/1.03  num_of_reused_defs:                     0
% 0.78/1.03  num_eq_ax_congr_red:                    3
% 0.78/1.03  num_of_sem_filtered_clauses:            1
% 0.78/1.03  num_of_subtypes:                        0
% 0.78/1.03  monotx_restored_types:                  0
% 0.78/1.03  sat_num_of_epr_types:                   0
% 0.78/1.03  sat_num_of_non_cyclic_types:            0
% 0.78/1.03  sat_guarded_non_collapsed_types:        0
% 0.78/1.03  num_pure_diseq_elim:                    0
% 0.78/1.03  simp_replaced_by:                       0
% 0.78/1.03  res_preprocessed:                       157
% 0.78/1.03  prep_upred:                             0
% 0.78/1.03  prep_unflattend:                        24
% 0.78/1.03  smt_new_axioms:                         0
% 0.78/1.03  pred_elim_cands:                        4
% 0.78/1.03  pred_elim:                              0
% 0.78/1.03  pred_elim_cl:                           0
% 0.78/1.03  pred_elim_cycles:                       2
% 0.78/1.03  merged_defs:                            0
% 0.78/1.03  merged_defs_ncl:                        0
% 0.78/1.03  bin_hyper_res:                          0
% 0.78/1.03  prep_cycles:                            4
% 0.78/1.03  pred_elim_time:                         0.002
% 0.78/1.03  splitting_time:                         0.
% 0.78/1.03  sem_filter_time:                        0.
% 0.78/1.03  monotx_time:                            0.
% 0.78/1.03  subtype_inf_time:                       0.
% 0.78/1.03  
% 0.78/1.03  ------ Problem properties
% 0.78/1.03  
% 0.78/1.03  clauses:                                33
% 0.78/1.03  conjectures:                            2
% 0.78/1.03  epr:                                    5
% 0.78/1.03  horn:                                   28
% 0.78/1.03  ground:                                 3
% 0.78/1.03  unary:                                  16
% 0.78/1.03  binary:                                 10
% 0.78/1.03  lits:                                   59
% 0.78/1.03  lits_eq:                                23
% 0.78/1.03  fd_pure:                                0
% 0.78/1.03  fd_pseudo:                              0
% 0.78/1.03  fd_cond:                                3
% 0.78/1.03  fd_pseudo_cond:                         3
% 0.78/1.03  ac_symbols:                             0
% 0.78/1.03  
% 0.78/1.03  ------ Propositional Solver
% 0.78/1.03  
% 0.78/1.03  prop_solver_calls:                      30
% 0.78/1.03  prop_fast_solver_calls:                 1090
% 0.78/1.03  smt_solver_calls:                       0
% 0.78/1.03  smt_fast_solver_calls:                  0
% 0.78/1.03  prop_num_of_clauses:                    7347
% 0.78/1.03  prop_preprocess_simplified:             16872
% 0.78/1.03  prop_fo_subsumed:                       9
% 0.78/1.03  prop_solver_time:                       0.
% 0.78/1.03  smt_solver_time:                        0.
% 0.78/1.03  smt_fast_solver_time:                   0.
% 0.78/1.03  prop_fast_solver_time:                  0.
% 0.78/1.03  prop_unsat_core_time:                   0.
% 0.78/1.03  
% 0.78/1.03  ------ QBF
% 0.78/1.03  
% 0.78/1.03  qbf_q_res:                              0
% 0.78/1.03  qbf_num_tautologies:                    0
% 0.78/1.03  qbf_prep_cycles:                        0
% 0.78/1.03  
% 0.78/1.03  ------ BMC1
% 0.78/1.03  
% 0.78/1.03  bmc1_current_bound:                     -1
% 0.78/1.03  bmc1_last_solved_bound:                 -1
% 0.78/1.03  bmc1_unsat_core_size:                   -1
% 0.78/1.03  bmc1_unsat_core_parents_size:           -1
% 0.78/1.03  bmc1_merge_next_fun:                    0
% 0.78/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.78/1.03  
% 0.78/1.03  ------ Instantiation
% 0.78/1.03  
% 0.78/1.03  inst_num_of_clauses:                    2275
% 0.78/1.03  inst_num_in_passive:                    930
% 0.78/1.03  inst_num_in_active:                     857
% 0.78/1.03  inst_num_in_unprocessed:                488
% 0.78/1.03  inst_num_of_loops:                      900
% 0.78/1.03  inst_num_of_learning_restarts:          0
% 0.78/1.03  inst_num_moves_active_passive:          41
% 0.78/1.03  inst_lit_activity:                      0
% 0.78/1.03  inst_lit_activity_moves:                0
% 0.78/1.03  inst_num_tautologies:                   0
% 0.78/1.03  inst_num_prop_implied:                  0
% 0.78/1.03  inst_num_existing_simplified:           0
% 0.78/1.03  inst_num_eq_res_simplified:             0
% 0.78/1.03  inst_num_child_elim:                    0
% 0.78/1.03  inst_num_of_dismatching_blockings:      715
% 0.78/1.03  inst_num_of_non_proper_insts:           1876
% 0.78/1.03  inst_num_of_duplicates:                 0
% 0.78/1.03  inst_inst_num_from_inst_to_res:         0
% 0.78/1.03  inst_dismatching_checking_time:         0.
% 0.78/1.03  
% 0.78/1.03  ------ Resolution
% 0.78/1.03  
% 0.78/1.03  res_num_of_clauses:                     0
% 0.78/1.03  res_num_in_passive:                     0
% 0.78/1.03  res_num_in_active:                      0
% 0.78/1.03  res_num_of_loops:                       161
% 0.78/1.03  res_forward_subset_subsumed:            143
% 0.78/1.03  res_backward_subset_subsumed:           0
% 0.78/1.03  res_forward_subsumed:                   0
% 0.78/1.03  res_backward_subsumed:                  0
% 0.78/1.03  res_forward_subsumption_resolution:     0
% 0.78/1.03  res_backward_subsumption_resolution:    0
% 0.78/1.03  res_clause_to_clause_subsumption:       1132
% 0.78/1.03  res_orphan_elimination:                 0
% 0.78/1.03  res_tautology_del:                      126
% 0.78/1.03  res_num_eq_res_simplified:              0
% 0.78/1.03  res_num_sel_changes:                    0
% 0.78/1.03  res_moves_from_active_to_pass:          0
% 0.78/1.03  
% 0.78/1.03  ------ Superposition
% 0.78/1.03  
% 0.78/1.03  sup_time_total:                         0.
% 0.78/1.03  sup_time_generating:                    0.
% 0.78/1.03  sup_time_sim_full:                      0.
% 0.78/1.03  sup_time_sim_immed:                     0.
% 0.78/1.03  
% 0.78/1.03  sup_num_of_clauses:                     128
% 0.78/1.03  sup_num_in_active:                      14
% 0.78/1.03  sup_num_in_passive:                     114
% 0.78/1.03  sup_num_of_loops:                       179
% 0.78/1.03  sup_fw_superposition:                   424
% 0.78/1.03  sup_bw_superposition:                   409
% 0.78/1.03  sup_immediate_simplified:               279
% 0.78/1.03  sup_given_eliminated:                   1
% 0.78/1.03  comparisons_done:                       0
% 0.78/1.03  comparisons_avoided:                    15
% 0.78/1.03  
% 0.78/1.03  ------ Simplifications
% 0.78/1.03  
% 0.78/1.03  
% 0.78/1.03  sim_fw_subset_subsumed:                 73
% 0.78/1.03  sim_bw_subset_subsumed:                 161
% 0.78/1.03  sim_fw_subsumed:                        87
% 0.78/1.03  sim_bw_subsumed:                        29
% 0.78/1.03  sim_fw_subsumption_res:                 6
% 0.78/1.03  sim_bw_subsumption_res:                 10
% 0.78/1.03  sim_tautology_del:                      39
% 0.78/1.03  sim_eq_tautology_del:                   49
% 0.78/1.03  sim_eq_res_simp:                        0
% 0.78/1.03  sim_fw_demodulated:                     50
% 0.78/1.03  sim_bw_demodulated:                     159
% 0.78/1.03  sim_light_normalised:                   11
% 0.78/1.03  sim_joinable_taut:                      0
% 0.78/1.03  sim_joinable_simp:                      0
% 0.78/1.03  sim_ac_normalised:                      0
% 0.78/1.03  sim_smt_subsumption:                    0
% 0.78/1.03  
%------------------------------------------------------------------------------
