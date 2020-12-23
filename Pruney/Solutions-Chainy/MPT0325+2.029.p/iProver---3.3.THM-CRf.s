%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:50 EST 2020

% Result     : Theorem 11.30s
% Output     : CNFRefutation 11.30s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 277 expanded)
%              Number of clauses        :   62 ( 125 expanded)
%              Number of leaves         :   11 (  53 expanded)
%              Depth                    :   19
%              Number of atoms          :  215 ( 722 expanded)
%              Number of equality atoms :  154 ( 428 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f15])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f22])).

fof(f39,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_7308,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_7309,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8625,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_7308,c_7309])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7300,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_7307,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8074,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7300,c_7307])).

cnf(c_14,plain,
    ( k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X1),X2),k2_zfmisc_1(X0,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_7,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7305,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7932,plain,
    ( r1_tarski(k2_zfmisc_1(k4_xboole_0(X0,X1),X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_7305])).

cnf(c_11022,plain,
    ( r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8074,c_7932])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_7311,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_11409,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11022,c_7311])).

cnf(c_11806,plain,
    ( k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11409,c_7308])).

cnf(c_11820,plain,
    ( k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0)) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_11806,c_14])).

cnf(c_13515,plain,
    ( k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11820,c_8074])).

cnf(c_30572,plain,
    ( k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8625,c_13515])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_31257,plain,
    ( k4_xboole_0(sK1,sK3) = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_30572,c_11])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_25,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_26,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_246,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4926,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_5063,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_4926])).

cnf(c_5064,plain,
    ( X0 != sK0
    | sK0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5063])).

cnf(c_5065,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_5064])).

cnf(c_250,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_5010,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1)
    | sK0 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_250])).

cnf(c_5337,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,X0)
    | sK0 != sK0
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_5010])).

cnf(c_5338,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,X0)
    | sK1 != X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5337])).

cnf(c_5339,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5338])).

cnf(c_4878,plain,
    ( k2_zfmisc_1(sK0,sK1) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_4950,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X0,X1)
    | k1_xboole_0 != k2_zfmisc_1(X0,X1)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_4878])).

cnf(c_5390,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,X0)
    | k1_xboole_0 != k2_zfmisc_1(sK0,X0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_4950])).

cnf(c_5391,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5390])).

cnf(c_11812,plain,
    ( k4_xboole_0(sK0,sK2) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11806,c_11])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_7306,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12292,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_11812,c_7306])).

cnf(c_12326,plain,
    ( r1_tarski(sK0,sK2)
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12292])).

cnf(c_23095,plain,
    ( k2_zfmisc_1(sK0,X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k2_zfmisc_1(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_23096,plain,
    ( k2_zfmisc_1(sK0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23095])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23628,plain,
    ( k2_zfmisc_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_25628,plain,
    ( r1_tarski(sK1,sK3)
    | k4_xboole_0(sK1,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_25651,plain,
    ( k4_xboole_0(sK1,sK3) != X0
    | k4_xboole_0(sK1,sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_26318,plain,
    ( k4_xboole_0(sK1,sK3) != k4_xboole_0(sK1,sK3)
    | k4_xboole_0(sK1,sK3) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_25651])).

cnf(c_26319,plain,
    ( k4_xboole_0(sK1,sK3) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK1,sK3) ),
    inference(equality_resolution_simp,[status(thm)],[c_26318])).

cnf(c_19628,plain,
    ( k2_zfmisc_1(sK0,X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_28365,plain,
    ( k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_19628])).

cnf(c_32335,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_31257,c_16,c_15,c_25,c_26,c_5065,c_5339,c_5391,c_12326,c_23096,c_23628,c_25628,c_26319,c_28365,c_30572])).

cnf(c_32428,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_32335,c_16])).

cnf(c_32430,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_32428,c_10])).

cnf(c_32431,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_32430])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.30/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.30/1.99  
% 11.30/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.30/1.99  
% 11.30/1.99  ------  iProver source info
% 11.30/1.99  
% 11.30/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.30/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.30/1.99  git: non_committed_changes: false
% 11.30/1.99  git: last_make_outside_of_git: false
% 11.30/1.99  
% 11.30/1.99  ------ 
% 11.30/1.99  ------ Parsing...
% 11.30/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  ------ Proving...
% 11.30/1.99  ------ Problem Properties 
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  clauses                                 17
% 11.30/1.99  conjectures                             3
% 11.30/1.99  EPR                                     4
% 11.30/1.99  Horn                                    14
% 11.30/1.99  unary                                   8
% 11.30/1.99  binary                                  5
% 11.30/1.99  lits                                    30
% 11.30/1.99  lits eq                                 13
% 11.30/1.99  fd_pure                                 0
% 11.30/1.99  fd_pseudo                               0
% 11.30/1.99  fd_cond                                 3
% 11.30/1.99  fd_pseudo_cond                          1
% 11.30/1.99  AC symbols                              0
% 11.30/1.99  
% 11.30/1.99  ------ Input Options Time Limit: Unbounded
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing...
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 11.30/1.99  Current options:
% 11.30/1.99  ------ 
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.30/1.99  
% 11.30/1.99  ------ Proving...
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  % SZS status Theorem for theBenchmark.p
% 11.30/1.99  
% 11.30/1.99   Resolution empty clause
% 11.30/1.99  
% 11.30/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.30/1.99  
% 11.30/1.99  fof(f3,axiom,(
% 11.30/1.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.30/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.30/1.99  
% 11.30/1.99  fof(f28,plain,(
% 11.30/1.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.30/1.99    inference(cnf_transformation,[],[f3])).
% 11.30/1.99  
% 11.30/1.99  fof(f2,axiom,(
% 11.30/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.30/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.30/1.99  
% 11.30/1.99  fof(f12,plain,(
% 11.30/1.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.30/1.99    inference(ennf_transformation,[],[f2])).
% 11.30/1.99  
% 11.30/1.99  fof(f27,plain,(
% 11.30/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.30/1.99    inference(cnf_transformation,[],[f12])).
% 11.30/1.99  
% 11.30/1.99  fof(f10,conjecture,(
% 11.30/1.99    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 11.30/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.30/1.99  
% 11.30/1.99  fof(f11,negated_conjecture,(
% 11.30/1.99    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 11.30/1.99    inference(negated_conjecture,[],[f10])).
% 11.30/1.99  
% 11.30/1.99  fof(f15,plain,(
% 11.30/1.99    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 11.30/1.99    inference(ennf_transformation,[],[f11])).
% 11.30/1.99  
% 11.30/1.99  fof(f16,plain,(
% 11.30/1.99    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 11.30/1.99    inference(flattening,[],[f15])).
% 11.30/1.99  
% 11.30/1.99  fof(f22,plain,(
% 11.30/1.99    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 11.30/1.99    introduced(choice_axiom,[])).
% 11.30/1.99  
% 11.30/1.99  fof(f23,plain,(
% 11.30/1.99    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 11.30/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f22])).
% 11.30/1.99  
% 11.30/1.99  fof(f39,plain,(
% 11.30/1.99    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 11.30/1.99    inference(cnf_transformation,[],[f23])).
% 11.30/1.99  
% 11.30/1.99  fof(f4,axiom,(
% 11.30/1.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 11.30/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.30/1.99  
% 11.30/1.99  fof(f19,plain,(
% 11.30/1.99    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 11.30/1.99    inference(nnf_transformation,[],[f4])).
% 11.30/1.99  
% 11.30/1.99  fof(f30,plain,(
% 11.30/1.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 11.30/1.99    inference(cnf_transformation,[],[f19])).
% 11.30/1.99  
% 11.30/1.99  fof(f9,axiom,(
% 11.30/1.99    ! [X0,X1,X2,X3] : k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))),
% 11.30/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.30/1.99  
% 11.30/1.99  fof(f38,plain,(
% 11.30/1.99    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 11.30/1.99    inference(cnf_transformation,[],[f9])).
% 11.30/1.99  
% 11.30/1.99  fof(f5,axiom,(
% 11.30/1.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.30/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.30/1.99  
% 11.30/1.99  fof(f31,plain,(
% 11.30/1.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.30/1.99    inference(cnf_transformation,[],[f5])).
% 11.30/1.99  
% 11.30/1.99  fof(f1,axiom,(
% 11.30/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.30/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.30/1.99  
% 11.30/1.99  fof(f17,plain,(
% 11.30/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.30/1.99    inference(nnf_transformation,[],[f1])).
% 11.30/1.99  
% 11.30/1.99  fof(f18,plain,(
% 11.30/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.30/1.99    inference(flattening,[],[f17])).
% 11.30/1.99  
% 11.30/1.99  fof(f26,plain,(
% 11.30/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.30/1.99    inference(cnf_transformation,[],[f18])).
% 11.30/1.99  
% 11.30/1.99  fof(f7,axiom,(
% 11.30/1.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.30/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.30/1.99  
% 11.30/1.99  fof(f20,plain,(
% 11.30/1.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.30/1.99    inference(nnf_transformation,[],[f7])).
% 11.30/1.99  
% 11.30/1.99  fof(f21,plain,(
% 11.30/1.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.30/1.99    inference(flattening,[],[f20])).
% 11.30/1.99  
% 11.30/1.99  fof(f33,plain,(
% 11.30/1.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 11.30/1.99    inference(cnf_transformation,[],[f21])).
% 11.30/1.99  
% 11.30/1.99  fof(f40,plain,(
% 11.30/1.99    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 11.30/1.99    inference(cnf_transformation,[],[f23])).
% 11.30/1.99  
% 11.30/1.99  fof(f41,plain,(
% 11.30/1.99    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 11.30/1.99    inference(cnf_transformation,[],[f23])).
% 11.30/1.99  
% 11.30/1.99  fof(f34,plain,(
% 11.30/1.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 11.30/1.99    inference(cnf_transformation,[],[f21])).
% 11.30/1.99  
% 11.30/1.99  fof(f45,plain,(
% 11.30/1.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 11.30/1.99    inference(equality_resolution,[],[f34])).
% 11.30/1.99  
% 11.30/1.99  fof(f29,plain,(
% 11.30/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 11.30/1.99    inference(cnf_transformation,[],[f19])).
% 11.30/1.99  
% 11.30/1.99  fof(f35,plain,(
% 11.30/1.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 11.30/1.99    inference(cnf_transformation,[],[f21])).
% 11.30/1.99  
% 11.30/1.99  fof(f44,plain,(
% 11.30/1.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 11.30/1.99    inference(equality_resolution,[],[f35])).
% 11.30/1.99  
% 11.30/1.99  cnf(c_4,plain,
% 11.30/1.99      ( r1_tarski(k1_xboole_0,X0) ),
% 11.30/1.99      inference(cnf_transformation,[],[f28]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_7308,plain,
% 11.30/1.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.30/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_3,plain,
% 11.30/1.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.30/1.99      inference(cnf_transformation,[],[f27]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_7309,plain,
% 11.30/1.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.30/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_8625,plain,
% 11.30/1.99      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.30/1.99      inference(superposition,[status(thm)],[c_7308,c_7309]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_17,negated_conjecture,
% 11.30/1.99      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
% 11.30/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_7300,plain,
% 11.30/1.99      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 11.30/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_5,plain,
% 11.30/1.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.30/1.99      inference(cnf_transformation,[],[f30]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_7307,plain,
% 11.30/1.99      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 11.30/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_8074,plain,
% 11.30/1.99      ( k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = k1_xboole_0 ),
% 11.30/1.99      inference(superposition,[status(thm)],[c_7300,c_7307]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_14,plain,
% 11.30/1.99      ( k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X1),X2),k2_zfmisc_1(X0,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 11.30/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_7,plain,
% 11.30/1.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 11.30/1.99      inference(cnf_transformation,[],[f31]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_7305,plain,
% 11.30/1.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 11.30/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_7932,plain,
% 11.30/1.99      ( r1_tarski(k2_zfmisc_1(k4_xboole_0(X0,X1),X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = iProver_top ),
% 11.30/1.99      inference(superposition,[status(thm)],[c_14,c_7305]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_11022,plain,
% 11.30/1.99      ( r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k1_xboole_0) = iProver_top ),
% 11.30/1.99      inference(superposition,[status(thm)],[c_8074,c_7932]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_0,plain,
% 11.30/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.30/1.99      inference(cnf_transformation,[],[f26]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_7311,plain,
% 11.30/1.99      ( X0 = X1
% 11.30/1.99      | r1_tarski(X0,X1) != iProver_top
% 11.30/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.30/1.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_11409,plain,
% 11.30/1.99      ( k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) = k1_xboole_0
% 11.30/1.99      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)) != iProver_top ),
% 11.30/1.99      inference(superposition,[status(thm)],[c_11022,c_7311]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_11806,plain,
% 11.30/1.99      ( k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) = k1_xboole_0 ),
% 11.30/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_11409,c_7308]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_11820,plain,
% 11.30/1.99      ( k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0)) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,X0))) ),
% 11.30/1.99      inference(superposition,[status(thm)],[c_11806,c_14]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_13515,plain,
% 11.30/1.99      ( k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))) = k1_xboole_0 ),
% 11.30/1.99      inference(superposition,[status(thm)],[c_11820,c_8074]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_30572,plain,
% 11.30/1.99      ( k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 11.30/1.99      inference(superposition,[status(thm)],[c_8625,c_13515]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_11,plain,
% 11.30/1.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 11.30/1.99      | k1_xboole_0 = X1
% 11.30/1.99      | k1_xboole_0 = X0 ),
% 11.30/1.99      inference(cnf_transformation,[],[f33]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_31257,plain,
% 11.30/1.99      ( k4_xboole_0(sK1,sK3) = k1_xboole_0 | sK0 = k1_xboole_0 ),
% 11.30/1.99      inference(superposition,[status(thm)],[c_30572,c_11]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_16,negated_conjecture,
% 11.30/1.99      ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
% 11.30/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_15,negated_conjecture,
% 11.30/1.99      ( ~ r1_tarski(sK0,sK2) | ~ r1_tarski(sK1,sK3) ),
% 11.30/1.99      inference(cnf_transformation,[],[f41]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_25,plain,
% 11.30/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.30/1.99      | k1_xboole_0 = k1_xboole_0 ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_10,plain,
% 11.30/1.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.30/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_26,plain,
% 11.30/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_246,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_4926,plain,
% 11.30/1.99      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_246]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_5063,plain,
% 11.30/1.99      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_4926]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_5064,plain,
% 11.30/1.99      ( X0 != sK0 | sK0 = X0 ),
% 11.30/1.99      inference(equality_resolution_simp,[status(thm)],[c_5063]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_5065,plain,
% 11.30/1.99      ( sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_5064]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_250,plain,
% 11.30/1.99      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 11.30/1.99      theory(equality) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_5010,plain,
% 11.30/1.99      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1) | sK0 != X0 | sK1 != X1 ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_250]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_5337,plain,
% 11.30/1.99      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,X0) | sK0 != sK0 | sK1 != X0 ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_5010]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_5338,plain,
% 11.30/1.99      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,X0) | sK1 != X0 ),
% 11.30/1.99      inference(equality_resolution_simp,[status(thm)],[c_5337]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_5339,plain,
% 11.30/1.99      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k1_xboole_0)
% 11.30/1.99      | sK1 != k1_xboole_0 ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_5338]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_4878,plain,
% 11.30/1.99      ( k2_zfmisc_1(sK0,sK1) != X0
% 11.30/1.99      | k1_xboole_0 != X0
% 11.30/1.99      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_246]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_4950,plain,
% 11.30/1.99      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X0,X1)
% 11.30/1.99      | k1_xboole_0 != k2_zfmisc_1(X0,X1)
% 11.30/1.99      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_4878]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_5390,plain,
% 11.30/1.99      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,X0)
% 11.30/1.99      | k1_xboole_0 != k2_zfmisc_1(sK0,X0)
% 11.30/1.99      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_4950]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_5391,plain,
% 11.30/1.99      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,k1_xboole_0)
% 11.30/1.99      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
% 11.30/1.99      | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_5390]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_11812,plain,
% 11.30/1.99      ( k4_xboole_0(sK0,sK2) = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 11.30/1.99      inference(superposition,[status(thm)],[c_11806,c_11]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_6,plain,
% 11.30/1.99      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 11.30/1.99      inference(cnf_transformation,[],[f29]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_7306,plain,
% 11.30/1.99      ( k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 11.30/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_12292,plain,
% 11.30/1.99      ( sK1 = k1_xboole_0 | r1_tarski(sK0,sK2) = iProver_top ),
% 11.30/1.99      inference(superposition,[status(thm)],[c_11812,c_7306]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_12326,plain,
% 11.30/1.99      ( r1_tarski(sK0,sK2) | sK1 = k1_xboole_0 ),
% 11.30/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_12292]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_23095,plain,
% 11.30/1.99      ( k2_zfmisc_1(sK0,X0) != X1
% 11.30/1.99      | k1_xboole_0 != X1
% 11.30/1.99      | k1_xboole_0 = k2_zfmisc_1(sK0,X0) ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_246]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_23096,plain,
% 11.30/1.99      ( k2_zfmisc_1(sK0,k1_xboole_0) != k1_xboole_0
% 11.30/1.99      | k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)
% 11.30/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_23095]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_9,plain,
% 11.30/1.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.30/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_23628,plain,
% 11.30/1.99      ( k2_zfmisc_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_25628,plain,
% 11.30/1.99      ( r1_tarski(sK1,sK3) | k4_xboole_0(sK1,sK3) != k1_xboole_0 ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_6]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_25651,plain,
% 11.30/1.99      ( k4_xboole_0(sK1,sK3) != X0
% 11.30/1.99      | k4_xboole_0(sK1,sK3) = k1_xboole_0
% 11.30/1.99      | k1_xboole_0 != X0 ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_246]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_26318,plain,
% 11.30/1.99      ( k4_xboole_0(sK1,sK3) != k4_xboole_0(sK1,sK3)
% 11.30/1.99      | k4_xboole_0(sK1,sK3) = k1_xboole_0
% 11.30/1.99      | k1_xboole_0 != k4_xboole_0(sK1,sK3) ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_25651]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_26319,plain,
% 11.30/1.99      ( k4_xboole_0(sK1,sK3) = k1_xboole_0
% 11.30/1.99      | k1_xboole_0 != k4_xboole_0(sK1,sK3) ),
% 11.30/1.99      inference(equality_resolution_simp,[status(thm)],[c_26318]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_19628,plain,
% 11.30/1.99      ( k2_zfmisc_1(sK0,X0) != k1_xboole_0
% 11.30/1.99      | k1_xboole_0 = X0
% 11.30/1.99      | k1_xboole_0 = sK0 ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_28365,plain,
% 11.30/1.99      ( k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) != k1_xboole_0
% 11.30/1.99      | k1_xboole_0 = k4_xboole_0(sK1,sK3)
% 11.30/1.99      | k1_xboole_0 = sK0 ),
% 11.30/1.99      inference(instantiation,[status(thm)],[c_19628]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_32335,plain,
% 11.30/1.99      ( sK0 = k1_xboole_0 ),
% 11.30/1.99      inference(global_propositional_subsumption,
% 11.30/1.99                [status(thm)],
% 11.30/1.99                [c_31257,c_16,c_15,c_25,c_26,c_5065,c_5339,c_5391,c_12326,
% 11.30/1.99                 c_23096,c_23628,c_25628,c_26319,c_28365,c_30572]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_32428,plain,
% 11.30/1.99      ( k2_zfmisc_1(k1_xboole_0,sK1) != k1_xboole_0 ),
% 11.30/1.99      inference(demodulation,[status(thm)],[c_32335,c_16]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_32430,plain,
% 11.30/1.99      ( k1_xboole_0 != k1_xboole_0 ),
% 11.30/1.99      inference(demodulation,[status(thm)],[c_32428,c_10]) ).
% 11.30/1.99  
% 11.30/1.99  cnf(c_32431,plain,
% 11.30/1.99      ( $false ),
% 11.30/1.99      inference(equality_resolution_simp,[status(thm)],[c_32430]) ).
% 11.30/1.99  
% 11.30/1.99  
% 11.30/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.30/1.99  
% 11.30/1.99  ------                               Statistics
% 11.30/1.99  
% 11.30/1.99  ------ Selected
% 11.30/1.99  
% 11.30/1.99  total_time:                             1.079
% 11.30/1.99  
%------------------------------------------------------------------------------
