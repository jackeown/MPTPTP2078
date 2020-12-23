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
% DateTime   : Thu Dec  3 11:43:38 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 132 expanded)
%              Number of clauses        :   43 (  49 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  172 ( 407 expanded)
%              Number of equality atoms :   66 (  77 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
          & v1_relat_1(X2) )
     => ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,sK2)),k5_relat_1(X0,k6_subset_1(X1,sK2)))
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,sK1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(sK1,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16,f15,f14])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f28,plain,(
    ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_99,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1079,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(X2,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
    | k5_relat_1(X2,sK1) != X0
    | k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) != X1 ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(c_1577,plain,
    ( ~ r1_tarski(X0,k5_relat_1(X1,X2))
    | r1_tarski(k5_relat_1(X3,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
    | k5_relat_1(X3,sK1) != X0
    | k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) != k5_relat_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_1079])).

cnf(c_4141,plain,
    ( ~ r1_tarski(k5_relat_1(X0,sK1),k5_relat_1(X1,X2))
    | r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
    | k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) != k5_relat_1(X1,X2)
    | k5_relat_1(sK0,sK1) != k5_relat_1(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_1577])).

cnf(c_17209,plain,
    ( ~ r1_tarski(k5_relat_1(X0,sK1),k5_relat_1(X1,k2_xboole_0(sK2,sK1)))
    | r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
    | k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) != k5_relat_1(X1,k2_xboole_0(sK2,sK1))
    | k5_relat_1(sK0,sK1) != k5_relat_1(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_4141])).

cnf(c_17215,plain,
    ( r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
    | ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,sK1)))
    | k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) != k5_relat_1(sK0,k2_xboole_0(sK2,sK1))
    | k5_relat_1(sK0,sK1) != k5_relat_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_17209])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_9935,plain,
    ( k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) = k2_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_101,plain,
    ( X0 != X1
    | X2 != X3
    | k5_relat_1(X0,X2) = k5_relat_1(X1,X3) ),
    theory(equality)).

cnf(c_2176,plain,
    ( k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) = k5_relat_1(X0,X1)
    | k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_4990,plain,
    ( k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) = k5_relat_1(X0,k2_xboole_0(sK2,sK1))
    | k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) != k2_xboole_0(sK2,sK1)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_2176])).

cnf(c_4991,plain,
    ( k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) = k5_relat_1(sK0,k2_xboole_0(sK2,sK1))
    | k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) != k2_xboole_0(sK2,sK1)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_4990])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_245,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_246,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_244,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k2_xboole_0(k5_relat_1(X0,X2),k5_relat_1(X0,X1)) = k5_relat_1(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_248,plain,
    ( k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_563,plain,
    ( k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(sK0,X1)) = k5_relat_1(sK0,k2_xboole_0(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_244,c_248])).

cnf(c_2614,plain,
    ( k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,X0)) = k5_relat_1(sK0,k2_xboole_0(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_246,c_563])).

cnf(c_2980,plain,
    ( k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,sK1)) = k5_relat_1(sK0,k2_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_245,c_2614])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_3,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_250,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_433,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_250])).

cnf(c_3065,plain,
    ( r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2980,c_433])).

cnf(c_3079,plain,
    ( r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3065])).

cnf(c_272,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
    | k5_relat_1(sK0,sK1) != X0
    | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) != X1 ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(c_300,plain,
    ( ~ r1_tarski(k5_relat_1(X0,X1),X2)
    | r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
    | k5_relat_1(sK0,sK1) != k5_relat_1(X0,X1)
    | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) != X2 ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_372,plain,
    ( ~ r1_tarski(k5_relat_1(X0,X1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
    | r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
    | k5_relat_1(sK0,sK1) != k5_relat_1(X0,X1)
    | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) != k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_915,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
    | r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
    | k5_relat_1(sK0,sK1) != k5_relat_1(sK0,sK1)
    | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) != k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_617,plain,
    ( v1_relat_1(k6_subset_1(sK1,sK2))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_479,plain,
    ( ~ v1_relat_1(k6_subset_1(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK0)
    | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) = k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_95,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_335,plain,
    ( k5_relat_1(sK0,sK1) = k5_relat_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_264,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
    | r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_107,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17215,c_9935,c_4991,c_3079,c_915,c_617,c_479,c_335,c_264,c_107,c_6,c_7,c_8,c_9])).

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
% 0.12/0.34  % DateTime   : Tue Dec  1 12:15:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.82/1.55  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.82/1.55  
% 7.82/1.55  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.82/1.55  
% 7.82/1.55  ------  iProver source info
% 7.82/1.55  
% 7.82/1.55  git: date: 2020-06-30 10:37:57 +0100
% 7.82/1.55  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.82/1.55  git: non_committed_changes: false
% 7.82/1.55  git: last_make_outside_of_git: false
% 7.82/1.55  
% 7.82/1.55  ------ 
% 7.82/1.55  
% 7.82/1.55  ------ Input Options
% 7.82/1.55  
% 7.82/1.55  --out_options                           all
% 7.82/1.55  --tptp_safe_out                         true
% 7.82/1.55  --problem_path                          ""
% 7.82/1.55  --include_path                          ""
% 7.82/1.55  --clausifier                            res/vclausify_rel
% 7.82/1.55  --clausifier_options                    ""
% 7.82/1.55  --stdin                                 false
% 7.82/1.55  --stats_out                             all
% 7.82/1.55  
% 7.82/1.55  ------ General Options
% 7.82/1.55  
% 7.82/1.55  --fof                                   false
% 7.82/1.55  --time_out_real                         305.
% 7.82/1.55  --time_out_virtual                      -1.
% 7.82/1.55  --symbol_type_check                     false
% 7.82/1.55  --clausify_out                          false
% 7.82/1.55  --sig_cnt_out                           false
% 7.82/1.55  --trig_cnt_out                          false
% 7.82/1.55  --trig_cnt_out_tolerance                1.
% 7.82/1.55  --trig_cnt_out_sk_spl                   false
% 7.82/1.55  --abstr_cl_out                          false
% 7.82/1.55  
% 7.82/1.55  ------ Global Options
% 7.82/1.55  
% 7.82/1.55  --schedule                              default
% 7.82/1.55  --add_important_lit                     false
% 7.82/1.55  --prop_solver_per_cl                    1000
% 7.82/1.55  --min_unsat_core                        false
% 7.82/1.55  --soft_assumptions                      false
% 7.82/1.55  --soft_lemma_size                       3
% 7.82/1.55  --prop_impl_unit_size                   0
% 7.82/1.55  --prop_impl_unit                        []
% 7.82/1.55  --share_sel_clauses                     true
% 7.82/1.55  --reset_solvers                         false
% 7.82/1.55  --bc_imp_inh                            [conj_cone]
% 7.82/1.55  --conj_cone_tolerance                   3.
% 7.82/1.55  --extra_neg_conj                        none
% 7.82/1.55  --large_theory_mode                     true
% 7.82/1.55  --prolific_symb_bound                   200
% 7.82/1.55  --lt_threshold                          2000
% 7.82/1.55  --clause_weak_htbl                      true
% 7.82/1.55  --gc_record_bc_elim                     false
% 7.82/1.55  
% 7.82/1.55  ------ Preprocessing Options
% 7.82/1.55  
% 7.82/1.55  --preprocessing_flag                    true
% 7.82/1.55  --time_out_prep_mult                    0.1
% 7.82/1.55  --splitting_mode                        input
% 7.82/1.55  --splitting_grd                         true
% 7.82/1.55  --splitting_cvd                         false
% 7.82/1.55  --splitting_cvd_svl                     false
% 7.82/1.55  --splitting_nvd                         32
% 7.82/1.55  --sub_typing                            true
% 7.82/1.55  --prep_gs_sim                           true
% 7.82/1.55  --prep_unflatten                        true
% 7.82/1.55  --prep_res_sim                          true
% 7.82/1.55  --prep_upred                            true
% 7.82/1.55  --prep_sem_filter                       exhaustive
% 7.82/1.55  --prep_sem_filter_out                   false
% 7.82/1.55  --pred_elim                             true
% 7.82/1.55  --res_sim_input                         true
% 7.82/1.55  --eq_ax_congr_red                       true
% 7.82/1.55  --pure_diseq_elim                       true
% 7.82/1.55  --brand_transform                       false
% 7.82/1.55  --non_eq_to_eq                          false
% 7.82/1.55  --prep_def_merge                        true
% 7.82/1.55  --prep_def_merge_prop_impl              false
% 7.82/1.55  --prep_def_merge_mbd                    true
% 7.82/1.55  --prep_def_merge_tr_red                 false
% 7.82/1.55  --prep_def_merge_tr_cl                  false
% 7.82/1.55  --smt_preprocessing                     true
% 7.82/1.55  --smt_ac_axioms                         fast
% 7.82/1.55  --preprocessed_out                      false
% 7.82/1.55  --preprocessed_stats                    false
% 7.82/1.55  
% 7.82/1.55  ------ Abstraction refinement Options
% 7.82/1.55  
% 7.82/1.55  --abstr_ref                             []
% 7.82/1.55  --abstr_ref_prep                        false
% 7.82/1.55  --abstr_ref_until_sat                   false
% 7.82/1.55  --abstr_ref_sig_restrict                funpre
% 7.82/1.55  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.55  --abstr_ref_under                       []
% 7.82/1.55  
% 7.82/1.55  ------ SAT Options
% 7.82/1.55  
% 7.82/1.55  --sat_mode                              false
% 7.82/1.55  --sat_fm_restart_options                ""
% 7.82/1.55  --sat_gr_def                            false
% 7.82/1.55  --sat_epr_types                         true
% 7.82/1.55  --sat_non_cyclic_types                  false
% 7.82/1.55  --sat_finite_models                     false
% 7.82/1.55  --sat_fm_lemmas                         false
% 7.82/1.55  --sat_fm_prep                           false
% 7.82/1.55  --sat_fm_uc_incr                        true
% 7.82/1.55  --sat_out_model                         small
% 7.82/1.55  --sat_out_clauses                       false
% 7.82/1.55  
% 7.82/1.55  ------ QBF Options
% 7.82/1.55  
% 7.82/1.55  --qbf_mode                              false
% 7.82/1.55  --qbf_elim_univ                         false
% 7.82/1.55  --qbf_dom_inst                          none
% 7.82/1.55  --qbf_dom_pre_inst                      false
% 7.82/1.55  --qbf_sk_in                             false
% 7.82/1.55  --qbf_pred_elim                         true
% 7.82/1.55  --qbf_split                             512
% 7.82/1.55  
% 7.82/1.55  ------ BMC1 Options
% 7.82/1.55  
% 7.82/1.55  --bmc1_incremental                      false
% 7.82/1.55  --bmc1_axioms                           reachable_all
% 7.82/1.55  --bmc1_min_bound                        0
% 7.82/1.55  --bmc1_max_bound                        -1
% 7.82/1.55  --bmc1_max_bound_default                -1
% 7.82/1.55  --bmc1_symbol_reachability              true
% 7.82/1.55  --bmc1_property_lemmas                  false
% 7.82/1.55  --bmc1_k_induction                      false
% 7.82/1.55  --bmc1_non_equiv_states                 false
% 7.82/1.55  --bmc1_deadlock                         false
% 7.82/1.55  --bmc1_ucm                              false
% 7.82/1.55  --bmc1_add_unsat_core                   none
% 7.82/1.55  --bmc1_unsat_core_children              false
% 7.82/1.55  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.55  --bmc1_out_stat                         full
% 7.82/1.55  --bmc1_ground_init                      false
% 7.82/1.55  --bmc1_pre_inst_next_state              false
% 7.82/1.55  --bmc1_pre_inst_state                   false
% 7.82/1.55  --bmc1_pre_inst_reach_state             false
% 7.82/1.55  --bmc1_out_unsat_core                   false
% 7.82/1.55  --bmc1_aig_witness_out                  false
% 7.82/1.55  --bmc1_verbose                          false
% 7.82/1.55  --bmc1_dump_clauses_tptp                false
% 7.82/1.55  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.55  --bmc1_dump_file                        -
% 7.82/1.55  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.55  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.55  --bmc1_ucm_extend_mode                  1
% 7.82/1.55  --bmc1_ucm_init_mode                    2
% 7.82/1.55  --bmc1_ucm_cone_mode                    none
% 7.82/1.55  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.55  --bmc1_ucm_relax_model                  4
% 7.82/1.55  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.55  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.55  --bmc1_ucm_layered_model                none
% 7.82/1.55  --bmc1_ucm_max_lemma_size               10
% 7.82/1.55  
% 7.82/1.55  ------ AIG Options
% 7.82/1.55  
% 7.82/1.55  --aig_mode                              false
% 7.82/1.55  
% 7.82/1.55  ------ Instantiation Options
% 7.82/1.55  
% 7.82/1.55  --instantiation_flag                    true
% 7.82/1.55  --inst_sos_flag                         true
% 7.82/1.55  --inst_sos_phase                        true
% 7.82/1.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.55  --inst_lit_sel_side                     num_symb
% 7.82/1.55  --inst_solver_per_active                1400
% 7.82/1.55  --inst_solver_calls_frac                1.
% 7.82/1.55  --inst_passive_queue_type               priority_queues
% 7.82/1.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.55  --inst_passive_queues_freq              [25;2]
% 7.82/1.55  --inst_dismatching                      true
% 7.82/1.55  --inst_eager_unprocessed_to_passive     true
% 7.82/1.55  --inst_prop_sim_given                   true
% 7.82/1.55  --inst_prop_sim_new                     false
% 7.82/1.55  --inst_subs_new                         false
% 7.82/1.55  --inst_eq_res_simp                      false
% 7.82/1.55  --inst_subs_given                       false
% 7.82/1.55  --inst_orphan_elimination               true
% 7.82/1.55  --inst_learning_loop_flag               true
% 7.82/1.55  --inst_learning_start                   3000
% 7.82/1.55  --inst_learning_factor                  2
% 7.82/1.55  --inst_start_prop_sim_after_learn       3
% 7.82/1.55  --inst_sel_renew                        solver
% 7.82/1.55  --inst_lit_activity_flag                true
% 7.82/1.55  --inst_restr_to_given                   false
% 7.82/1.55  --inst_activity_threshold               500
% 7.82/1.55  --inst_out_proof                        true
% 7.82/1.55  
% 7.82/1.55  ------ Resolution Options
% 7.82/1.55  
% 7.82/1.55  --resolution_flag                       true
% 7.82/1.55  --res_lit_sel                           adaptive
% 7.82/1.55  --res_lit_sel_side                      none
% 7.82/1.55  --res_ordering                          kbo
% 7.82/1.55  --res_to_prop_solver                    active
% 7.82/1.55  --res_prop_simpl_new                    false
% 7.82/1.55  --res_prop_simpl_given                  true
% 7.82/1.55  --res_passive_queue_type                priority_queues
% 7.82/1.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.55  --res_passive_queues_freq               [15;5]
% 7.82/1.55  --res_forward_subs                      full
% 7.82/1.55  --res_backward_subs                     full
% 7.82/1.55  --res_forward_subs_resolution           true
% 7.82/1.55  --res_backward_subs_resolution          true
% 7.82/1.55  --res_orphan_elimination                true
% 7.82/1.55  --res_time_limit                        2.
% 7.82/1.55  --res_out_proof                         true
% 7.82/1.55  
% 7.82/1.55  ------ Superposition Options
% 7.82/1.55  
% 7.82/1.55  --superposition_flag                    true
% 7.82/1.55  --sup_passive_queue_type                priority_queues
% 7.82/1.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.55  --sup_passive_queues_freq               [8;1;4]
% 7.82/1.55  --demod_completeness_check              fast
% 7.82/1.55  --demod_use_ground                      true
% 7.82/1.55  --sup_to_prop_solver                    passive
% 7.82/1.55  --sup_prop_simpl_new                    true
% 7.82/1.55  --sup_prop_simpl_given                  true
% 7.82/1.55  --sup_fun_splitting                     true
% 7.82/1.55  --sup_smt_interval                      50000
% 7.82/1.55  
% 7.82/1.55  ------ Superposition Simplification Setup
% 7.82/1.55  
% 7.82/1.55  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.82/1.55  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.82/1.55  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.82/1.55  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.82/1.55  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.82/1.55  --sup_immed_triv                        [TrivRules]
% 7.82/1.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.55  --sup_immed_bw_main                     []
% 7.82/1.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.82/1.55  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.55  --sup_input_bw                          []
% 7.82/1.55  
% 7.82/1.55  ------ Combination Options
% 7.82/1.55  
% 7.82/1.55  --comb_res_mult                         3
% 7.82/1.55  --comb_sup_mult                         2
% 7.82/1.55  --comb_inst_mult                        10
% 7.82/1.55  
% 7.82/1.55  ------ Debug Options
% 7.82/1.55  
% 7.82/1.55  --dbg_backtrace                         false
% 7.82/1.55  --dbg_dump_prop_clauses                 false
% 7.82/1.55  --dbg_dump_prop_clauses_file            -
% 7.82/1.55  --dbg_out_stat                          false
% 7.82/1.55  ------ Parsing...
% 7.82/1.55  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.82/1.55  
% 7.82/1.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.82/1.55  
% 7.82/1.55  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.82/1.55  
% 7.82/1.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.55  ------ Proving...
% 7.82/1.55  ------ Problem Properties 
% 7.82/1.55  
% 7.82/1.55  
% 7.82/1.55  clauses                                 10
% 7.82/1.55  conjectures                             4
% 7.82/1.55  EPR                                     3
% 7.82/1.55  Horn                                    10
% 7.82/1.55  unary                                   7
% 7.82/1.55  binary                                  2
% 7.82/1.55  lits                                    15
% 7.82/1.55  lits eq                                 3
% 7.82/1.55  fd_pure                                 0
% 7.82/1.55  fd_pseudo                               0
% 7.82/1.55  fd_cond                                 0
% 7.82/1.55  fd_pseudo_cond                          0
% 7.82/1.55  AC symbols                              0
% 7.82/1.55  
% 7.82/1.55  ------ Schedule dynamic 5 is on 
% 7.82/1.55  
% 7.82/1.55  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.82/1.55  
% 7.82/1.55  
% 7.82/1.55  ------ 
% 7.82/1.55  Current options:
% 7.82/1.55  ------ 
% 7.82/1.55  
% 7.82/1.55  ------ Input Options
% 7.82/1.55  
% 7.82/1.55  --out_options                           all
% 7.82/1.55  --tptp_safe_out                         true
% 7.82/1.55  --problem_path                          ""
% 7.82/1.55  --include_path                          ""
% 7.82/1.55  --clausifier                            res/vclausify_rel
% 7.82/1.55  --clausifier_options                    ""
% 7.82/1.55  --stdin                                 false
% 7.82/1.55  --stats_out                             all
% 7.82/1.55  
% 7.82/1.55  ------ General Options
% 7.82/1.55  
% 7.82/1.55  --fof                                   false
% 7.82/1.55  --time_out_real                         305.
% 7.82/1.55  --time_out_virtual                      -1.
% 7.82/1.55  --symbol_type_check                     false
% 7.82/1.55  --clausify_out                          false
% 7.82/1.55  --sig_cnt_out                           false
% 7.82/1.55  --trig_cnt_out                          false
% 7.82/1.55  --trig_cnt_out_tolerance                1.
% 7.82/1.55  --trig_cnt_out_sk_spl                   false
% 7.82/1.55  --abstr_cl_out                          false
% 7.82/1.55  
% 7.82/1.55  ------ Global Options
% 7.82/1.55  
% 7.82/1.55  --schedule                              default
% 7.82/1.55  --add_important_lit                     false
% 7.82/1.55  --prop_solver_per_cl                    1000
% 7.82/1.55  --min_unsat_core                        false
% 7.82/1.55  --soft_assumptions                      false
% 7.82/1.55  --soft_lemma_size                       3
% 7.82/1.55  --prop_impl_unit_size                   0
% 7.82/1.55  --prop_impl_unit                        []
% 7.82/1.55  --share_sel_clauses                     true
% 7.82/1.55  --reset_solvers                         false
% 7.82/1.55  --bc_imp_inh                            [conj_cone]
% 7.82/1.55  --conj_cone_tolerance                   3.
% 7.82/1.55  --extra_neg_conj                        none
% 7.82/1.55  --large_theory_mode                     true
% 7.82/1.55  --prolific_symb_bound                   200
% 7.82/1.55  --lt_threshold                          2000
% 7.82/1.55  --clause_weak_htbl                      true
% 7.82/1.55  --gc_record_bc_elim                     false
% 7.82/1.55  
% 7.82/1.55  ------ Preprocessing Options
% 7.82/1.55  
% 7.82/1.55  --preprocessing_flag                    true
% 7.82/1.55  --time_out_prep_mult                    0.1
% 7.82/1.55  --splitting_mode                        input
% 7.82/1.55  --splitting_grd                         true
% 7.82/1.55  --splitting_cvd                         false
% 7.82/1.55  --splitting_cvd_svl                     false
% 7.82/1.55  --splitting_nvd                         32
% 7.82/1.55  --sub_typing                            true
% 7.82/1.55  --prep_gs_sim                           true
% 7.82/1.55  --prep_unflatten                        true
% 7.82/1.55  --prep_res_sim                          true
% 7.82/1.55  --prep_upred                            true
% 7.82/1.55  --prep_sem_filter                       exhaustive
% 7.82/1.55  --prep_sem_filter_out                   false
% 7.82/1.55  --pred_elim                             true
% 7.82/1.55  --res_sim_input                         true
% 7.82/1.55  --eq_ax_congr_red                       true
% 7.82/1.55  --pure_diseq_elim                       true
% 7.82/1.55  --brand_transform                       false
% 7.82/1.55  --non_eq_to_eq                          false
% 7.82/1.55  --prep_def_merge                        true
% 7.82/1.55  --prep_def_merge_prop_impl              false
% 7.82/1.55  --prep_def_merge_mbd                    true
% 7.82/1.55  --prep_def_merge_tr_red                 false
% 7.82/1.55  --prep_def_merge_tr_cl                  false
% 7.82/1.55  --smt_preprocessing                     true
% 7.82/1.55  --smt_ac_axioms                         fast
% 7.82/1.55  --preprocessed_out                      false
% 7.82/1.55  --preprocessed_stats                    false
% 7.82/1.55  
% 7.82/1.55  ------ Abstraction refinement Options
% 7.82/1.55  
% 7.82/1.55  --abstr_ref                             []
% 7.82/1.55  --abstr_ref_prep                        false
% 7.82/1.55  --abstr_ref_until_sat                   false
% 7.82/1.55  --abstr_ref_sig_restrict                funpre
% 7.82/1.55  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.55  --abstr_ref_under                       []
% 7.82/1.55  
% 7.82/1.55  ------ SAT Options
% 7.82/1.55  
% 7.82/1.55  --sat_mode                              false
% 7.82/1.55  --sat_fm_restart_options                ""
% 7.82/1.55  --sat_gr_def                            false
% 7.82/1.55  --sat_epr_types                         true
% 7.82/1.55  --sat_non_cyclic_types                  false
% 7.82/1.55  --sat_finite_models                     false
% 7.82/1.55  --sat_fm_lemmas                         false
% 7.82/1.55  --sat_fm_prep                           false
% 7.82/1.55  --sat_fm_uc_incr                        true
% 7.82/1.55  --sat_out_model                         small
% 7.82/1.55  --sat_out_clauses                       false
% 7.82/1.55  
% 7.82/1.55  ------ QBF Options
% 7.82/1.55  
% 7.82/1.55  --qbf_mode                              false
% 7.82/1.55  --qbf_elim_univ                         false
% 7.82/1.55  --qbf_dom_inst                          none
% 7.82/1.55  --qbf_dom_pre_inst                      false
% 7.82/1.55  --qbf_sk_in                             false
% 7.82/1.55  --qbf_pred_elim                         true
% 7.82/1.55  --qbf_split                             512
% 7.82/1.55  
% 7.82/1.55  ------ BMC1 Options
% 7.82/1.55  
% 7.82/1.55  --bmc1_incremental                      false
% 7.82/1.55  --bmc1_axioms                           reachable_all
% 7.82/1.55  --bmc1_min_bound                        0
% 7.82/1.55  --bmc1_max_bound                        -1
% 7.82/1.55  --bmc1_max_bound_default                -1
% 7.82/1.55  --bmc1_symbol_reachability              true
% 7.82/1.55  --bmc1_property_lemmas                  false
% 7.82/1.55  --bmc1_k_induction                      false
% 7.82/1.55  --bmc1_non_equiv_states                 false
% 7.82/1.55  --bmc1_deadlock                         false
% 7.82/1.55  --bmc1_ucm                              false
% 7.82/1.55  --bmc1_add_unsat_core                   none
% 7.82/1.55  --bmc1_unsat_core_children              false
% 7.82/1.55  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.55  --bmc1_out_stat                         full
% 7.82/1.55  --bmc1_ground_init                      false
% 7.82/1.55  --bmc1_pre_inst_next_state              false
% 7.82/1.55  --bmc1_pre_inst_state                   false
% 7.82/1.55  --bmc1_pre_inst_reach_state             false
% 7.82/1.55  --bmc1_out_unsat_core                   false
% 7.82/1.55  --bmc1_aig_witness_out                  false
% 7.82/1.55  --bmc1_verbose                          false
% 7.82/1.55  --bmc1_dump_clauses_tptp                false
% 7.82/1.55  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.55  --bmc1_dump_file                        -
% 7.82/1.55  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.55  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.55  --bmc1_ucm_extend_mode                  1
% 7.82/1.55  --bmc1_ucm_init_mode                    2
% 7.82/1.55  --bmc1_ucm_cone_mode                    none
% 7.82/1.55  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.55  --bmc1_ucm_relax_model                  4
% 7.82/1.55  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.55  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.55  --bmc1_ucm_layered_model                none
% 7.82/1.55  --bmc1_ucm_max_lemma_size               10
% 7.82/1.55  
% 7.82/1.55  ------ AIG Options
% 7.82/1.55  
% 7.82/1.55  --aig_mode                              false
% 7.82/1.55  
% 7.82/1.55  ------ Instantiation Options
% 7.82/1.55  
% 7.82/1.55  --instantiation_flag                    true
% 7.82/1.55  --inst_sos_flag                         true
% 7.82/1.55  --inst_sos_phase                        true
% 7.82/1.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.55  --inst_lit_sel_side                     none
% 7.82/1.55  --inst_solver_per_active                1400
% 7.82/1.55  --inst_solver_calls_frac                1.
% 7.82/1.55  --inst_passive_queue_type               priority_queues
% 7.82/1.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.55  --inst_passive_queues_freq              [25;2]
% 7.82/1.55  --inst_dismatching                      true
% 7.82/1.55  --inst_eager_unprocessed_to_passive     true
% 7.82/1.55  --inst_prop_sim_given                   true
% 7.82/1.55  --inst_prop_sim_new                     false
% 7.82/1.55  --inst_subs_new                         false
% 7.82/1.55  --inst_eq_res_simp                      false
% 7.82/1.55  --inst_subs_given                       false
% 7.82/1.55  --inst_orphan_elimination               true
% 7.82/1.55  --inst_learning_loop_flag               true
% 7.82/1.55  --inst_learning_start                   3000
% 7.82/1.55  --inst_learning_factor                  2
% 7.82/1.55  --inst_start_prop_sim_after_learn       3
% 7.82/1.55  --inst_sel_renew                        solver
% 7.82/1.55  --inst_lit_activity_flag                true
% 7.82/1.55  --inst_restr_to_given                   false
% 7.82/1.55  --inst_activity_threshold               500
% 7.82/1.55  --inst_out_proof                        true
% 7.82/1.55  
% 7.82/1.55  ------ Resolution Options
% 7.82/1.55  
% 7.82/1.55  --resolution_flag                       false
% 7.82/1.55  --res_lit_sel                           adaptive
% 7.82/1.55  --res_lit_sel_side                      none
% 7.82/1.55  --res_ordering                          kbo
% 7.82/1.55  --res_to_prop_solver                    active
% 7.82/1.55  --res_prop_simpl_new                    false
% 7.82/1.55  --res_prop_simpl_given                  true
% 7.82/1.55  --res_passive_queue_type                priority_queues
% 7.82/1.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.55  --res_passive_queues_freq               [15;5]
% 7.82/1.55  --res_forward_subs                      full
% 7.82/1.55  --res_backward_subs                     full
% 7.82/1.55  --res_forward_subs_resolution           true
% 7.82/1.55  --res_backward_subs_resolution          true
% 7.82/1.55  --res_orphan_elimination                true
% 7.82/1.55  --res_time_limit                        2.
% 7.82/1.55  --res_out_proof                         true
% 7.82/1.55  
% 7.82/1.55  ------ Superposition Options
% 7.82/1.55  
% 7.82/1.55  --superposition_flag                    true
% 7.82/1.55  --sup_passive_queue_type                priority_queues
% 7.82/1.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.55  --sup_passive_queues_freq               [8;1;4]
% 7.82/1.55  --demod_completeness_check              fast
% 7.82/1.55  --demod_use_ground                      true
% 7.82/1.55  --sup_to_prop_solver                    passive
% 7.82/1.55  --sup_prop_simpl_new                    true
% 7.82/1.55  --sup_prop_simpl_given                  true
% 7.82/1.55  --sup_fun_splitting                     true
% 7.82/1.55  --sup_smt_interval                      50000
% 7.82/1.55  
% 7.82/1.55  ------ Superposition Simplification Setup
% 7.82/1.55  
% 7.82/1.55  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.82/1.55  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.82/1.55  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.82/1.55  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.82/1.55  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.82/1.55  --sup_immed_triv                        [TrivRules]
% 7.82/1.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.55  --sup_immed_bw_main                     []
% 7.82/1.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.82/1.55  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.55  --sup_input_bw                          []
% 7.82/1.55  
% 7.82/1.55  ------ Combination Options
% 7.82/1.55  
% 7.82/1.55  --comb_res_mult                         3
% 7.82/1.55  --comb_sup_mult                         2
% 7.82/1.55  --comb_inst_mult                        10
% 7.82/1.55  
% 7.82/1.55  ------ Debug Options
% 7.82/1.55  
% 7.82/1.55  --dbg_backtrace                         false
% 7.82/1.55  --dbg_dump_prop_clauses                 false
% 7.82/1.55  --dbg_dump_prop_clauses_file            -
% 7.82/1.55  --dbg_out_stat                          false
% 7.82/1.55  
% 7.82/1.55  
% 7.82/1.55  
% 7.82/1.55  
% 7.82/1.55  ------ Proving...
% 7.82/1.55  
% 7.82/1.55  
% 7.82/1.55  % SZS status Theorem for theBenchmark.p
% 7.82/1.55  
% 7.82/1.55  % SZS output start CNFRefutation for theBenchmark.p
% 7.82/1.55  
% 7.82/1.55  fof(f2,axiom,(
% 7.82/1.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.82/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.55  
% 7.82/1.55  fof(f19,plain,(
% 7.82/1.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.82/1.55    inference(cnf_transformation,[],[f2])).
% 7.82/1.55  
% 7.82/1.55  fof(f5,axiom,(
% 7.82/1.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.82/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.55  
% 7.82/1.55  fof(f22,plain,(
% 7.82/1.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.82/1.55    inference(cnf_transformation,[],[f5])).
% 7.82/1.55  
% 7.82/1.55  fof(f29,plain,(
% 7.82/1.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 7.82/1.55    inference(definition_unfolding,[],[f19,f22])).
% 7.82/1.55  
% 7.82/1.55  fof(f8,conjecture,(
% 7.82/1.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))))))),
% 7.82/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.55  
% 7.82/1.55  fof(f9,negated_conjecture,(
% 7.82/1.55    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))))))),
% 7.82/1.55    inference(negated_conjecture,[],[f8])).
% 7.82/1.55  
% 7.82/1.55  fof(f13,plain,(
% 7.82/1.55    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.82/1.55    inference(ennf_transformation,[],[f9])).
% 7.82/1.55  
% 7.82/1.55  fof(f16,plain,(
% 7.82/1.55    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) => (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,sK2)),k5_relat_1(X0,k6_subset_1(X1,sK2))) & v1_relat_1(sK2))) )),
% 7.82/1.55    introduced(choice_axiom,[])).
% 7.82/1.55  
% 7.82/1.55  fof(f15,plain,(
% 7.82/1.55    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,sK1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(sK1,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))) )),
% 7.82/1.55    introduced(choice_axiom,[])).
% 7.82/1.55  
% 7.82/1.55  fof(f14,plain,(
% 7.82/1.55    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k6_subset_1(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)),k5_relat_1(sK0,k6_subset_1(X1,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 7.82/1.55    introduced(choice_axiom,[])).
% 7.82/1.55  
% 7.82/1.55  fof(f17,plain,(
% 7.82/1.55    ((~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 7.82/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16,f15,f14])).
% 7.82/1.55  
% 7.82/1.55  fof(f26,plain,(
% 7.82/1.55    v1_relat_1(sK1)),
% 7.82/1.55    inference(cnf_transformation,[],[f17])).
% 7.82/1.55  
% 7.82/1.55  fof(f27,plain,(
% 7.82/1.55    v1_relat_1(sK2)),
% 7.82/1.55    inference(cnf_transformation,[],[f17])).
% 7.82/1.55  
% 7.82/1.55  fof(f25,plain,(
% 7.82/1.55    v1_relat_1(sK0)),
% 7.82/1.55    inference(cnf_transformation,[],[f17])).
% 7.82/1.55  
% 7.82/1.55  fof(f7,axiom,(
% 7.82/1.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2)))))),
% 7.82/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.55  
% 7.82/1.55  fof(f12,plain,(
% 7.82/1.55    ! [X0] : (! [X1] : (! [X2] : (k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.82/1.55    inference(ennf_transformation,[],[f7])).
% 7.82/1.55  
% 7.82/1.55  fof(f24,plain,(
% 7.82/1.55    ( ! [X2,X0,X1] : (k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.82/1.55    inference(cnf_transformation,[],[f12])).
% 7.82/1.55  
% 7.82/1.55  fof(f1,axiom,(
% 7.82/1.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.82/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.55  
% 7.82/1.55  fof(f18,plain,(
% 7.82/1.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.82/1.55    inference(cnf_transformation,[],[f1])).
% 7.82/1.55  
% 7.82/1.55  fof(f4,axiom,(
% 7.82/1.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.82/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.55  
% 7.82/1.55  fof(f21,plain,(
% 7.82/1.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.82/1.55    inference(cnf_transformation,[],[f4])).
% 7.82/1.55  
% 7.82/1.55  fof(f6,axiom,(
% 7.82/1.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 7.82/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.55  
% 7.82/1.55  fof(f11,plain,(
% 7.82/1.55    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 7.82/1.55    inference(ennf_transformation,[],[f6])).
% 7.82/1.55  
% 7.82/1.55  fof(f23,plain,(
% 7.82/1.55    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.82/1.55    inference(cnf_transformation,[],[f11])).
% 7.82/1.55  
% 7.82/1.55  fof(f31,plain,(
% 7.82/1.55    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.82/1.55    inference(definition_unfolding,[],[f23,f22])).
% 7.82/1.55  
% 7.82/1.55  fof(f3,axiom,(
% 7.82/1.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.82/1.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.82/1.55  
% 7.82/1.55  fof(f10,plain,(
% 7.82/1.55    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.82/1.55    inference(ennf_transformation,[],[f3])).
% 7.82/1.55  
% 7.82/1.55  fof(f20,plain,(
% 7.82/1.55    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.82/1.55    inference(cnf_transformation,[],[f10])).
% 7.82/1.55  
% 7.82/1.55  fof(f30,plain,(
% 7.82/1.55    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.82/1.55    inference(definition_unfolding,[],[f20,f22])).
% 7.82/1.55  
% 7.82/1.55  fof(f28,plain,(
% 7.82/1.55    ~r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2)))),
% 7.82/1.55    inference(cnf_transformation,[],[f17])).
% 7.82/1.55  
% 7.82/1.55  cnf(c_99,plain,
% 7.82/1.55      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.82/1.55      theory(equality) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_1079,plain,
% 7.82/1.55      ( ~ r1_tarski(X0,X1)
% 7.82/1.55      | r1_tarski(k5_relat_1(X2,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
% 7.82/1.55      | k5_relat_1(X2,sK1) != X0
% 7.82/1.55      | k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) != X1 ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_99]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_1577,plain,
% 7.82/1.55      ( ~ r1_tarski(X0,k5_relat_1(X1,X2))
% 7.82/1.55      | r1_tarski(k5_relat_1(X3,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
% 7.82/1.55      | k5_relat_1(X3,sK1) != X0
% 7.82/1.55      | k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) != k5_relat_1(X1,X2) ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_1079]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_4141,plain,
% 7.82/1.55      ( ~ r1_tarski(k5_relat_1(X0,sK1),k5_relat_1(X1,X2))
% 7.82/1.55      | r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
% 7.82/1.55      | k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) != k5_relat_1(X1,X2)
% 7.82/1.55      | k5_relat_1(sK0,sK1) != k5_relat_1(X0,sK1) ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_1577]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_17209,plain,
% 7.82/1.55      ( ~ r1_tarski(k5_relat_1(X0,sK1),k5_relat_1(X1,k2_xboole_0(sK2,sK1)))
% 7.82/1.55      | r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
% 7.82/1.55      | k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) != k5_relat_1(X1,k2_xboole_0(sK2,sK1))
% 7.82/1.55      | k5_relat_1(sK0,sK1) != k5_relat_1(X0,sK1) ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_4141]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_17215,plain,
% 7.82/1.55      ( r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
% 7.82/1.55      | ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,sK1)))
% 7.82/1.55      | k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) != k5_relat_1(sK0,k2_xboole_0(sK2,sK1))
% 7.82/1.55      | k5_relat_1(sK0,sK1) != k5_relat_1(sK0,sK1) ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_17209]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_1,plain,
% 7.82/1.55      ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.82/1.55      inference(cnf_transformation,[],[f29]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_9935,plain,
% 7.82/1.55      ( k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) = k2_xboole_0(sK2,sK1) ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_1]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_101,plain,
% 7.82/1.55      ( X0 != X1 | X2 != X3 | k5_relat_1(X0,X2) = k5_relat_1(X1,X3) ),
% 7.82/1.55      theory(equality) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_2176,plain,
% 7.82/1.55      ( k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) = k5_relat_1(X0,X1)
% 7.82/1.55      | k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) != X1
% 7.82/1.55      | sK0 != X0 ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_101]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_4990,plain,
% 7.82/1.55      ( k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) = k5_relat_1(X0,k2_xboole_0(sK2,sK1))
% 7.82/1.55      | k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) != k2_xboole_0(sK2,sK1)
% 7.82/1.55      | sK0 != X0 ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_2176]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_4991,plain,
% 7.82/1.55      ( k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) = k5_relat_1(sK0,k2_xboole_0(sK2,sK1))
% 7.82/1.55      | k2_xboole_0(sK2,k6_subset_1(sK1,sK2)) != k2_xboole_0(sK2,sK1)
% 7.82/1.55      | sK0 != sK0 ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_4990]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_8,negated_conjecture,
% 7.82/1.55      ( v1_relat_1(sK1) ),
% 7.82/1.55      inference(cnf_transformation,[],[f26]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_245,plain,
% 7.82/1.55      ( v1_relat_1(sK1) = iProver_top ),
% 7.82/1.55      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_7,negated_conjecture,
% 7.82/1.55      ( v1_relat_1(sK2) ),
% 7.82/1.55      inference(cnf_transformation,[],[f27]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_246,plain,
% 7.82/1.55      ( v1_relat_1(sK2) = iProver_top ),
% 7.82/1.55      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_9,negated_conjecture,
% 7.82/1.55      ( v1_relat_1(sK0) ),
% 7.82/1.55      inference(cnf_transformation,[],[f25]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_244,plain,
% 7.82/1.55      ( v1_relat_1(sK0) = iProver_top ),
% 7.82/1.55      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_5,plain,
% 7.82/1.55      ( ~ v1_relat_1(X0)
% 7.82/1.55      | ~ v1_relat_1(X1)
% 7.82/1.55      | ~ v1_relat_1(X2)
% 7.82/1.55      | k2_xboole_0(k5_relat_1(X0,X2),k5_relat_1(X0,X1)) = k5_relat_1(X0,k2_xboole_0(X2,X1)) ),
% 7.82/1.55      inference(cnf_transformation,[],[f24]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_248,plain,
% 7.82/1.55      ( k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) = k5_relat_1(X0,k2_xboole_0(X1,X2))
% 7.82/1.55      | v1_relat_1(X0) != iProver_top
% 7.82/1.55      | v1_relat_1(X2) != iProver_top
% 7.82/1.55      | v1_relat_1(X1) != iProver_top ),
% 7.82/1.55      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_563,plain,
% 7.82/1.55      ( k2_xboole_0(k5_relat_1(sK0,X0),k5_relat_1(sK0,X1)) = k5_relat_1(sK0,k2_xboole_0(X0,X1))
% 7.82/1.55      | v1_relat_1(X0) != iProver_top
% 7.82/1.55      | v1_relat_1(X1) != iProver_top ),
% 7.82/1.55      inference(superposition,[status(thm)],[c_244,c_248]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_2614,plain,
% 7.82/1.55      ( k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,X0)) = k5_relat_1(sK0,k2_xboole_0(sK2,X0))
% 7.82/1.55      | v1_relat_1(X0) != iProver_top ),
% 7.82/1.55      inference(superposition,[status(thm)],[c_246,c_563]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_2980,plain,
% 7.82/1.55      ( k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,sK1)) = k5_relat_1(sK0,k2_xboole_0(sK2,sK1)) ),
% 7.82/1.55      inference(superposition,[status(thm)],[c_245,c_2614]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_0,plain,
% 7.82/1.55      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.82/1.55      inference(cnf_transformation,[],[f18]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_3,plain,
% 7.82/1.55      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.82/1.55      inference(cnf_transformation,[],[f21]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_250,plain,
% 7.82/1.55      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.82/1.55      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_433,plain,
% 7.82/1.55      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 7.82/1.55      inference(superposition,[status(thm)],[c_0,c_250]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_3065,plain,
% 7.82/1.55      ( r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,sK1))) = iProver_top ),
% 7.82/1.55      inference(superposition,[status(thm)],[c_2980,c_433]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_3079,plain,
% 7.82/1.55      ( r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,sK1))) ),
% 7.82/1.55      inference(predicate_to_equality_rev,[status(thm)],[c_3065]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_272,plain,
% 7.82/1.55      ( ~ r1_tarski(X0,X1)
% 7.82/1.55      | r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
% 7.82/1.55      | k5_relat_1(sK0,sK1) != X0
% 7.82/1.55      | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) != X1 ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_99]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_300,plain,
% 7.82/1.55      ( ~ r1_tarski(k5_relat_1(X0,X1),X2)
% 7.82/1.55      | r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
% 7.82/1.55      | k5_relat_1(sK0,sK1) != k5_relat_1(X0,X1)
% 7.82/1.55      | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) != X2 ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_272]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_372,plain,
% 7.82/1.55      ( ~ r1_tarski(k5_relat_1(X0,X1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
% 7.82/1.55      | r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
% 7.82/1.55      | k5_relat_1(sK0,sK1) != k5_relat_1(X0,X1)
% 7.82/1.55      | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) != k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_300]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_915,plain,
% 7.82/1.55      ( ~ r1_tarski(k5_relat_1(sK0,sK1),k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))))
% 7.82/1.55      | r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
% 7.82/1.55      | k5_relat_1(sK0,sK1) != k5_relat_1(sK0,sK1)
% 7.82/1.55      | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) != k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_372]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_4,plain,
% 7.82/1.55      ( ~ v1_relat_1(X0) | v1_relat_1(k6_subset_1(X0,X1)) ),
% 7.82/1.55      inference(cnf_transformation,[],[f31]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_617,plain,
% 7.82/1.55      ( v1_relat_1(k6_subset_1(sK1,sK2)) | ~ v1_relat_1(sK1) ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_4]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_479,plain,
% 7.82/1.55      ( ~ v1_relat_1(k6_subset_1(sK1,sK2))
% 7.82/1.55      | ~ v1_relat_1(sK2)
% 7.82/1.55      | ~ v1_relat_1(sK0)
% 7.82/1.55      | k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) = k5_relat_1(sK0,k2_xboole_0(sK2,k6_subset_1(sK1,sK2))) ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_5]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_95,plain,( X0 = X0 ),theory(equality) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_335,plain,
% 7.82/1.55      ( k5_relat_1(sK0,sK1) = k5_relat_1(sK0,sK1) ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_95]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_2,plain,
% 7.82/1.55      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 7.82/1.55      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 7.82/1.55      inference(cnf_transformation,[],[f30]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_264,plain,
% 7.82/1.55      ( ~ r1_tarski(k5_relat_1(sK0,sK1),k2_xboole_0(k5_relat_1(sK0,sK2),k5_relat_1(sK0,k6_subset_1(sK1,sK2))))
% 7.82/1.55      | r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_2]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_107,plain,
% 7.82/1.55      ( sK0 = sK0 ),
% 7.82/1.55      inference(instantiation,[status(thm)],[c_95]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(c_6,negated_conjecture,
% 7.82/1.55      ( ~ r1_tarski(k6_subset_1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)),k5_relat_1(sK0,k6_subset_1(sK1,sK2))) ),
% 7.82/1.55      inference(cnf_transformation,[],[f28]) ).
% 7.82/1.55  
% 7.82/1.55  cnf(contradiction,plain,
% 7.82/1.55      ( $false ),
% 7.82/1.55      inference(minisat,
% 7.82/1.55                [status(thm)],
% 7.82/1.55                [c_17215,c_9935,c_4991,c_3079,c_915,c_617,c_479,c_335,
% 7.82/1.55                 c_264,c_107,c_6,c_7,c_8,c_9]) ).
% 7.82/1.55  
% 7.82/1.55  
% 7.82/1.55  % SZS output end CNFRefutation for theBenchmark.p
% 7.82/1.55  
% 7.82/1.55  ------                               Statistics
% 7.82/1.55  
% 7.82/1.55  ------ General
% 7.82/1.55  
% 7.82/1.55  abstr_ref_over_cycles:                  0
% 7.82/1.55  abstr_ref_under_cycles:                 0
% 7.82/1.55  gc_basic_clause_elim:                   0
% 7.82/1.55  forced_gc_time:                         0
% 7.82/1.55  parsing_time:                           0.012
% 7.82/1.55  unif_index_cands_time:                  0.
% 7.82/1.55  unif_index_add_time:                    0.
% 7.82/1.55  orderings_time:                         0.
% 7.82/1.55  out_proof_time:                         0.008
% 7.82/1.55  total_time:                             0.575
% 7.82/1.55  num_of_symbols:                         39
% 7.82/1.55  num_of_terms:                           16843
% 7.82/1.55  
% 7.82/1.55  ------ Preprocessing
% 7.82/1.55  
% 7.82/1.55  num_of_splits:                          0
% 7.82/1.55  num_of_split_atoms:                     0
% 7.82/1.55  num_of_reused_defs:                     0
% 7.82/1.55  num_eq_ax_congr_red:                    0
% 7.82/1.55  num_of_sem_filtered_clauses:            1
% 7.82/1.55  num_of_subtypes:                        1
% 7.82/1.55  monotx_restored_types:                  0
% 7.82/1.55  sat_num_of_epr_types:                   0
% 7.82/1.55  sat_num_of_non_cyclic_types:            0
% 7.82/1.55  sat_guarded_non_collapsed_types:        0
% 7.82/1.55  num_pure_diseq_elim:                    0
% 7.82/1.55  simp_replaced_by:                       0
% 7.82/1.55  res_preprocessed:                       45
% 7.82/1.55  prep_upred:                             0
% 7.82/1.55  prep_unflattend:                        0
% 7.82/1.55  smt_new_axioms:                         0
% 7.82/1.55  pred_elim_cands:                        2
% 7.82/1.55  pred_elim:                              0
% 7.82/1.55  pred_elim_cl:                           0
% 7.82/1.55  pred_elim_cycles:                       1
% 7.82/1.55  merged_defs:                            0
% 7.82/1.55  merged_defs_ncl:                        0
% 7.82/1.55  bin_hyper_res:                          0
% 7.82/1.55  prep_cycles:                            3
% 7.82/1.55  pred_elim_time:                         0.
% 7.82/1.55  splitting_time:                         0.
% 7.82/1.55  sem_filter_time:                        0.
% 7.82/1.55  monotx_time:                            0.
% 7.82/1.55  subtype_inf_time:                       0.
% 7.82/1.55  
% 7.82/1.55  ------ Problem properties
% 7.82/1.55  
% 7.82/1.55  clauses:                                10
% 7.82/1.55  conjectures:                            4
% 7.82/1.55  epr:                                    3
% 7.82/1.55  horn:                                   10
% 7.82/1.55  ground:                                 4
% 7.82/1.55  unary:                                  7
% 7.82/1.55  binary:                                 2
% 7.82/1.55  lits:                                   15
% 7.82/1.55  lits_eq:                                3
% 7.82/1.55  fd_pure:                                0
% 7.82/1.55  fd_pseudo:                              0
% 7.82/1.55  fd_cond:                                0
% 7.82/1.55  fd_pseudo_cond:                         0
% 7.82/1.55  ac_symbols:                             0
% 7.82/1.55  
% 7.82/1.55  ------ Propositional Solver
% 7.82/1.55  
% 7.82/1.55  prop_solver_calls:                      33
% 7.82/1.55  prop_fast_solver_calls:                 435
% 7.82/1.55  smt_solver_calls:                       0
% 7.82/1.55  smt_fast_solver_calls:                  0
% 7.82/1.55  prop_num_of_clauses:                    6912
% 7.82/1.55  prop_preprocess_simplified:             11729
% 7.82/1.55  prop_fo_subsumed:                       0
% 7.82/1.55  prop_solver_time:                       0.
% 7.82/1.55  smt_solver_time:                        0.
% 7.82/1.55  smt_fast_solver_time:                   0.
% 7.82/1.55  prop_fast_solver_time:                  0.
% 7.82/1.55  prop_unsat_core_time:                   0.
% 7.82/1.55  
% 7.82/1.55  ------ QBF
% 7.82/1.55  
% 7.82/1.55  qbf_q_res:                              0
% 7.82/1.55  qbf_num_tautologies:                    0
% 7.82/1.55  qbf_prep_cycles:                        0
% 7.82/1.55  
% 7.82/1.55  ------ BMC1
% 7.82/1.55  
% 7.82/1.55  bmc1_current_bound:                     -1
% 7.82/1.55  bmc1_last_solved_bound:                 -1
% 7.82/1.55  bmc1_unsat_core_size:                   -1
% 7.82/1.55  bmc1_unsat_core_parents_size:           -1
% 7.82/1.55  bmc1_merge_next_fun:                    0
% 7.82/1.55  bmc1_unsat_core_clauses_time:           0.
% 7.82/1.55  
% 7.82/1.55  ------ Instantiation
% 7.82/1.55  
% 7.82/1.55  inst_num_of_clauses:                    1922
% 7.82/1.55  inst_num_in_passive:                    697
% 7.82/1.55  inst_num_in_active:                     877
% 7.82/1.55  inst_num_in_unprocessed:                347
% 7.82/1.55  inst_num_of_loops:                      952
% 7.82/1.55  inst_num_of_learning_restarts:          0
% 7.82/1.55  inst_num_moves_active_passive:          67
% 7.82/1.55  inst_lit_activity:                      0
% 7.82/1.55  inst_lit_activity_moves:                0
% 7.82/1.55  inst_num_tautologies:                   0
% 7.82/1.55  inst_num_prop_implied:                  0
% 7.82/1.55  inst_num_existing_simplified:           0
% 7.82/1.55  inst_num_eq_res_simplified:             0
% 7.82/1.55  inst_num_child_elim:                    0
% 7.82/1.55  inst_num_of_dismatching_blockings:      2058
% 7.82/1.55  inst_num_of_non_proper_insts:           3276
% 7.82/1.55  inst_num_of_duplicates:                 0
% 7.82/1.55  inst_inst_num_from_inst_to_res:         0
% 7.82/1.55  inst_dismatching_checking_time:         0.
% 7.82/1.55  
% 7.82/1.55  ------ Resolution
% 7.82/1.55  
% 7.82/1.55  res_num_of_clauses:                     0
% 7.82/1.55  res_num_in_passive:                     0
% 7.82/1.55  res_num_in_active:                      0
% 7.82/1.55  res_num_of_loops:                       48
% 7.82/1.55  res_forward_subset_subsumed:            787
% 7.82/1.55  res_backward_subset_subsumed:           0
% 7.82/1.55  res_forward_subsumed:                   0
% 7.82/1.55  res_backward_subsumed:                  0
% 7.82/1.55  res_forward_subsumption_resolution:     0
% 7.82/1.55  res_backward_subsumption_resolution:    0
% 7.82/1.55  res_clause_to_clause_subsumption:       5690
% 7.82/1.55  res_orphan_elimination:                 0
% 7.82/1.55  res_tautology_del:                      338
% 7.82/1.55  res_num_eq_res_simplified:              0
% 7.82/1.55  res_num_sel_changes:                    0
% 7.82/1.55  res_moves_from_active_to_pass:          0
% 7.82/1.55  
% 7.82/1.55  ------ Superposition
% 7.82/1.55  
% 7.82/1.55  sup_time_total:                         0.
% 7.82/1.55  sup_time_generating:                    0.
% 7.82/1.55  sup_time_sim_full:                      0.
% 7.82/1.55  sup_time_sim_immed:                     0.
% 7.82/1.55  
% 7.82/1.55  sup_num_of_clauses:                     1215
% 7.82/1.55  sup_num_in_active:                      180
% 7.82/1.55  sup_num_in_passive:                     1035
% 7.82/1.55  sup_num_of_loops:                       190
% 7.82/1.55  sup_fw_superposition:                   1427
% 7.82/1.55  sup_bw_superposition:                   800
% 7.82/1.55  sup_immediate_simplified:               14
% 7.82/1.55  sup_given_eliminated:                   0
% 7.82/1.55  comparisons_done:                       0
% 7.82/1.55  comparisons_avoided:                    0
% 7.82/1.55  
% 7.82/1.55  ------ Simplifications
% 7.82/1.55  
% 7.82/1.55  
% 7.82/1.55  sim_fw_subset_subsumed:                 0
% 7.82/1.55  sim_bw_subset_subsumed:                 0
% 7.82/1.55  sim_fw_subsumed:                        0
% 7.82/1.55  sim_bw_subsumed:                        0
% 7.82/1.55  sim_fw_subsumption_res:                 0
% 7.82/1.55  sim_bw_subsumption_res:                 0
% 7.82/1.55  sim_tautology_del:                      0
% 7.82/1.55  sim_eq_tautology_del:                   0
% 7.82/1.55  sim_eq_res_simp:                        0
% 7.82/1.55  sim_fw_demodulated:                     0
% 7.82/1.55  sim_bw_demodulated:                     10
% 7.82/1.55  sim_light_normalised:                   63
% 7.82/1.55  sim_joinable_taut:                      0
% 7.82/1.55  sim_joinable_simp:                      0
% 7.82/1.55  sim_ac_normalised:                      0
% 7.82/1.55  sim_smt_subsumption:                    0
% 7.82/1.55  
%------------------------------------------------------------------------------
