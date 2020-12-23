%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:11 EST 2020

% Result     : Theorem 7.29s
% Output     : CNFRefutation 7.29s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 242 expanded)
%              Number of clauses        :   71 (  88 expanded)
%              Number of leaves         :   20 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  313 ( 676 expanded)
%              Number of equality atoms :  109 ( 150 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(sK3))
        & r1_tarski(X0,sK3)
        & v1_relat_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(X1))
          & r1_tarski(sK2,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f44,f43])).

fof(f73,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f80,plain,(
    ! [X0] :
      ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f69,f65])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f61,f65])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f74,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f65])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f65])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f75,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_24,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_149,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_21,c_19])).

cnf(c_150,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_149])).

cnf(c_945,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_150])).

cnf(c_14,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_954,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_955,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4066,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_954,c_955])).

cnf(c_27,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_947,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_950,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2738,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(sK3),k2_relat_1(sK3))) = k3_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_947,c_950])).

cnf(c_18,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_953,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3669,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_953])).

cnf(c_3895,plain,
    ( r1_tarski(X0,k3_relat_1(sK3)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,k2_relat_1(sK3)),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2738,c_3669])).

cnf(c_19336,plain,
    ( r1_tarski(X0,k3_relat_1(sK3)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4066,c_3895])).

cnf(c_33209,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),k3_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_945,c_19336])).

cnf(c_33245,plain,
    ( r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) = iProver_top
    | r1_tarski(sK2,sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33209])).

cnf(c_16,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_952,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1237,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_952])).

cnf(c_3064,plain,
    ( r1_tarski(k2_relat_1(sK3),k3_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2738,c_1237])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_948,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_154,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_21,c_19])).

cnf(c_155,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_154])).

cnf(c_944,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_155])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_956,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2426,plain,
    ( k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(X1)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_944,c_956])).

cnf(c_12533,plain,
    ( k3_tarski(k2_tarski(k2_relat_1(sK2),k2_relat_1(sK3))) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_948,c_2426])).

cnf(c_30,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_12993,plain,
    ( k3_tarski(k2_tarski(k2_relat_1(sK2),k2_relat_1(sK3))) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12533,c_30])).

cnf(c_13001,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12993,c_952])).

cnf(c_13055,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13001,c_955])).

cnf(c_29965,plain,
    ( r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3064,c_13055])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1200,plain,
    ( ~ r1_tarski(X0,k3_relat_1(sK3))
    | ~ r1_tarski(X1,k3_relat_1(sK3))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k3_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_26013,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3))
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1200])).

cnf(c_26014,plain,
    ( r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) != iProver_top
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26013])).

cnf(c_527,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1152,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
    | k3_relat_1(sK3) != X1
    | k3_relat_1(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_1226,plain,
    ( ~ r1_tarski(X0,k3_relat_1(X1))
    | r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
    | k3_relat_1(sK3) != k3_relat_1(X1)
    | k3_relat_1(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1152])).

cnf(c_8275,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
    | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_relat_1(X0))
    | k3_relat_1(sK3) != k3_relat_1(X0)
    | k3_relat_1(sK2) != k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_1226])).

cnf(c_13302,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
    | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_relat_1(sK3))
    | k3_relat_1(sK3) != k3_relat_1(sK3)
    | k3_relat_1(sK2) != k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_8275])).

cnf(c_13303,plain,
    ( k3_relat_1(sK3) != k3_relat_1(sK3)
    | k3_relat_1(sK2) != k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))
    | r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) = iProver_top
    | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13302])).

cnf(c_526,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1549,plain,
    ( X0 != X1
    | k3_relat_1(sK2) != X1
    | k3_relat_1(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_2452,plain,
    ( X0 != k3_relat_1(sK2)
    | k3_relat_1(sK2) = X0
    | k3_relat_1(sK2) != k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1549])).

cnf(c_4325,plain,
    ( k3_relat_1(sK2) != k3_relat_1(sK2)
    | k3_relat_1(sK2) = k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))
    | k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) != k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2452])).

cnf(c_525,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1220,plain,
    ( k3_relat_1(sK3) = k3_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_532,plain,
    ( X0 != X1
    | k3_relat_1(X0) = k3_relat_1(X1) ),
    theory(equality)).

cnf(c_537,plain,
    ( k3_relat_1(sK2) = k3_relat_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_69,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_65,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_40,plain,
    ( ~ v1_relat_1(sK2)
    | k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_32,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_31,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33245,c_29965,c_26014,c_13303,c_4325,c_1220,c_537,c_69,c_65,c_40,c_32,c_31,c_30,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:45:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.29/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/1.50  
% 7.29/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.29/1.50  
% 7.29/1.50  ------  iProver source info
% 7.29/1.50  
% 7.29/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.29/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.29/1.50  git: non_committed_changes: false
% 7.29/1.50  git: last_make_outside_of_git: false
% 7.29/1.50  
% 7.29/1.50  ------ 
% 7.29/1.50  
% 7.29/1.50  ------ Input Options
% 7.29/1.50  
% 7.29/1.50  --out_options                           all
% 7.29/1.50  --tptp_safe_out                         true
% 7.29/1.50  --problem_path                          ""
% 7.29/1.50  --include_path                          ""
% 7.29/1.50  --clausifier                            res/vclausify_rel
% 7.29/1.50  --clausifier_options                    --mode clausify
% 7.29/1.50  --stdin                                 false
% 7.29/1.50  --stats_out                             all
% 7.29/1.50  
% 7.29/1.50  ------ General Options
% 7.29/1.50  
% 7.29/1.50  --fof                                   false
% 7.29/1.50  --time_out_real                         305.
% 7.29/1.50  --time_out_virtual                      -1.
% 7.29/1.50  --symbol_type_check                     false
% 7.29/1.50  --clausify_out                          false
% 7.29/1.50  --sig_cnt_out                           false
% 7.29/1.50  --trig_cnt_out                          false
% 7.29/1.50  --trig_cnt_out_tolerance                1.
% 7.29/1.50  --trig_cnt_out_sk_spl                   false
% 7.29/1.50  --abstr_cl_out                          false
% 7.29/1.50  
% 7.29/1.50  ------ Global Options
% 7.29/1.50  
% 7.29/1.50  --schedule                              default
% 7.29/1.50  --add_important_lit                     false
% 7.29/1.50  --prop_solver_per_cl                    1000
% 7.29/1.50  --min_unsat_core                        false
% 7.29/1.50  --soft_assumptions                      false
% 7.29/1.50  --soft_lemma_size                       3
% 7.29/1.50  --prop_impl_unit_size                   0
% 7.29/1.50  --prop_impl_unit                        []
% 7.29/1.50  --share_sel_clauses                     true
% 7.29/1.50  --reset_solvers                         false
% 7.29/1.50  --bc_imp_inh                            [conj_cone]
% 7.29/1.50  --conj_cone_tolerance                   3.
% 7.29/1.50  --extra_neg_conj                        none
% 7.29/1.50  --large_theory_mode                     true
% 7.29/1.50  --prolific_symb_bound                   200
% 7.29/1.50  --lt_threshold                          2000
% 7.29/1.50  --clause_weak_htbl                      true
% 7.29/1.50  --gc_record_bc_elim                     false
% 7.29/1.50  
% 7.29/1.50  ------ Preprocessing Options
% 7.29/1.50  
% 7.29/1.50  --preprocessing_flag                    true
% 7.29/1.50  --time_out_prep_mult                    0.1
% 7.29/1.50  --splitting_mode                        input
% 7.29/1.50  --splitting_grd                         true
% 7.29/1.50  --splitting_cvd                         false
% 7.29/1.50  --splitting_cvd_svl                     false
% 7.29/1.50  --splitting_nvd                         32
% 7.29/1.50  --sub_typing                            true
% 7.29/1.50  --prep_gs_sim                           true
% 7.29/1.50  --prep_unflatten                        true
% 7.29/1.50  --prep_res_sim                          true
% 7.29/1.50  --prep_upred                            true
% 7.29/1.50  --prep_sem_filter                       exhaustive
% 7.29/1.50  --prep_sem_filter_out                   false
% 7.29/1.50  --pred_elim                             true
% 7.29/1.50  --res_sim_input                         true
% 7.29/1.50  --eq_ax_congr_red                       true
% 7.29/1.50  --pure_diseq_elim                       true
% 7.29/1.50  --brand_transform                       false
% 7.29/1.50  --non_eq_to_eq                          false
% 7.29/1.50  --prep_def_merge                        true
% 7.29/1.50  --prep_def_merge_prop_impl              false
% 7.29/1.50  --prep_def_merge_mbd                    true
% 7.29/1.50  --prep_def_merge_tr_red                 false
% 7.29/1.50  --prep_def_merge_tr_cl                  false
% 7.29/1.50  --smt_preprocessing                     true
% 7.29/1.50  --smt_ac_axioms                         fast
% 7.29/1.50  --preprocessed_out                      false
% 7.29/1.50  --preprocessed_stats                    false
% 7.29/1.50  
% 7.29/1.50  ------ Abstraction refinement Options
% 7.29/1.50  
% 7.29/1.50  --abstr_ref                             []
% 7.29/1.50  --abstr_ref_prep                        false
% 7.29/1.50  --abstr_ref_until_sat                   false
% 7.29/1.50  --abstr_ref_sig_restrict                funpre
% 7.29/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.29/1.50  --abstr_ref_under                       []
% 7.29/1.50  
% 7.29/1.50  ------ SAT Options
% 7.29/1.50  
% 7.29/1.50  --sat_mode                              false
% 7.29/1.50  --sat_fm_restart_options                ""
% 7.29/1.50  --sat_gr_def                            false
% 7.29/1.50  --sat_epr_types                         true
% 7.29/1.50  --sat_non_cyclic_types                  false
% 7.29/1.50  --sat_finite_models                     false
% 7.29/1.50  --sat_fm_lemmas                         false
% 7.29/1.50  --sat_fm_prep                           false
% 7.29/1.50  --sat_fm_uc_incr                        true
% 7.29/1.50  --sat_out_model                         small
% 7.29/1.50  --sat_out_clauses                       false
% 7.29/1.50  
% 7.29/1.50  ------ QBF Options
% 7.29/1.50  
% 7.29/1.50  --qbf_mode                              false
% 7.29/1.50  --qbf_elim_univ                         false
% 7.29/1.50  --qbf_dom_inst                          none
% 7.29/1.50  --qbf_dom_pre_inst                      false
% 7.29/1.50  --qbf_sk_in                             false
% 7.29/1.50  --qbf_pred_elim                         true
% 7.29/1.50  --qbf_split                             512
% 7.29/1.50  
% 7.29/1.50  ------ BMC1 Options
% 7.29/1.50  
% 7.29/1.50  --bmc1_incremental                      false
% 7.29/1.50  --bmc1_axioms                           reachable_all
% 7.29/1.50  --bmc1_min_bound                        0
% 7.29/1.50  --bmc1_max_bound                        -1
% 7.29/1.50  --bmc1_max_bound_default                -1
% 7.29/1.50  --bmc1_symbol_reachability              true
% 7.29/1.50  --bmc1_property_lemmas                  false
% 7.29/1.50  --bmc1_k_induction                      false
% 7.29/1.50  --bmc1_non_equiv_states                 false
% 7.29/1.50  --bmc1_deadlock                         false
% 7.29/1.50  --bmc1_ucm                              false
% 7.29/1.50  --bmc1_add_unsat_core                   none
% 7.29/1.50  --bmc1_unsat_core_children              false
% 7.29/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.29/1.50  --bmc1_out_stat                         full
% 7.29/1.50  --bmc1_ground_init                      false
% 7.29/1.50  --bmc1_pre_inst_next_state              false
% 7.29/1.50  --bmc1_pre_inst_state                   false
% 7.29/1.50  --bmc1_pre_inst_reach_state             false
% 7.29/1.50  --bmc1_out_unsat_core                   false
% 7.29/1.50  --bmc1_aig_witness_out                  false
% 7.29/1.50  --bmc1_verbose                          false
% 7.29/1.50  --bmc1_dump_clauses_tptp                false
% 7.29/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.29/1.50  --bmc1_dump_file                        -
% 7.29/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.29/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.29/1.50  --bmc1_ucm_extend_mode                  1
% 7.29/1.50  --bmc1_ucm_init_mode                    2
% 7.29/1.50  --bmc1_ucm_cone_mode                    none
% 7.29/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.29/1.50  --bmc1_ucm_relax_model                  4
% 7.29/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.29/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.29/1.50  --bmc1_ucm_layered_model                none
% 7.29/1.50  --bmc1_ucm_max_lemma_size               10
% 7.29/1.50  
% 7.29/1.50  ------ AIG Options
% 7.29/1.50  
% 7.29/1.50  --aig_mode                              false
% 7.29/1.50  
% 7.29/1.50  ------ Instantiation Options
% 7.29/1.50  
% 7.29/1.50  --instantiation_flag                    true
% 7.29/1.50  --inst_sos_flag                         false
% 7.29/1.50  --inst_sos_phase                        true
% 7.29/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.29/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.29/1.50  --inst_lit_sel_side                     num_symb
% 7.29/1.50  --inst_solver_per_active                1400
% 7.29/1.50  --inst_solver_calls_frac                1.
% 7.29/1.50  --inst_passive_queue_type               priority_queues
% 7.29/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.29/1.50  --inst_passive_queues_freq              [25;2]
% 7.29/1.50  --inst_dismatching                      true
% 7.29/1.50  --inst_eager_unprocessed_to_passive     true
% 7.29/1.50  --inst_prop_sim_given                   true
% 7.29/1.50  --inst_prop_sim_new                     false
% 7.29/1.50  --inst_subs_new                         false
% 7.29/1.50  --inst_eq_res_simp                      false
% 7.29/1.50  --inst_subs_given                       false
% 7.29/1.50  --inst_orphan_elimination               true
% 7.29/1.50  --inst_learning_loop_flag               true
% 7.29/1.50  --inst_learning_start                   3000
% 7.29/1.50  --inst_learning_factor                  2
% 7.29/1.50  --inst_start_prop_sim_after_learn       3
% 7.29/1.50  --inst_sel_renew                        solver
% 7.29/1.50  --inst_lit_activity_flag                true
% 7.29/1.50  --inst_restr_to_given                   false
% 7.29/1.50  --inst_activity_threshold               500
% 7.29/1.50  --inst_out_proof                        true
% 7.29/1.50  
% 7.29/1.50  ------ Resolution Options
% 7.29/1.50  
% 7.29/1.50  --resolution_flag                       true
% 7.29/1.50  --res_lit_sel                           adaptive
% 7.29/1.50  --res_lit_sel_side                      none
% 7.29/1.50  --res_ordering                          kbo
% 7.29/1.50  --res_to_prop_solver                    active
% 7.29/1.50  --res_prop_simpl_new                    false
% 7.29/1.50  --res_prop_simpl_given                  true
% 7.29/1.50  --res_passive_queue_type                priority_queues
% 7.29/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.29/1.50  --res_passive_queues_freq               [15;5]
% 7.29/1.50  --res_forward_subs                      full
% 7.29/1.50  --res_backward_subs                     full
% 7.29/1.50  --res_forward_subs_resolution           true
% 7.29/1.50  --res_backward_subs_resolution          true
% 7.29/1.50  --res_orphan_elimination                true
% 7.29/1.50  --res_time_limit                        2.
% 7.29/1.50  --res_out_proof                         true
% 7.29/1.50  
% 7.29/1.50  ------ Superposition Options
% 7.29/1.50  
% 7.29/1.50  --superposition_flag                    true
% 7.29/1.50  --sup_passive_queue_type                priority_queues
% 7.29/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.29/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.29/1.50  --demod_completeness_check              fast
% 7.29/1.50  --demod_use_ground                      true
% 7.29/1.50  --sup_to_prop_solver                    passive
% 7.29/1.50  --sup_prop_simpl_new                    true
% 7.29/1.50  --sup_prop_simpl_given                  true
% 7.29/1.50  --sup_fun_splitting                     false
% 7.29/1.50  --sup_smt_interval                      50000
% 7.29/1.50  
% 7.29/1.50  ------ Superposition Simplification Setup
% 7.29/1.50  
% 7.29/1.50  --sup_indices_passive                   []
% 7.29/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.29/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.50  --sup_full_bw                           [BwDemod]
% 7.29/1.50  --sup_immed_triv                        [TrivRules]
% 7.29/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.29/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.50  --sup_immed_bw_main                     []
% 7.29/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.29/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.29/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.29/1.50  
% 7.29/1.50  ------ Combination Options
% 7.29/1.50  
% 7.29/1.50  --comb_res_mult                         3
% 7.29/1.50  --comb_sup_mult                         2
% 7.29/1.50  --comb_inst_mult                        10
% 7.29/1.50  
% 7.29/1.50  ------ Debug Options
% 7.29/1.50  
% 7.29/1.50  --dbg_backtrace                         false
% 7.29/1.50  --dbg_dump_prop_clauses                 false
% 7.29/1.50  --dbg_dump_prop_clauses_file            -
% 7.29/1.50  --dbg_out_stat                          false
% 7.29/1.50  ------ Parsing...
% 7.29/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.29/1.50  
% 7.29/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.29/1.50  
% 7.29/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.29/1.50  
% 7.29/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.29/1.50  ------ Proving...
% 7.29/1.50  ------ Problem Properties 
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  clauses                                 26
% 7.29/1.50  conjectures                             4
% 7.29/1.50  EPR                                     8
% 7.29/1.50  Horn                                    23
% 7.29/1.50  unary                                   8
% 7.29/1.50  binary                                  7
% 7.29/1.50  lits                                    56
% 7.29/1.50  lits eq                                 7
% 7.29/1.50  fd_pure                                 0
% 7.29/1.50  fd_pseudo                               0
% 7.29/1.50  fd_cond                                 0
% 7.29/1.50  fd_pseudo_cond                          4
% 7.29/1.50  AC symbols                              0
% 7.29/1.50  
% 7.29/1.50  ------ Schedule dynamic 5 is on 
% 7.29/1.50  
% 7.29/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  ------ 
% 7.29/1.50  Current options:
% 7.29/1.50  ------ 
% 7.29/1.50  
% 7.29/1.50  ------ Input Options
% 7.29/1.50  
% 7.29/1.50  --out_options                           all
% 7.29/1.50  --tptp_safe_out                         true
% 7.29/1.50  --problem_path                          ""
% 7.29/1.50  --include_path                          ""
% 7.29/1.50  --clausifier                            res/vclausify_rel
% 7.29/1.50  --clausifier_options                    --mode clausify
% 7.29/1.50  --stdin                                 false
% 7.29/1.50  --stats_out                             all
% 7.29/1.50  
% 7.29/1.50  ------ General Options
% 7.29/1.50  
% 7.29/1.50  --fof                                   false
% 7.29/1.50  --time_out_real                         305.
% 7.29/1.50  --time_out_virtual                      -1.
% 7.29/1.50  --symbol_type_check                     false
% 7.29/1.50  --clausify_out                          false
% 7.29/1.50  --sig_cnt_out                           false
% 7.29/1.50  --trig_cnt_out                          false
% 7.29/1.50  --trig_cnt_out_tolerance                1.
% 7.29/1.50  --trig_cnt_out_sk_spl                   false
% 7.29/1.50  --abstr_cl_out                          false
% 7.29/1.50  
% 7.29/1.50  ------ Global Options
% 7.29/1.50  
% 7.29/1.50  --schedule                              default
% 7.29/1.50  --add_important_lit                     false
% 7.29/1.50  --prop_solver_per_cl                    1000
% 7.29/1.50  --min_unsat_core                        false
% 7.29/1.50  --soft_assumptions                      false
% 7.29/1.50  --soft_lemma_size                       3
% 7.29/1.50  --prop_impl_unit_size                   0
% 7.29/1.50  --prop_impl_unit                        []
% 7.29/1.50  --share_sel_clauses                     true
% 7.29/1.50  --reset_solvers                         false
% 7.29/1.50  --bc_imp_inh                            [conj_cone]
% 7.29/1.50  --conj_cone_tolerance                   3.
% 7.29/1.50  --extra_neg_conj                        none
% 7.29/1.50  --large_theory_mode                     true
% 7.29/1.50  --prolific_symb_bound                   200
% 7.29/1.50  --lt_threshold                          2000
% 7.29/1.50  --clause_weak_htbl                      true
% 7.29/1.50  --gc_record_bc_elim                     false
% 7.29/1.50  
% 7.29/1.50  ------ Preprocessing Options
% 7.29/1.50  
% 7.29/1.50  --preprocessing_flag                    true
% 7.29/1.50  --time_out_prep_mult                    0.1
% 7.29/1.50  --splitting_mode                        input
% 7.29/1.50  --splitting_grd                         true
% 7.29/1.50  --splitting_cvd                         false
% 7.29/1.50  --splitting_cvd_svl                     false
% 7.29/1.50  --splitting_nvd                         32
% 7.29/1.50  --sub_typing                            true
% 7.29/1.50  --prep_gs_sim                           true
% 7.29/1.50  --prep_unflatten                        true
% 7.29/1.50  --prep_res_sim                          true
% 7.29/1.50  --prep_upred                            true
% 7.29/1.50  --prep_sem_filter                       exhaustive
% 7.29/1.50  --prep_sem_filter_out                   false
% 7.29/1.50  --pred_elim                             true
% 7.29/1.50  --res_sim_input                         true
% 7.29/1.50  --eq_ax_congr_red                       true
% 7.29/1.50  --pure_diseq_elim                       true
% 7.29/1.50  --brand_transform                       false
% 7.29/1.50  --non_eq_to_eq                          false
% 7.29/1.50  --prep_def_merge                        true
% 7.29/1.50  --prep_def_merge_prop_impl              false
% 7.29/1.50  --prep_def_merge_mbd                    true
% 7.29/1.50  --prep_def_merge_tr_red                 false
% 7.29/1.50  --prep_def_merge_tr_cl                  false
% 7.29/1.50  --smt_preprocessing                     true
% 7.29/1.50  --smt_ac_axioms                         fast
% 7.29/1.50  --preprocessed_out                      false
% 7.29/1.50  --preprocessed_stats                    false
% 7.29/1.50  
% 7.29/1.50  ------ Abstraction refinement Options
% 7.29/1.50  
% 7.29/1.50  --abstr_ref                             []
% 7.29/1.50  --abstr_ref_prep                        false
% 7.29/1.50  --abstr_ref_until_sat                   false
% 7.29/1.50  --abstr_ref_sig_restrict                funpre
% 7.29/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.29/1.50  --abstr_ref_under                       []
% 7.29/1.50  
% 7.29/1.50  ------ SAT Options
% 7.29/1.50  
% 7.29/1.50  --sat_mode                              false
% 7.29/1.50  --sat_fm_restart_options                ""
% 7.29/1.50  --sat_gr_def                            false
% 7.29/1.50  --sat_epr_types                         true
% 7.29/1.50  --sat_non_cyclic_types                  false
% 7.29/1.50  --sat_finite_models                     false
% 7.29/1.50  --sat_fm_lemmas                         false
% 7.29/1.50  --sat_fm_prep                           false
% 7.29/1.50  --sat_fm_uc_incr                        true
% 7.29/1.50  --sat_out_model                         small
% 7.29/1.50  --sat_out_clauses                       false
% 7.29/1.50  
% 7.29/1.50  ------ QBF Options
% 7.29/1.50  
% 7.29/1.50  --qbf_mode                              false
% 7.29/1.50  --qbf_elim_univ                         false
% 7.29/1.50  --qbf_dom_inst                          none
% 7.29/1.50  --qbf_dom_pre_inst                      false
% 7.29/1.50  --qbf_sk_in                             false
% 7.29/1.50  --qbf_pred_elim                         true
% 7.29/1.50  --qbf_split                             512
% 7.29/1.50  
% 7.29/1.50  ------ BMC1 Options
% 7.29/1.50  
% 7.29/1.50  --bmc1_incremental                      false
% 7.29/1.50  --bmc1_axioms                           reachable_all
% 7.29/1.50  --bmc1_min_bound                        0
% 7.29/1.50  --bmc1_max_bound                        -1
% 7.29/1.50  --bmc1_max_bound_default                -1
% 7.29/1.50  --bmc1_symbol_reachability              true
% 7.29/1.50  --bmc1_property_lemmas                  false
% 7.29/1.50  --bmc1_k_induction                      false
% 7.29/1.50  --bmc1_non_equiv_states                 false
% 7.29/1.50  --bmc1_deadlock                         false
% 7.29/1.50  --bmc1_ucm                              false
% 7.29/1.50  --bmc1_add_unsat_core                   none
% 7.29/1.50  --bmc1_unsat_core_children              false
% 7.29/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.29/1.50  --bmc1_out_stat                         full
% 7.29/1.50  --bmc1_ground_init                      false
% 7.29/1.50  --bmc1_pre_inst_next_state              false
% 7.29/1.50  --bmc1_pre_inst_state                   false
% 7.29/1.50  --bmc1_pre_inst_reach_state             false
% 7.29/1.50  --bmc1_out_unsat_core                   false
% 7.29/1.50  --bmc1_aig_witness_out                  false
% 7.29/1.50  --bmc1_verbose                          false
% 7.29/1.50  --bmc1_dump_clauses_tptp                false
% 7.29/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.29/1.50  --bmc1_dump_file                        -
% 7.29/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.29/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.29/1.50  --bmc1_ucm_extend_mode                  1
% 7.29/1.50  --bmc1_ucm_init_mode                    2
% 7.29/1.50  --bmc1_ucm_cone_mode                    none
% 7.29/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.29/1.50  --bmc1_ucm_relax_model                  4
% 7.29/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.29/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.29/1.50  --bmc1_ucm_layered_model                none
% 7.29/1.50  --bmc1_ucm_max_lemma_size               10
% 7.29/1.50  
% 7.29/1.50  ------ AIG Options
% 7.29/1.50  
% 7.29/1.50  --aig_mode                              false
% 7.29/1.50  
% 7.29/1.50  ------ Instantiation Options
% 7.29/1.50  
% 7.29/1.50  --instantiation_flag                    true
% 7.29/1.50  --inst_sos_flag                         false
% 7.29/1.50  --inst_sos_phase                        true
% 7.29/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.29/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.29/1.50  --inst_lit_sel_side                     none
% 7.29/1.50  --inst_solver_per_active                1400
% 7.29/1.50  --inst_solver_calls_frac                1.
% 7.29/1.50  --inst_passive_queue_type               priority_queues
% 7.29/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.29/1.50  --inst_passive_queues_freq              [25;2]
% 7.29/1.50  --inst_dismatching                      true
% 7.29/1.50  --inst_eager_unprocessed_to_passive     true
% 7.29/1.50  --inst_prop_sim_given                   true
% 7.29/1.50  --inst_prop_sim_new                     false
% 7.29/1.50  --inst_subs_new                         false
% 7.29/1.50  --inst_eq_res_simp                      false
% 7.29/1.50  --inst_subs_given                       false
% 7.29/1.50  --inst_orphan_elimination               true
% 7.29/1.50  --inst_learning_loop_flag               true
% 7.29/1.50  --inst_learning_start                   3000
% 7.29/1.50  --inst_learning_factor                  2
% 7.29/1.50  --inst_start_prop_sim_after_learn       3
% 7.29/1.50  --inst_sel_renew                        solver
% 7.29/1.50  --inst_lit_activity_flag                true
% 7.29/1.50  --inst_restr_to_given                   false
% 7.29/1.50  --inst_activity_threshold               500
% 7.29/1.50  --inst_out_proof                        true
% 7.29/1.50  
% 7.29/1.50  ------ Resolution Options
% 7.29/1.50  
% 7.29/1.50  --resolution_flag                       false
% 7.29/1.50  --res_lit_sel                           adaptive
% 7.29/1.50  --res_lit_sel_side                      none
% 7.29/1.50  --res_ordering                          kbo
% 7.29/1.50  --res_to_prop_solver                    active
% 7.29/1.50  --res_prop_simpl_new                    false
% 7.29/1.50  --res_prop_simpl_given                  true
% 7.29/1.50  --res_passive_queue_type                priority_queues
% 7.29/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.29/1.50  --res_passive_queues_freq               [15;5]
% 7.29/1.50  --res_forward_subs                      full
% 7.29/1.50  --res_backward_subs                     full
% 7.29/1.50  --res_forward_subs_resolution           true
% 7.29/1.50  --res_backward_subs_resolution          true
% 7.29/1.50  --res_orphan_elimination                true
% 7.29/1.50  --res_time_limit                        2.
% 7.29/1.50  --res_out_proof                         true
% 7.29/1.50  
% 7.29/1.50  ------ Superposition Options
% 7.29/1.50  
% 7.29/1.50  --superposition_flag                    true
% 7.29/1.50  --sup_passive_queue_type                priority_queues
% 7.29/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.29/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.29/1.50  --demod_completeness_check              fast
% 7.29/1.50  --demod_use_ground                      true
% 7.29/1.50  --sup_to_prop_solver                    passive
% 7.29/1.50  --sup_prop_simpl_new                    true
% 7.29/1.50  --sup_prop_simpl_given                  true
% 7.29/1.50  --sup_fun_splitting                     false
% 7.29/1.50  --sup_smt_interval                      50000
% 7.29/1.50  
% 7.29/1.50  ------ Superposition Simplification Setup
% 7.29/1.50  
% 7.29/1.50  --sup_indices_passive                   []
% 7.29/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.29/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.50  --sup_full_bw                           [BwDemod]
% 7.29/1.50  --sup_immed_triv                        [TrivRules]
% 7.29/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.29/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.50  --sup_immed_bw_main                     []
% 7.29/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.29/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.29/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.29/1.50  
% 7.29/1.50  ------ Combination Options
% 7.29/1.50  
% 7.29/1.50  --comb_res_mult                         3
% 7.29/1.50  --comb_sup_mult                         2
% 7.29/1.50  --comb_inst_mult                        10
% 7.29/1.50  
% 7.29/1.50  ------ Debug Options
% 7.29/1.50  
% 7.29/1.50  --dbg_backtrace                         false
% 7.29/1.50  --dbg_dump_prop_clauses                 false
% 7.29/1.50  --dbg_dump_prop_clauses_file            -
% 7.29/1.50  --dbg_out_stat                          false
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  ------ Proving...
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  % SZS status Theorem for theBenchmark.p
% 7.29/1.50  
% 7.29/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.29/1.50  
% 7.29/1.50  fof(f15,axiom,(
% 7.29/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.29/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f27,plain,(
% 7.29/1.50    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.29/1.50    inference(ennf_transformation,[],[f15])).
% 7.29/1.50  
% 7.29/1.50  fof(f28,plain,(
% 7.29/1.50    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.29/1.50    inference(flattening,[],[f27])).
% 7.29/1.50  
% 7.29/1.50  fof(f70,plain,(
% 7.29/1.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f28])).
% 7.29/1.50  
% 7.29/1.50  fof(f13,axiom,(
% 7.29/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.29/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f25,plain,(
% 7.29/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.29/1.50    inference(ennf_transformation,[],[f13])).
% 7.29/1.50  
% 7.29/1.50  fof(f68,plain,(
% 7.29/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f25])).
% 7.29/1.50  
% 7.29/1.50  fof(f12,axiom,(
% 7.29/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.29/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f42,plain,(
% 7.29/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.29/1.50    inference(nnf_transformation,[],[f12])).
% 7.29/1.50  
% 7.29/1.50  fof(f67,plain,(
% 7.29/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f42])).
% 7.29/1.50  
% 7.29/1.50  fof(f6,axiom,(
% 7.29/1.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.29/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f60,plain,(
% 7.29/1.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f6])).
% 7.29/1.50  
% 7.29/1.50  fof(f5,axiom,(
% 7.29/1.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.29/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f20,plain,(
% 7.29/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.29/1.50    inference(ennf_transformation,[],[f5])).
% 7.29/1.50  
% 7.29/1.50  fof(f21,plain,(
% 7.29/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.29/1.50    inference(flattening,[],[f20])).
% 7.29/1.50  
% 7.29/1.50  fof(f59,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f21])).
% 7.29/1.50  
% 7.29/1.50  fof(f16,conjecture,(
% 7.29/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 7.29/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f17,negated_conjecture,(
% 7.29/1.50    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 7.29/1.50    inference(negated_conjecture,[],[f16])).
% 7.29/1.50  
% 7.29/1.50  fof(f29,plain,(
% 7.29/1.50    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.29/1.50    inference(ennf_transformation,[],[f17])).
% 7.29/1.50  
% 7.29/1.50  fof(f30,plain,(
% 7.29/1.50    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.29/1.50    inference(flattening,[],[f29])).
% 7.29/1.50  
% 7.29/1.50  fof(f44,plain,(
% 7.29/1.50    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(X0),k3_relat_1(sK3)) & r1_tarski(X0,sK3) & v1_relat_1(sK3))) )),
% 7.29/1.50    introduced(choice_axiom,[])).
% 7.29/1.50  
% 7.29/1.50  fof(f43,plain,(
% 7.29/1.50    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK2),k3_relat_1(X1)) & r1_tarski(sK2,X1) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 7.29/1.50    introduced(choice_axiom,[])).
% 7.29/1.50  
% 7.29/1.50  fof(f45,plain,(
% 7.29/1.50    (~r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 7.29/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f44,f43])).
% 7.29/1.50  
% 7.29/1.50  fof(f73,plain,(
% 7.29/1.50    v1_relat_1(sK3)),
% 7.29/1.50    inference(cnf_transformation,[],[f45])).
% 7.29/1.50  
% 7.29/1.50  fof(f14,axiom,(
% 7.29/1.50    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 7.29/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f26,plain,(
% 7.29/1.50    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 7.29/1.50    inference(ennf_transformation,[],[f14])).
% 7.29/1.50  
% 7.29/1.50  fof(f69,plain,(
% 7.29/1.50    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f26])).
% 7.29/1.50  
% 7.29/1.50  fof(f11,axiom,(
% 7.29/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.29/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f65,plain,(
% 7.29/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.29/1.50    inference(cnf_transformation,[],[f11])).
% 7.29/1.50  
% 7.29/1.50  fof(f80,plain,(
% 7.29/1.50    ( ! [X0] : (k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.29/1.50    inference(definition_unfolding,[],[f69,f65])).
% 7.29/1.50  
% 7.29/1.50  fof(f10,axiom,(
% 7.29/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.29/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f64,plain,(
% 7.29/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f10])).
% 7.29/1.50  
% 7.29/1.50  fof(f7,axiom,(
% 7.29/1.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.29/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f22,plain,(
% 7.29/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.29/1.50    inference(ennf_transformation,[],[f7])).
% 7.29/1.50  
% 7.29/1.50  fof(f61,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f22])).
% 7.29/1.50  
% 7.29/1.50  fof(f77,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.29/1.50    inference(definition_unfolding,[],[f61,f65])).
% 7.29/1.50  
% 7.29/1.50  fof(f8,axiom,(
% 7.29/1.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.29/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f62,plain,(
% 7.29/1.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.29/1.50    inference(cnf_transformation,[],[f8])).
% 7.29/1.50  
% 7.29/1.50  fof(f78,plain,(
% 7.29/1.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 7.29/1.50    inference(definition_unfolding,[],[f62,f65])).
% 7.29/1.50  
% 7.29/1.50  fof(f74,plain,(
% 7.29/1.50    r1_tarski(sK2,sK3)),
% 7.29/1.50    inference(cnf_transformation,[],[f45])).
% 7.29/1.50  
% 7.29/1.50  fof(f71,plain,(
% 7.29/1.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f28])).
% 7.29/1.50  
% 7.29/1.50  fof(f4,axiom,(
% 7.29/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.29/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f19,plain,(
% 7.29/1.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.29/1.50    inference(ennf_transformation,[],[f4])).
% 7.29/1.50  
% 7.29/1.50  fof(f58,plain,(
% 7.29/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f19])).
% 7.29/1.50  
% 7.29/1.50  fof(f76,plain,(
% 7.29/1.50    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 7.29/1.50    inference(definition_unfolding,[],[f58,f65])).
% 7.29/1.50  
% 7.29/1.50  fof(f9,axiom,(
% 7.29/1.50    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.29/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f23,plain,(
% 7.29/1.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.29/1.50    inference(ennf_transformation,[],[f9])).
% 7.29/1.50  
% 7.29/1.50  fof(f24,plain,(
% 7.29/1.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.29/1.50    inference(flattening,[],[f23])).
% 7.29/1.50  
% 7.29/1.50  fof(f63,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f24])).
% 7.29/1.50  
% 7.29/1.50  fof(f79,plain,(
% 7.29/1.50    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.29/1.50    inference(definition_unfolding,[],[f63,f65])).
% 7.29/1.50  
% 7.29/1.50  fof(f3,axiom,(
% 7.29/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.29/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.50  
% 7.29/1.50  fof(f40,plain,(
% 7.29/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.29/1.50    inference(nnf_transformation,[],[f3])).
% 7.29/1.50  
% 7.29/1.50  fof(f41,plain,(
% 7.29/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.29/1.50    inference(flattening,[],[f40])).
% 7.29/1.50  
% 7.29/1.50  fof(f57,plain,(
% 7.29/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.29/1.50    inference(cnf_transformation,[],[f41])).
% 7.29/1.50  
% 7.29/1.50  fof(f55,plain,(
% 7.29/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.29/1.50    inference(cnf_transformation,[],[f41])).
% 7.29/1.50  
% 7.29/1.50  fof(f85,plain,(
% 7.29/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.29/1.50    inference(equality_resolution,[],[f55])).
% 7.29/1.50  
% 7.29/1.50  fof(f75,plain,(
% 7.29/1.50    ~r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))),
% 7.29/1.50    inference(cnf_transformation,[],[f45])).
% 7.29/1.50  
% 7.29/1.50  fof(f72,plain,(
% 7.29/1.50    v1_relat_1(sK2)),
% 7.29/1.50    inference(cnf_transformation,[],[f45])).
% 7.29/1.50  
% 7.29/1.50  cnf(c_24,plain,
% 7.29/1.50      ( ~ r1_tarski(X0,X1)
% 7.29/1.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.29/1.50      | ~ v1_relat_1(X0)
% 7.29/1.50      | ~ v1_relat_1(X1) ),
% 7.29/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_21,plain,
% 7.29/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.29/1.50      | ~ v1_relat_1(X1)
% 7.29/1.50      | v1_relat_1(X0) ),
% 7.29/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_19,plain,
% 7.29/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.29/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_149,plain,
% 7.29/1.50      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.29/1.50      | ~ r1_tarski(X0,X1)
% 7.29/1.50      | ~ v1_relat_1(X1) ),
% 7.29/1.50      inference(global_propositional_subsumption,
% 7.29/1.50                [status(thm)],
% 7.29/1.50                [c_24,c_21,c_19]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_150,plain,
% 7.29/1.50      ( ~ r1_tarski(X0,X1)
% 7.29/1.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.29/1.50      | ~ v1_relat_1(X1) ),
% 7.29/1.50      inference(renaming,[status(thm)],[c_149]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_945,plain,
% 7.29/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.29/1.50      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 7.29/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_150]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_14,plain,
% 7.29/1.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.29/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_954,plain,
% 7.29/1.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_13,plain,
% 7.29/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.29/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_955,plain,
% 7.29/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.29/1.50      | r1_tarski(X1,X2) != iProver_top
% 7.29/1.50      | r1_tarski(X0,X2) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_4066,plain,
% 7.29/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.29/1.50      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_954,c_955]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_27,negated_conjecture,
% 7.29/1.50      ( v1_relat_1(sK3) ),
% 7.29/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_947,plain,
% 7.29/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_22,plain,
% 7.29/1.50      ( ~ v1_relat_1(X0)
% 7.29/1.50      | k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 7.29/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_950,plain,
% 7.29/1.50      ( k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 7.29/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_2738,plain,
% 7.29/1.50      ( k3_tarski(k2_tarski(k1_relat_1(sK3),k2_relat_1(sK3))) = k3_relat_1(sK3) ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_947,c_950]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_18,plain,
% 7.29/1.50      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 7.29/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_15,plain,
% 7.29/1.50      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 7.29/1.50      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.29/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_953,plain,
% 7.29/1.50      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
% 7.29/1.50      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_3669,plain,
% 7.29/1.50      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
% 7.29/1.50      | r1_tarski(k4_xboole_0(X0,X2),X1) != iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_18,c_953]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_3895,plain,
% 7.29/1.50      ( r1_tarski(X0,k3_relat_1(sK3)) = iProver_top
% 7.29/1.50      | r1_tarski(k4_xboole_0(X0,k2_relat_1(sK3)),k1_relat_1(sK3)) != iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_2738,c_3669]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_19336,plain,
% 7.29/1.50      ( r1_tarski(X0,k3_relat_1(sK3)) = iProver_top
% 7.29/1.50      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_4066,c_3895]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_33209,plain,
% 7.29/1.50      ( r1_tarski(X0,sK3) != iProver_top
% 7.29/1.50      | r1_tarski(k1_relat_1(X0),k3_relat_1(sK3)) = iProver_top
% 7.29/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_945,c_19336]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_33245,plain,
% 7.29/1.50      ( r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) = iProver_top
% 7.29/1.50      | r1_tarski(sK2,sK3) != iProver_top
% 7.29/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_33209]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_16,plain,
% 7.29/1.50      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 7.29/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_952,plain,
% 7.29/1.50      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_1237,plain,
% 7.29/1.50      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_18,c_952]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_3064,plain,
% 7.29/1.50      ( r1_tarski(k2_relat_1(sK3),k3_relat_1(sK3)) = iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_2738,c_1237]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_26,negated_conjecture,
% 7.29/1.50      ( r1_tarski(sK2,sK3) ),
% 7.29/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_948,plain,
% 7.29/1.50      ( r1_tarski(sK2,sK3) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_23,plain,
% 7.29/1.50      ( ~ r1_tarski(X0,X1)
% 7.29/1.50      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.29/1.50      | ~ v1_relat_1(X0)
% 7.29/1.50      | ~ v1_relat_1(X1) ),
% 7.29/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_154,plain,
% 7.29/1.50      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.29/1.50      | ~ r1_tarski(X0,X1)
% 7.29/1.50      | ~ v1_relat_1(X1) ),
% 7.29/1.50      inference(global_propositional_subsumption,
% 7.29/1.50                [status(thm)],
% 7.29/1.50                [c_23,c_21,c_19]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_155,plain,
% 7.29/1.50      ( ~ r1_tarski(X0,X1)
% 7.29/1.50      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 7.29/1.50      | ~ v1_relat_1(X1) ),
% 7.29/1.50      inference(renaming,[status(thm)],[c_154]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_944,plain,
% 7.29/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.29/1.50      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 7.29/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_155]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12,plain,
% 7.29/1.50      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1 ),
% 7.29/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_956,plain,
% 7.29/1.50      ( k3_tarski(k2_tarski(X0,X1)) = X1
% 7.29/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_2426,plain,
% 7.29/1.50      ( k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1))) = k2_relat_1(X1)
% 7.29/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.29/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_944,c_956]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12533,plain,
% 7.29/1.50      ( k3_tarski(k2_tarski(k2_relat_1(sK2),k2_relat_1(sK3))) = k2_relat_1(sK3)
% 7.29/1.50      | v1_relat_1(sK3) != iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_948,c_2426]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_30,plain,
% 7.29/1.50      ( v1_relat_1(sK3) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12993,plain,
% 7.29/1.50      ( k3_tarski(k2_tarski(k2_relat_1(sK2),k2_relat_1(sK3))) = k2_relat_1(sK3) ),
% 7.29/1.50      inference(global_propositional_subsumption,
% 7.29/1.50                [status(thm)],
% 7.29/1.50                [c_12533,c_30]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_13001,plain,
% 7.29/1.50      ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK3)) = iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_12993,c_952]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_13055,plain,
% 7.29/1.50      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 7.29/1.50      | r1_tarski(k2_relat_1(sK2),X0) = iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_13001,c_955]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_29965,plain,
% 7.29/1.50      ( r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3)) = iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_3064,c_13055]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_17,plain,
% 7.29/1.50      ( ~ r1_tarski(X0,X1)
% 7.29/1.50      | ~ r1_tarski(X2,X1)
% 7.29/1.50      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 7.29/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_1200,plain,
% 7.29/1.50      ( ~ r1_tarski(X0,k3_relat_1(sK3))
% 7.29/1.50      | ~ r1_tarski(X1,k3_relat_1(sK3))
% 7.29/1.50      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k3_relat_1(sK3)) ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_17]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_26013,plain,
% 7.29/1.50      ( ~ r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3))
% 7.29/1.50      | ~ r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3))
% 7.29/1.50      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_relat_1(sK3)) ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_1200]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_26014,plain,
% 7.29/1.50      ( r1_tarski(k2_relat_1(sK2),k3_relat_1(sK3)) != iProver_top
% 7.29/1.50      | r1_tarski(k1_relat_1(sK2),k3_relat_1(sK3)) != iProver_top
% 7.29/1.50      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_relat_1(sK3)) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_26013]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_527,plain,
% 7.29/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.29/1.50      theory(equality) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_1152,plain,
% 7.29/1.50      ( ~ r1_tarski(X0,X1)
% 7.29/1.50      | r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
% 7.29/1.50      | k3_relat_1(sK3) != X1
% 7.29/1.50      | k3_relat_1(sK2) != X0 ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_527]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_1226,plain,
% 7.29/1.50      ( ~ r1_tarski(X0,k3_relat_1(X1))
% 7.29/1.50      | r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
% 7.29/1.50      | k3_relat_1(sK3) != k3_relat_1(X1)
% 7.29/1.50      | k3_relat_1(sK2) != X0 ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_1152]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_8275,plain,
% 7.29/1.50      ( r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
% 7.29/1.50      | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_relat_1(X0))
% 7.29/1.50      | k3_relat_1(sK3) != k3_relat_1(X0)
% 7.29/1.50      | k3_relat_1(sK2) != k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_1226]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_13302,plain,
% 7.29/1.50      ( r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
% 7.29/1.50      | ~ r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_relat_1(sK3))
% 7.29/1.50      | k3_relat_1(sK3) != k3_relat_1(sK3)
% 7.29/1.50      | k3_relat_1(sK2) != k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_8275]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_13303,plain,
% 7.29/1.50      ( k3_relat_1(sK3) != k3_relat_1(sK3)
% 7.29/1.50      | k3_relat_1(sK2) != k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))
% 7.29/1.50      | r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) = iProver_top
% 7.29/1.50      | r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))),k3_relat_1(sK3)) != iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_13302]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_526,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_1549,plain,
% 7.29/1.50      ( X0 != X1 | k3_relat_1(sK2) != X1 | k3_relat_1(sK2) = X0 ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_526]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_2452,plain,
% 7.29/1.50      ( X0 != k3_relat_1(sK2)
% 7.29/1.50      | k3_relat_1(sK2) = X0
% 7.29/1.50      | k3_relat_1(sK2) != k3_relat_1(sK2) ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_1549]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_4325,plain,
% 7.29/1.50      ( k3_relat_1(sK2) != k3_relat_1(sK2)
% 7.29/1.50      | k3_relat_1(sK2) = k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2)))
% 7.29/1.50      | k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) != k3_relat_1(sK2) ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_2452]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_525,plain,( X0 = X0 ),theory(equality) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_1220,plain,
% 7.29/1.50      ( k3_relat_1(sK3) = k3_relat_1(sK3) ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_525]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_532,plain,
% 7.29/1.50      ( X0 != X1 | k3_relat_1(X0) = k3_relat_1(X1) ),
% 7.29/1.50      theory(equality) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_537,plain,
% 7.29/1.50      ( k3_relat_1(sK2) = k3_relat_1(sK2) | sK2 != sK2 ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_532]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_9,plain,
% 7.29/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.29/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_69,plain,
% 7.29/1.50      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_11,plain,
% 7.29/1.50      ( r1_tarski(X0,X0) ),
% 7.29/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_65,plain,
% 7.29/1.50      ( r1_tarski(sK2,sK2) ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_40,plain,
% 7.29/1.50      ( ~ v1_relat_1(sK2)
% 7.29/1.50      | k3_tarski(k2_tarski(k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
% 7.29/1.50      inference(instantiation,[status(thm)],[c_22]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_25,negated_conjecture,
% 7.29/1.50      ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) ),
% 7.29/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_32,plain,
% 7.29/1.50      ( r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) != iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_31,plain,
% 7.29/1.50      ( r1_tarski(sK2,sK3) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_28,negated_conjecture,
% 7.29/1.50      ( v1_relat_1(sK2) ),
% 7.29/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(contradiction,plain,
% 7.29/1.50      ( $false ),
% 7.29/1.50      inference(minisat,
% 7.29/1.50                [status(thm)],
% 7.29/1.50                [c_33245,c_29965,c_26014,c_13303,c_4325,c_1220,c_537,
% 7.29/1.50                 c_69,c_65,c_40,c_32,c_31,c_30,c_28]) ).
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.29/1.50  
% 7.29/1.50  ------                               Statistics
% 7.29/1.50  
% 7.29/1.50  ------ General
% 7.29/1.50  
% 7.29/1.50  abstr_ref_over_cycles:                  0
% 7.29/1.50  abstr_ref_under_cycles:                 0
% 7.29/1.50  gc_basic_clause_elim:                   0
% 7.29/1.50  forced_gc_time:                         0
% 7.29/1.50  parsing_time:                           0.009
% 7.29/1.50  unif_index_cands_time:                  0.
% 7.29/1.50  unif_index_add_time:                    0.
% 7.29/1.50  orderings_time:                         0.
% 7.29/1.50  out_proof_time:                         0.01
% 7.29/1.50  total_time:                             0.847
% 7.29/1.50  num_of_symbols:                         47
% 7.29/1.50  num_of_terms:                           34528
% 7.29/1.50  
% 7.29/1.50  ------ Preprocessing
% 7.29/1.50  
% 7.29/1.50  num_of_splits:                          0
% 7.29/1.50  num_of_split_atoms:                     0
% 7.29/1.50  num_of_reused_defs:                     0
% 7.29/1.50  num_eq_ax_congr_red:                    35
% 7.29/1.50  num_of_sem_filtered_clauses:            1
% 7.29/1.50  num_of_subtypes:                        0
% 7.29/1.50  monotx_restored_types:                  0
% 7.29/1.50  sat_num_of_epr_types:                   0
% 7.29/1.50  sat_num_of_non_cyclic_types:            0
% 7.29/1.50  sat_guarded_non_collapsed_types:        0
% 7.29/1.50  num_pure_diseq_elim:                    0
% 7.29/1.50  simp_replaced_by:                       0
% 7.29/1.50  res_preprocessed:                       123
% 7.29/1.50  prep_upred:                             0
% 7.29/1.50  prep_unflattend:                        0
% 7.29/1.50  smt_new_axioms:                         0
% 7.29/1.50  pred_elim_cands:                        3
% 7.29/1.50  pred_elim:                              1
% 7.29/1.50  pred_elim_cl:                           2
% 7.29/1.50  pred_elim_cycles:                       3
% 7.29/1.50  merged_defs:                            2
% 7.29/1.50  merged_defs_ncl:                        0
% 7.29/1.50  bin_hyper_res:                          3
% 7.29/1.50  prep_cycles:                            4
% 7.29/1.50  pred_elim_time:                         0.
% 7.29/1.50  splitting_time:                         0.
% 7.29/1.50  sem_filter_time:                        0.
% 7.29/1.50  monotx_time:                            0.
% 7.29/1.50  subtype_inf_time:                       0.
% 7.29/1.50  
% 7.29/1.50  ------ Problem properties
% 7.29/1.50  
% 7.29/1.50  clauses:                                26
% 7.29/1.50  conjectures:                            4
% 7.29/1.50  epr:                                    8
% 7.29/1.50  horn:                                   23
% 7.29/1.50  ground:                                 4
% 7.29/1.50  unary:                                  8
% 7.29/1.50  binary:                                 7
% 7.29/1.50  lits:                                   56
% 7.29/1.50  lits_eq:                                7
% 7.29/1.50  fd_pure:                                0
% 7.29/1.50  fd_pseudo:                              0
% 7.29/1.50  fd_cond:                                0
% 7.29/1.50  fd_pseudo_cond:                         4
% 7.29/1.50  ac_symbols:                             0
% 7.29/1.50  
% 7.29/1.50  ------ Propositional Solver
% 7.29/1.50  
% 7.29/1.50  prop_solver_calls:                      32
% 7.29/1.50  prop_fast_solver_calls:                 913
% 7.29/1.50  smt_solver_calls:                       0
% 7.29/1.50  smt_fast_solver_calls:                  0
% 7.29/1.50  prop_num_of_clauses:                    13414
% 7.29/1.50  prop_preprocess_simplified:             26005
% 7.29/1.50  prop_fo_subsumed:                       6
% 7.29/1.50  prop_solver_time:                       0.
% 7.29/1.50  smt_solver_time:                        0.
% 7.29/1.50  smt_fast_solver_time:                   0.
% 7.29/1.50  prop_fast_solver_time:                  0.
% 7.29/1.50  prop_unsat_core_time:                   0.001
% 7.29/1.50  
% 7.29/1.50  ------ QBF
% 7.29/1.50  
% 7.29/1.50  qbf_q_res:                              0
% 7.29/1.50  qbf_num_tautologies:                    0
% 7.29/1.50  qbf_prep_cycles:                        0
% 7.29/1.50  
% 7.29/1.50  ------ BMC1
% 7.29/1.50  
% 7.29/1.50  bmc1_current_bound:                     -1
% 7.29/1.50  bmc1_last_solved_bound:                 -1
% 7.29/1.50  bmc1_unsat_core_size:                   -1
% 7.29/1.50  bmc1_unsat_core_parents_size:           -1
% 7.29/1.50  bmc1_merge_next_fun:                    0
% 7.29/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.29/1.50  
% 7.29/1.50  ------ Instantiation
% 7.29/1.50  
% 7.29/1.50  inst_num_of_clauses:                    3246
% 7.29/1.50  inst_num_in_passive:                    1549
% 7.29/1.50  inst_num_in_active:                     830
% 7.29/1.50  inst_num_in_unprocessed:                867
% 7.29/1.50  inst_num_of_loops:                      1050
% 7.29/1.50  inst_num_of_learning_restarts:          0
% 7.29/1.50  inst_num_moves_active_passive:          217
% 7.29/1.50  inst_lit_activity:                      0
% 7.29/1.50  inst_lit_activity_moves:                1
% 7.29/1.50  inst_num_tautologies:                   0
% 7.29/1.50  inst_num_prop_implied:                  0
% 7.29/1.50  inst_num_existing_simplified:           0
% 7.29/1.50  inst_num_eq_res_simplified:             0
% 7.29/1.50  inst_num_child_elim:                    0
% 7.29/1.50  inst_num_of_dismatching_blockings:      2409
% 7.29/1.50  inst_num_of_non_proper_insts:           3450
% 7.29/1.50  inst_num_of_duplicates:                 0
% 7.29/1.50  inst_inst_num_from_inst_to_res:         0
% 7.29/1.50  inst_dismatching_checking_time:         0.
% 7.29/1.50  
% 7.29/1.50  ------ Resolution
% 7.29/1.50  
% 7.29/1.50  res_num_of_clauses:                     0
% 7.29/1.50  res_num_in_passive:                     0
% 7.29/1.50  res_num_in_active:                      0
% 7.29/1.50  res_num_of_loops:                       127
% 7.29/1.50  res_forward_subset_subsumed:            340
% 7.29/1.50  res_backward_subset_subsumed:           0
% 7.29/1.50  res_forward_subsumed:                   0
% 7.29/1.50  res_backward_subsumed:                  0
% 7.29/1.50  res_forward_subsumption_resolution:     0
% 7.29/1.50  res_backward_subsumption_resolution:    0
% 7.29/1.50  res_clause_to_clause_subsumption:       4753
% 7.29/1.50  res_orphan_elimination:                 0
% 7.29/1.50  res_tautology_del:                      218
% 7.29/1.50  res_num_eq_res_simplified:              0
% 7.29/1.50  res_num_sel_changes:                    0
% 7.29/1.50  res_moves_from_active_to_pass:          0
% 7.29/1.50  
% 7.29/1.50  ------ Superposition
% 7.29/1.50  
% 7.29/1.50  sup_time_total:                         0.
% 7.29/1.50  sup_time_generating:                    0.
% 7.29/1.50  sup_time_sim_full:                      0.
% 7.29/1.50  sup_time_sim_immed:                     0.
% 7.29/1.50  
% 7.29/1.50  sup_num_of_clauses:                     867
% 7.29/1.50  sup_num_in_active:                      197
% 7.29/1.50  sup_num_in_passive:                     670
% 7.29/1.50  sup_num_of_loops:                       208
% 7.29/1.50  sup_fw_superposition:                   933
% 7.29/1.50  sup_bw_superposition:                   1101
% 7.29/1.50  sup_immediate_simplified:               376
% 7.29/1.50  sup_given_eliminated:                   0
% 7.29/1.50  comparisons_done:                       0
% 7.29/1.50  comparisons_avoided:                    0
% 7.29/1.50  
% 7.29/1.50  ------ Simplifications
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  sim_fw_subset_subsumed:                 36
% 7.29/1.50  sim_bw_subset_subsumed:                 0
% 7.29/1.50  sim_fw_subsumed:                        101
% 7.29/1.50  sim_bw_subsumed:                        2
% 7.29/1.50  sim_fw_subsumption_res:                 2
% 7.29/1.50  sim_bw_subsumption_res:                 0
% 7.29/1.50  sim_tautology_del:                      94
% 7.29/1.50  sim_eq_tautology_del:                   35
% 7.29/1.50  sim_eq_res_simp:                        6
% 7.29/1.50  sim_fw_demodulated:                     31
% 7.29/1.50  sim_bw_demodulated:                     13
% 7.29/1.50  sim_light_normalised:                   215
% 7.29/1.50  sim_joinable_taut:                      0
% 7.29/1.50  sim_joinable_simp:                      0
% 7.29/1.50  sim_ac_normalised:                      0
% 7.29/1.50  sim_smt_subsumption:                    0
% 7.29/1.50  
%------------------------------------------------------------------------------
