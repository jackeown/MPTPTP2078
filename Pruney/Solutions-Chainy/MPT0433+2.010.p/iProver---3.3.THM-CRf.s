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
% DateTime   : Thu Dec  3 11:42:52 EST 2020

% Result     : Theorem 7.53s
% Output     : CNFRefutation 7.53s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 393 expanded)
%              Number of clauses        :   56 (  89 expanded)
%              Number of leaves         :   18 ( 110 expanded)
%              Depth                    :   15
%              Number of atoms          :  233 ( 661 expanded)
%              Number of equality atoms :   97 ( 331 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f51,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f29,f49,f49])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f50])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f27,f26])).

fof(f45,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f44,f50,f50])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f47,f49,f49])).

cnf(c_0,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_6,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_577,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_803,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_577])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_578,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1230,plain,
    ( k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1)) = X1 ),
    inference(superposition,[status(thm)],[c_803,c_578])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_570,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_571,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_95,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_96,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_95])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_96])).

cnf(c_569,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_119])).

cnf(c_1075,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_577,c_569])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_573,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2034,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(X2))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X2)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1075,c_573])).

cnf(c_8371,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),X1)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_571,c_2034])).

cnf(c_9856,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(sK0))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),sK0))) ),
    inference(superposition,[status(thm)],[c_570,c_8371])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_580,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_579,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1242,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_580,c_579])).

cnf(c_9894,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9856,c_1242])).

cnf(c_13261,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))),k1_relat_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_9894])).

cnf(c_1076,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_569])).

cnf(c_2035,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(X2))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X2)))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1076,c_573])).

cnf(c_10476,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),X1)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_571,c_2035])).

cnf(c_10836,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(sK1))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),sK1))) ),
    inference(superposition,[status(thm)],[c_571,c_10476])).

cnf(c_10851,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(sK1))) = k1_relat_1(sK1) ),
    inference(demodulation,[status(thm)],[c_10836,c_1230])).

cnf(c_12799,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10851,c_1242])).

cnf(c_12828,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_12799])).

cnf(c_253,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_770,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))
    | k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != X0
    | k1_relat_1(sK0) != X1 ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_1007,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK0))
    | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))
    | k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != X0
    | k1_relat_1(sK0) != k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_1417,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))),k1_relat_1(sK0))
    | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))
    | k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))
    | k1_relat_1(sK0) != k1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_1418,plain,
    ( k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))
    | k1_relat_1(sK0) != k1_relat_1(sK0)
    | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))),k1_relat_1(sK0)) != iProver_top
    | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1417])).

cnf(c_943,plain,
    ( k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)) = k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_257,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_794,plain,
    ( k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) = k1_relat_1(X0)
    | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)) != X0 ),
    inference(instantiation,[status(thm)],[c_257])).

cnf(c_942,plain,
    ( k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) = k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))
    | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)) != k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_728,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))
    | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_729,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) != iProver_top
    | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_264,plain,
    ( k1_relat_1(sK0) = k1_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_257])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_45,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_41,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_17,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13261,c_12828,c_1418,c_943,c_942,c_729,c_264,c_45,c_41,c_17])).

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
% 7.53/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.53/1.50  
% 7.53/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.53/1.50  
% 7.53/1.50  ------  iProver source info
% 7.53/1.50  
% 7.53/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.53/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.53/1.50  git: non_committed_changes: false
% 7.53/1.50  git: last_make_outside_of_git: false
% 7.53/1.50  
% 7.53/1.50  ------ 
% 7.53/1.50  ------ Parsing...
% 7.53/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.53/1.50  
% 7.53/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.53/1.50  
% 7.53/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.53/1.50  
% 7.53/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.53/1.50  ------ Proving...
% 7.53/1.50  ------ Problem Properties 
% 7.53/1.50  
% 7.53/1.50  
% 7.53/1.50  clauses                                 14
% 7.53/1.50  conjectures                             3
% 7.53/1.50  EPR                                     5
% 7.53/1.50  Horn                                    14
% 7.53/1.50  unary                                   6
% 7.53/1.50  binary                                  4
% 7.53/1.50  lits                                    26
% 7.53/1.50  lits eq                                 4
% 7.53/1.50  fd_pure                                 0
% 7.53/1.50  fd_pseudo                               0
% 7.53/1.50  fd_cond                                 0
% 7.53/1.50  fd_pseudo_cond                          1
% 7.53/1.50  AC symbols                              0
% 7.53/1.50  
% 7.53/1.50  ------ Input Options Time Limit: Unbounded
% 7.53/1.50  
% 7.53/1.50  
% 7.53/1.50  ------ 
% 7.53/1.50  Current options:
% 7.53/1.50  ------ 
% 7.53/1.50  
% 7.53/1.50  
% 7.53/1.50  
% 7.53/1.50  
% 7.53/1.50  ------ Proving...
% 7.53/1.50  
% 7.53/1.50  
% 7.53/1.50  % SZS status Theorem for theBenchmark.p
% 7.53/1.50  
% 7.53/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.53/1.50  
% 7.53/1.50  fof(f1,axiom,(
% 7.53/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.53/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.50  
% 7.53/1.50  fof(f29,plain,(
% 7.53/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.53/1.50    inference(cnf_transformation,[],[f1])).
% 7.53/1.50  
% 7.53/1.50  fof(f10,axiom,(
% 7.53/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.53/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.50  
% 7.53/1.50  fof(f40,plain,(
% 7.53/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.53/1.50    inference(cnf_transformation,[],[f10])).
% 7.53/1.50  
% 7.53/1.50  fof(f7,axiom,(
% 7.53/1.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.53/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.50  
% 7.53/1.50  fof(f37,plain,(
% 7.53/1.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.53/1.50    inference(cnf_transformation,[],[f7])).
% 7.53/1.50  
% 7.53/1.50  fof(f8,axiom,(
% 7.53/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.53/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.50  
% 7.53/1.50  fof(f38,plain,(
% 7.53/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.53/1.50    inference(cnf_transformation,[],[f8])).
% 7.53/1.50  
% 7.53/1.50  fof(f48,plain,(
% 7.53/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.53/1.50    inference(definition_unfolding,[],[f37,f38])).
% 7.53/1.50  
% 7.53/1.50  fof(f49,plain,(
% 7.53/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 7.53/1.50    inference(definition_unfolding,[],[f40,f48])).
% 7.53/1.50  
% 7.53/1.50  fof(f51,plain,(
% 7.53/1.50    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 7.53/1.50    inference(definition_unfolding,[],[f29,f49,f49])).
% 7.53/1.50  
% 7.53/1.50  fof(f5,axiom,(
% 7.53/1.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.53/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.50  
% 7.53/1.50  fof(f35,plain,(
% 7.53/1.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.53/1.50    inference(cnf_transformation,[],[f5])).
% 7.53/1.50  
% 7.53/1.50  fof(f54,plain,(
% 7.53/1.50    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 7.53/1.50    inference(definition_unfolding,[],[f35,f49])).
% 7.53/1.50  
% 7.53/1.50  fof(f4,axiom,(
% 7.53/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.53/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.50  
% 7.53/1.50  fof(f17,plain,(
% 7.53/1.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.53/1.50    inference(ennf_transformation,[],[f4])).
% 7.53/1.50  
% 7.53/1.50  fof(f34,plain,(
% 7.53/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.53/1.50    inference(cnf_transformation,[],[f17])).
% 7.53/1.50  
% 7.53/1.50  fof(f9,axiom,(
% 7.53/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.53/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.50  
% 7.53/1.50  fof(f39,plain,(
% 7.53/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.53/1.50    inference(cnf_transformation,[],[f9])).
% 7.53/1.50  
% 7.53/1.50  fof(f50,plain,(
% 7.53/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 7.53/1.50    inference(definition_unfolding,[],[f39,f48])).
% 7.53/1.50  
% 7.53/1.50  fof(f53,plain,(
% 7.53/1.50    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 7.53/1.50    inference(definition_unfolding,[],[f34,f50])).
% 7.53/1.50  
% 7.53/1.50  fof(f14,conjecture,(
% 7.53/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 7.53/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.50  
% 7.53/1.50  fof(f15,negated_conjecture,(
% 7.53/1.50    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 7.53/1.50    inference(negated_conjecture,[],[f14])).
% 7.53/1.50  
% 7.53/1.50  fof(f22,plain,(
% 7.53/1.50    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.53/1.50    inference(ennf_transformation,[],[f15])).
% 7.53/1.50  
% 7.53/1.50  fof(f27,plain,(
% 7.53/1.50    ( ! [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK1))) & v1_relat_1(sK1))) )),
% 7.53/1.50    introduced(choice_axiom,[])).
% 7.53/1.50  
% 7.53/1.50  fof(f26,plain,(
% 7.53/1.50    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 7.53/1.50    introduced(choice_axiom,[])).
% 7.53/1.50  
% 7.53/1.50  fof(f28,plain,(
% 7.53/1.50    (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 7.53/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f27,f26])).
% 7.53/1.50  
% 7.53/1.50  fof(f45,plain,(
% 7.53/1.50    v1_relat_1(sK0)),
% 7.53/1.50    inference(cnf_transformation,[],[f28])).
% 7.53/1.50  
% 7.53/1.50  fof(f46,plain,(
% 7.53/1.50    v1_relat_1(sK1)),
% 7.53/1.50    inference(cnf_transformation,[],[f28])).
% 7.53/1.50  
% 7.53/1.50  fof(f12,axiom,(
% 7.53/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.53/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.50  
% 7.53/1.50  fof(f20,plain,(
% 7.53/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.53/1.50    inference(ennf_transformation,[],[f12])).
% 7.53/1.50  
% 7.53/1.50  fof(f43,plain,(
% 7.53/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.53/1.50    inference(cnf_transformation,[],[f20])).
% 7.53/1.50  
% 7.53/1.50  fof(f11,axiom,(
% 7.53/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.53/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.50  
% 7.53/1.50  fof(f25,plain,(
% 7.53/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.53/1.50    inference(nnf_transformation,[],[f11])).
% 7.53/1.50  
% 7.53/1.50  fof(f42,plain,(
% 7.53/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.53/1.50    inference(cnf_transformation,[],[f25])).
% 7.53/1.50  
% 7.53/1.50  fof(f13,axiom,(
% 7.53/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 7.53/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.50  
% 7.53/1.50  fof(f21,plain,(
% 7.53/1.50    ! [X0] : (! [X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.53/1.50    inference(ennf_transformation,[],[f13])).
% 7.53/1.50  
% 7.53/1.50  fof(f44,plain,(
% 7.53/1.50    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.53/1.50    inference(cnf_transformation,[],[f21])).
% 7.53/1.50  
% 7.53/1.50  fof(f56,plain,(
% 7.53/1.50    ( ! [X0,X1] : (k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.53/1.50    inference(definition_unfolding,[],[f44,f50,f50])).
% 7.53/1.50  
% 7.53/1.50  fof(f2,axiom,(
% 7.53/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.53/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.50  
% 7.53/1.50  fof(f23,plain,(
% 7.53/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.53/1.50    inference(nnf_transformation,[],[f2])).
% 7.53/1.50  
% 7.53/1.50  fof(f24,plain,(
% 7.53/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.53/1.50    inference(flattening,[],[f23])).
% 7.53/1.50  
% 7.53/1.50  fof(f30,plain,(
% 7.53/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.53/1.50    inference(cnf_transformation,[],[f24])).
% 7.53/1.50  
% 7.53/1.50  fof(f59,plain,(
% 7.53/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.53/1.50    inference(equality_resolution,[],[f30])).
% 7.53/1.50  
% 7.53/1.50  fof(f3,axiom,(
% 7.53/1.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 7.53/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.50  
% 7.53/1.50  fof(f16,plain,(
% 7.53/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 7.53/1.50    inference(ennf_transformation,[],[f3])).
% 7.53/1.50  
% 7.53/1.50  fof(f33,plain,(
% 7.53/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 7.53/1.50    inference(cnf_transformation,[],[f16])).
% 7.53/1.50  
% 7.53/1.50  fof(f52,plain,(
% 7.53/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2)) )),
% 7.53/1.50    inference(definition_unfolding,[],[f33,f50])).
% 7.53/1.50  
% 7.53/1.50  fof(f6,axiom,(
% 7.53/1.50    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 7.53/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.53/1.50  
% 7.53/1.50  fof(f18,plain,(
% 7.53/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 7.53/1.50    inference(ennf_transformation,[],[f6])).
% 7.53/1.50  
% 7.53/1.50  fof(f19,plain,(
% 7.53/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 7.53/1.50    inference(flattening,[],[f18])).
% 7.53/1.50  
% 7.53/1.50  fof(f36,plain,(
% 7.53/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.53/1.50    inference(cnf_transformation,[],[f19])).
% 7.53/1.50  
% 7.53/1.50  fof(f55,plain,(
% 7.53/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 7.53/1.50    inference(definition_unfolding,[],[f36,f49])).
% 7.53/1.50  
% 7.53/1.50  fof(f32,plain,(
% 7.53/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.53/1.50    inference(cnf_transformation,[],[f24])).
% 7.53/1.50  
% 7.53/1.50  fof(f47,plain,(
% 7.53/1.50    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 7.53/1.50    inference(cnf_transformation,[],[f28])).
% 7.53/1.50  
% 7.53/1.50  fof(f57,plain,(
% 7.53/1.50    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))),
% 7.53/1.50    inference(definition_unfolding,[],[f47,f49,f49])).
% 7.53/1.50  
% 7.53/1.50  cnf(c_0,plain,
% 7.53/1.50      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
% 7.53/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_6,plain,
% 7.53/1.50      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
% 7.53/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_577,plain,
% 7.53/1.50      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
% 7.53/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_803,plain,
% 7.53/1.50      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
% 7.53/1.50      inference(superposition,[status(thm)],[c_0,c_577]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_5,plain,
% 7.53/1.50      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ),
% 7.53/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_578,plain,
% 7.53/1.50      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
% 7.53/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.53/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_1230,plain,
% 7.53/1.50      ( k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1)) = X1 ),
% 7.53/1.50      inference(superposition,[status(thm)],[c_803,c_578]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_14,negated_conjecture,
% 7.53/1.50      ( v1_relat_1(sK0) ),
% 7.53/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_570,plain,
% 7.53/1.50      ( v1_relat_1(sK0) = iProver_top ),
% 7.53/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_13,negated_conjecture,
% 7.53/1.50      ( v1_relat_1(sK1) ),
% 7.53/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_571,plain,
% 7.53/1.50      ( v1_relat_1(sK1) = iProver_top ),
% 7.53/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_10,plain,
% 7.53/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.53/1.50      | ~ v1_relat_1(X1)
% 7.53/1.50      | v1_relat_1(X0) ),
% 7.53/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_8,plain,
% 7.53/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.53/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_95,plain,
% 7.53/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.53/1.50      inference(prop_impl,[status(thm)],[c_8]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_96,plain,
% 7.53/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.53/1.50      inference(renaming,[status(thm)],[c_95]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_119,plain,
% 7.53/1.50      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.53/1.50      inference(bin_hyper_res,[status(thm)],[c_10,c_96]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_569,plain,
% 7.53/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.53/1.50      | v1_relat_1(X1) != iProver_top
% 7.53/1.50      | v1_relat_1(X0) = iProver_top ),
% 7.53/1.50      inference(predicate_to_equality,[status(thm)],[c_119]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_1075,plain,
% 7.53/1.50      ( v1_relat_1(X0) != iProver_top
% 7.53/1.50      | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 7.53/1.50      inference(superposition,[status(thm)],[c_577,c_569]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_11,plain,
% 7.53/1.50      ( ~ v1_relat_1(X0)
% 7.53/1.50      | ~ v1_relat_1(X1)
% 7.53/1.50      | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 7.53/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_573,plain,
% 7.53/1.50      ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
% 7.53/1.50      | v1_relat_1(X0) != iProver_top
% 7.53/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.53/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_2034,plain,
% 7.53/1.50      ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(X2))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X2)))
% 7.53/1.50      | v1_relat_1(X0) != iProver_top
% 7.53/1.50      | v1_relat_1(X2) != iProver_top ),
% 7.53/1.50      inference(superposition,[status(thm)],[c_1075,c_573]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_8371,plain,
% 7.53/1.50      ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),X1)))
% 7.53/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.53/1.50      inference(superposition,[status(thm)],[c_571,c_2034]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_9856,plain,
% 7.53/1.50      ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(sK0))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),sK0))) ),
% 7.53/1.50      inference(superposition,[status(thm)],[c_570,c_8371]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_3,plain,
% 7.53/1.50      ( r1_tarski(X0,X0) ),
% 7.53/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_580,plain,
% 7.53/1.50      ( r1_tarski(X0,X0) = iProver_top ),
% 7.53/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_4,plain,
% 7.53/1.50      ( r1_tarski(X0,X1)
% 7.53/1.50      | ~ r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) ),
% 7.53/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_579,plain,
% 7.53/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.53/1.50      | r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) != iProver_top ),
% 7.53/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_1242,plain,
% 7.53/1.50      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 7.53/1.50      inference(superposition,[status(thm)],[c_580,c_579]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_9894,plain,
% 7.53/1.50      ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0))),k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),sK0)))) = iProver_top ),
% 7.53/1.50      inference(superposition,[status(thm)],[c_9856,c_1242]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_13261,plain,
% 7.53/1.50      ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))),k1_relat_1(sK0)) = iProver_top ),
% 7.53/1.50      inference(superposition,[status(thm)],[c_1230,c_9894]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_1076,plain,
% 7.53/1.50      ( v1_relat_1(X0) != iProver_top
% 7.53/1.50      | v1_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = iProver_top ),
% 7.53/1.50      inference(superposition,[status(thm)],[c_803,c_569]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_2035,plain,
% 7.53/1.50      ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(X2))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X2)))
% 7.53/1.50      | v1_relat_1(X1) != iProver_top
% 7.53/1.50      | v1_relat_1(X2) != iProver_top ),
% 7.53/1.50      inference(superposition,[status(thm)],[c_1076,c_573]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_10476,plain,
% 7.53/1.50      ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(X1))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),X1)))
% 7.53/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.53/1.50      inference(superposition,[status(thm)],[c_571,c_2035]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_10836,plain,
% 7.53/1.50      ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(sK1))) = k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),k1_setfam_1(k2_enumset1(X0,X0,X0,sK1)),sK1))) ),
% 7.53/1.50      inference(superposition,[status(thm)],[c_571,c_10476]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_10851,plain,
% 7.53/1.50      ( k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(sK1))) = k1_relat_1(sK1) ),
% 7.53/1.50      inference(demodulation,[status(thm)],[c_10836,c_1230]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_12799,plain,
% 7.53/1.50      ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(sK1)) = iProver_top ),
% 7.53/1.50      inference(superposition,[status(thm)],[c_10851,c_1242]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_12828,plain,
% 7.53/1.50      ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) = iProver_top ),
% 7.53/1.50      inference(instantiation,[status(thm)],[c_12799]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_253,plain,
% 7.53/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.53/1.50      theory(equality) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_770,plain,
% 7.53/1.50      ( ~ r1_tarski(X0,X1)
% 7.53/1.50      | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))
% 7.53/1.50      | k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != X0
% 7.53/1.50      | k1_relat_1(sK0) != X1 ),
% 7.53/1.50      inference(instantiation,[status(thm)],[c_253]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_1007,plain,
% 7.53/1.50      ( ~ r1_tarski(X0,k1_relat_1(sK0))
% 7.53/1.50      | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))
% 7.53/1.50      | k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != X0
% 7.53/1.50      | k1_relat_1(sK0) != k1_relat_1(sK0) ),
% 7.53/1.50      inference(instantiation,[status(thm)],[c_770]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_1417,plain,
% 7.53/1.50      ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))),k1_relat_1(sK0))
% 7.53/1.50      | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))
% 7.53/1.50      | k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))
% 7.53/1.50      | k1_relat_1(sK0) != k1_relat_1(sK0) ),
% 7.53/1.50      inference(instantiation,[status(thm)],[c_1007]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_1418,plain,
% 7.53/1.50      ( k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))
% 7.53/1.50      | k1_relat_1(sK0) != k1_relat_1(sK0)
% 7.53/1.50      | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))),k1_relat_1(sK0)) != iProver_top
% 7.53/1.50      | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) = iProver_top ),
% 7.53/1.50      inference(predicate_to_equality,[status(thm)],[c_1417]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_943,plain,
% 7.53/1.50      ( k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)) = k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)) ),
% 7.53/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_257,plain,
% 7.53/1.50      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 7.53/1.50      theory(equality) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_794,plain,
% 7.53/1.50      ( k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) = k1_relat_1(X0)
% 7.53/1.50      | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)) != X0 ),
% 7.53/1.50      inference(instantiation,[status(thm)],[c_257]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_942,plain,
% 7.53/1.50      ( k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) = k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)))
% 7.53/1.50      | k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)) != k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0)) ),
% 7.53/1.50      inference(instantiation,[status(thm)],[c_794]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_7,plain,
% 7.53/1.50      ( ~ r1_tarski(X0,X1)
% 7.53/1.50      | ~ r1_tarski(X0,X2)
% 7.53/1.50      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
% 7.53/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_728,plain,
% 7.53/1.50      ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1))
% 7.53/1.50      | ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))
% 7.53/1.50      | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
% 7.53/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_729,plain,
% 7.53/1.50      ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) != iProver_top
% 7.53/1.50      | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) != iProver_top
% 7.53/1.50      | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) = iProver_top ),
% 7.53/1.50      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_264,plain,
% 7.53/1.50      ( k1_relat_1(sK0) = k1_relat_1(sK0) | sK0 != sK0 ),
% 7.53/1.50      inference(instantiation,[status(thm)],[c_257]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_1,plain,
% 7.53/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.53/1.50      inference(cnf_transformation,[],[f32]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_45,plain,
% 7.53/1.50      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 7.53/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_41,plain,
% 7.53/1.50      ( r1_tarski(sK0,sK0) ),
% 7.53/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_12,negated_conjecture,
% 7.53/1.50      ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
% 7.53/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(c_17,plain,
% 7.53/1.50      ( r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) != iProver_top ),
% 7.53/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.53/1.50  
% 7.53/1.50  cnf(contradiction,plain,
% 7.53/1.50      ( $false ),
% 7.53/1.50      inference(minisat,
% 7.53/1.50                [status(thm)],
% 7.53/1.50                [c_13261,c_12828,c_1418,c_943,c_942,c_729,c_264,c_45,
% 7.53/1.50                 c_41,c_17]) ).
% 7.53/1.50  
% 7.53/1.50  
% 7.53/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.53/1.50  
% 7.53/1.50  ------                               Statistics
% 7.53/1.50  
% 7.53/1.50  ------ Selected
% 7.53/1.50  
% 7.53/1.50  total_time:                             0.64
% 7.53/1.50  
%------------------------------------------------------------------------------
