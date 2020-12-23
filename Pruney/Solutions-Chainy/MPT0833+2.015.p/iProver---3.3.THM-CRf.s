%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:55 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 209 expanded)
%              Number of clauses        :   60 (  84 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   19
%              Number of atoms          :  313 ( 596 expanded)
%              Number of equality atoms :   93 ( 118 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f41,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r2_relset_1(sK2,sK3,k6_relset_1(sK2,sK3,sK4,sK5),sK5)
      & r1_tarski(sK3,sK4)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ r2_relset_1(sK2,sK3,k6_relset_1(sK2,sK3,sK4,sK5),sK5)
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f41])).

fof(f65,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ~ r2_relset_1(sK2,sK3,k6_relset_1(sK2,sK3,sK4,sK5),sK5) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1102,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1101,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_15,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_345,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_15])).

cnf(c_1097,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_1469,plain,
    ( r1_tarski(k2_relat_1(sK5),sK3) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1101,c_1097])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1109,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1113,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1116,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1964,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_zfmisc_1(X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_1116])).

cnf(c_3331,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1109,c_1964])).

cnf(c_4696,plain,
    ( r2_hidden(k2_relat_1(sK5),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_3331])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1106,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1456,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1101,c_1106])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_198,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_199,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_198])).

cnf(c_242,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_199])).

cnf(c_1100,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_242])).

cnf(c_1743,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_1100])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1105,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2276,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1743,c_1105])).

cnf(c_5557,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | r2_hidden(k2_relat_1(sK5),k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4696,c_2276])).

cnf(c_5558,plain,
    ( r2_hidden(k2_relat_1(sK5),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5557])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1112,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5567,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5558,c_1112])).

cnf(c_17,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1104,plain,
    ( k8_relat_1(X0,X1) = X1
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5907,plain,
    ( k8_relat_1(X0,sK5) = sK5
    | r1_tarski(sK3,X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5567,c_1104])).

cnf(c_6834,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | k8_relat_1(X0,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5907,c_2276])).

cnf(c_6835,plain,
    ( k8_relat_1(X0,sK5) = sK5
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6834])).

cnf(c_6840,plain,
    ( k8_relat_1(sK4,sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_1102,c_6835])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1103,plain,
    ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1857,plain,
    ( k6_relset_1(sK2,sK3,X0,sK5) = k8_relat_1(X0,sK5) ),
    inference(superposition,[status(thm)],[c_1101,c_1103])).

cnf(c_20,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,negated_conjecture,
    ( ~ r2_relset_1(sK2,sK3,k6_relset_1(sK2,sK3,sK4,sK5),sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_326,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(sK2,sK3,sK4,sK5) != X3
    | sK5 != X3
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_21])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ m1_subset_1(k6_relset_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sK5 != k6_relset_1(sK2,sK3,sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_558,plain,
    ( ~ m1_subset_1(k6_relset_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | sP0_iProver_split
    | sK5 != k6_relset_1(sK2,sK3,sK4,sK5) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_327])).

cnf(c_1098,plain,
    ( sK5 != k6_relset_1(sK2,sK3,sK4,sK5)
    | m1_subset_1(k6_relset_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_557,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_327])).

cnf(c_1099,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_557])).

cnf(c_1212,plain,
    ( k6_relset_1(sK2,sK3,sK4,sK5) != sK5
    | m1_subset_1(k6_relset_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1098,c_1099])).

cnf(c_2093,plain,
    ( k8_relat_1(sK4,sK5) != sK5
    | m1_subset_1(k8_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1857,c_1212])).

cnf(c_6894,plain,
    ( sK5 != sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6840,c_2093])).

cnf(c_560,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1333,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_24,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6894,c_1333,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n013.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:01:54 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.05/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/0.93  
% 3.05/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.05/0.93  
% 3.05/0.93  ------  iProver source info
% 3.05/0.93  
% 3.05/0.93  git: date: 2020-06-30 10:37:57 +0100
% 3.05/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.05/0.93  git: non_committed_changes: false
% 3.05/0.93  git: last_make_outside_of_git: false
% 3.05/0.93  
% 3.05/0.93  ------ 
% 3.05/0.93  
% 3.05/0.93  ------ Input Options
% 3.05/0.93  
% 3.05/0.93  --out_options                           all
% 3.05/0.93  --tptp_safe_out                         true
% 3.05/0.93  --problem_path                          ""
% 3.05/0.93  --include_path                          ""
% 3.05/0.93  --clausifier                            res/vclausify_rel
% 3.05/0.93  --clausifier_options                    --mode clausify
% 3.05/0.93  --stdin                                 false
% 3.05/0.93  --stats_out                             all
% 3.05/0.93  
% 3.05/0.93  ------ General Options
% 3.05/0.93  
% 3.05/0.93  --fof                                   false
% 3.05/0.93  --time_out_real                         305.
% 3.05/0.93  --time_out_virtual                      -1.
% 3.05/0.93  --symbol_type_check                     false
% 3.05/0.93  --clausify_out                          false
% 3.05/0.93  --sig_cnt_out                           false
% 3.05/0.93  --trig_cnt_out                          false
% 3.05/0.93  --trig_cnt_out_tolerance                1.
% 3.05/0.93  --trig_cnt_out_sk_spl                   false
% 3.05/0.93  --abstr_cl_out                          false
% 3.05/0.93  
% 3.05/0.93  ------ Global Options
% 3.05/0.93  
% 3.05/0.93  --schedule                              default
% 3.05/0.93  --add_important_lit                     false
% 3.05/0.93  --prop_solver_per_cl                    1000
% 3.05/0.93  --min_unsat_core                        false
% 3.05/0.93  --soft_assumptions                      false
% 3.05/0.93  --soft_lemma_size                       3
% 3.05/0.93  --prop_impl_unit_size                   0
% 3.05/0.93  --prop_impl_unit                        []
% 3.05/0.93  --share_sel_clauses                     true
% 3.05/0.93  --reset_solvers                         false
% 3.05/0.93  --bc_imp_inh                            [conj_cone]
% 3.05/0.93  --conj_cone_tolerance                   3.
% 3.05/0.93  --extra_neg_conj                        none
% 3.05/0.93  --large_theory_mode                     true
% 3.05/0.93  --prolific_symb_bound                   200
% 3.05/0.93  --lt_threshold                          2000
% 3.05/0.93  --clause_weak_htbl                      true
% 3.05/0.93  --gc_record_bc_elim                     false
% 3.05/0.93  
% 3.05/0.93  ------ Preprocessing Options
% 3.05/0.93  
% 3.05/0.93  --preprocessing_flag                    true
% 3.05/0.93  --time_out_prep_mult                    0.1
% 3.05/0.93  --splitting_mode                        input
% 3.05/0.93  --splitting_grd                         true
% 3.05/0.93  --splitting_cvd                         false
% 3.05/0.93  --splitting_cvd_svl                     false
% 3.05/0.93  --splitting_nvd                         32
% 3.05/0.93  --sub_typing                            true
% 3.05/0.93  --prep_gs_sim                           true
% 3.05/0.93  --prep_unflatten                        true
% 3.05/0.93  --prep_res_sim                          true
% 3.05/0.93  --prep_upred                            true
% 3.05/0.93  --prep_sem_filter                       exhaustive
% 3.05/0.93  --prep_sem_filter_out                   false
% 3.05/0.93  --pred_elim                             true
% 3.05/0.93  --res_sim_input                         true
% 3.05/0.93  --eq_ax_congr_red                       true
% 3.05/0.93  --pure_diseq_elim                       true
% 3.05/0.93  --brand_transform                       false
% 3.05/0.93  --non_eq_to_eq                          false
% 3.05/0.93  --prep_def_merge                        true
% 3.05/0.93  --prep_def_merge_prop_impl              false
% 3.05/0.93  --prep_def_merge_mbd                    true
% 3.05/0.93  --prep_def_merge_tr_red                 false
% 3.05/0.93  --prep_def_merge_tr_cl                  false
% 3.05/0.93  --smt_preprocessing                     true
% 3.05/0.93  --smt_ac_axioms                         fast
% 3.05/0.93  --preprocessed_out                      false
% 3.05/0.93  --preprocessed_stats                    false
% 3.05/0.93  
% 3.05/0.93  ------ Abstraction refinement Options
% 3.05/0.93  
% 3.05/0.93  --abstr_ref                             []
% 3.05/0.93  --abstr_ref_prep                        false
% 3.05/0.93  --abstr_ref_until_sat                   false
% 3.05/0.93  --abstr_ref_sig_restrict                funpre
% 3.05/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/0.93  --abstr_ref_under                       []
% 3.05/0.93  
% 3.05/0.93  ------ SAT Options
% 3.05/0.93  
% 3.05/0.93  --sat_mode                              false
% 3.05/0.93  --sat_fm_restart_options                ""
% 3.05/0.93  --sat_gr_def                            false
% 3.05/0.93  --sat_epr_types                         true
% 3.05/0.93  --sat_non_cyclic_types                  false
% 3.05/0.93  --sat_finite_models                     false
% 3.05/0.93  --sat_fm_lemmas                         false
% 3.05/0.93  --sat_fm_prep                           false
% 3.05/0.93  --sat_fm_uc_incr                        true
% 3.05/0.93  --sat_out_model                         small
% 3.05/0.93  --sat_out_clauses                       false
% 3.05/0.93  
% 3.05/0.93  ------ QBF Options
% 3.05/0.93  
% 3.05/0.93  --qbf_mode                              false
% 3.05/0.93  --qbf_elim_univ                         false
% 3.05/0.93  --qbf_dom_inst                          none
% 3.05/0.93  --qbf_dom_pre_inst                      false
% 3.05/0.93  --qbf_sk_in                             false
% 3.05/0.93  --qbf_pred_elim                         true
% 3.05/0.93  --qbf_split                             512
% 3.05/0.93  
% 3.05/0.93  ------ BMC1 Options
% 3.05/0.93  
% 3.05/0.93  --bmc1_incremental                      false
% 3.05/0.93  --bmc1_axioms                           reachable_all
% 3.05/0.93  --bmc1_min_bound                        0
% 3.05/0.93  --bmc1_max_bound                        -1
% 3.05/0.93  --bmc1_max_bound_default                -1
% 3.05/0.93  --bmc1_symbol_reachability              true
% 3.05/0.93  --bmc1_property_lemmas                  false
% 3.05/0.93  --bmc1_k_induction                      false
% 3.05/0.93  --bmc1_non_equiv_states                 false
% 3.05/0.93  --bmc1_deadlock                         false
% 3.05/0.93  --bmc1_ucm                              false
% 3.05/0.93  --bmc1_add_unsat_core                   none
% 3.05/0.93  --bmc1_unsat_core_children              false
% 3.05/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/0.93  --bmc1_out_stat                         full
% 3.05/0.93  --bmc1_ground_init                      false
% 3.05/0.93  --bmc1_pre_inst_next_state              false
% 3.05/0.93  --bmc1_pre_inst_state                   false
% 3.05/0.93  --bmc1_pre_inst_reach_state             false
% 3.05/0.93  --bmc1_out_unsat_core                   false
% 3.05/0.93  --bmc1_aig_witness_out                  false
% 3.05/0.93  --bmc1_verbose                          false
% 3.05/0.93  --bmc1_dump_clauses_tptp                false
% 3.05/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.05/0.93  --bmc1_dump_file                        -
% 3.05/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.05/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.05/0.93  --bmc1_ucm_extend_mode                  1
% 3.05/0.93  --bmc1_ucm_init_mode                    2
% 3.05/0.93  --bmc1_ucm_cone_mode                    none
% 3.05/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.05/0.93  --bmc1_ucm_relax_model                  4
% 3.05/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.05/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/0.93  --bmc1_ucm_layered_model                none
% 3.05/0.93  --bmc1_ucm_max_lemma_size               10
% 3.05/0.93  
% 3.05/0.93  ------ AIG Options
% 3.05/0.93  
% 3.05/0.93  --aig_mode                              false
% 3.05/0.93  
% 3.05/0.93  ------ Instantiation Options
% 3.05/0.93  
% 3.05/0.93  --instantiation_flag                    true
% 3.05/0.93  --inst_sos_flag                         false
% 3.05/0.93  --inst_sos_phase                        true
% 3.05/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/0.93  --inst_lit_sel_side                     num_symb
% 3.05/0.93  --inst_solver_per_active                1400
% 3.05/0.93  --inst_solver_calls_frac                1.
% 3.05/0.93  --inst_passive_queue_type               priority_queues
% 3.05/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/0.93  --inst_passive_queues_freq              [25;2]
% 3.05/0.93  --inst_dismatching                      true
% 3.05/0.93  --inst_eager_unprocessed_to_passive     true
% 3.05/0.93  --inst_prop_sim_given                   true
% 3.05/0.93  --inst_prop_sim_new                     false
% 3.05/0.93  --inst_subs_new                         false
% 3.05/0.93  --inst_eq_res_simp                      false
% 3.05/0.93  --inst_subs_given                       false
% 3.05/0.93  --inst_orphan_elimination               true
% 3.05/0.93  --inst_learning_loop_flag               true
% 3.05/0.93  --inst_learning_start                   3000
% 3.05/0.93  --inst_learning_factor                  2
% 3.05/0.93  --inst_start_prop_sim_after_learn       3
% 3.05/0.93  --inst_sel_renew                        solver
% 3.05/0.93  --inst_lit_activity_flag                true
% 3.05/0.93  --inst_restr_to_given                   false
% 3.05/0.93  --inst_activity_threshold               500
% 3.05/0.93  --inst_out_proof                        true
% 3.05/0.93  
% 3.05/0.93  ------ Resolution Options
% 3.05/0.93  
% 3.05/0.93  --resolution_flag                       true
% 3.05/0.93  --res_lit_sel                           adaptive
% 3.05/0.93  --res_lit_sel_side                      none
% 3.05/0.93  --res_ordering                          kbo
% 3.05/0.93  --res_to_prop_solver                    active
% 3.05/0.93  --res_prop_simpl_new                    false
% 3.05/0.93  --res_prop_simpl_given                  true
% 3.05/0.93  --res_passive_queue_type                priority_queues
% 3.05/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/0.93  --res_passive_queues_freq               [15;5]
% 3.05/0.93  --res_forward_subs                      full
% 3.05/0.93  --res_backward_subs                     full
% 3.05/0.93  --res_forward_subs_resolution           true
% 3.05/0.93  --res_backward_subs_resolution          true
% 3.05/0.93  --res_orphan_elimination                true
% 3.05/0.93  --res_time_limit                        2.
% 3.05/0.93  --res_out_proof                         true
% 3.05/0.93  
% 3.05/0.93  ------ Superposition Options
% 3.05/0.93  
% 3.05/0.93  --superposition_flag                    true
% 3.05/0.93  --sup_passive_queue_type                priority_queues
% 3.05/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.05/0.93  --demod_completeness_check              fast
% 3.05/0.93  --demod_use_ground                      true
% 3.05/0.93  --sup_to_prop_solver                    passive
% 3.05/0.93  --sup_prop_simpl_new                    true
% 3.05/0.93  --sup_prop_simpl_given                  true
% 3.05/0.93  --sup_fun_splitting                     false
% 3.05/0.93  --sup_smt_interval                      50000
% 3.05/0.93  
% 3.05/0.93  ------ Superposition Simplification Setup
% 3.05/0.93  
% 3.05/0.93  --sup_indices_passive                   []
% 3.05/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.93  --sup_full_bw                           [BwDemod]
% 3.05/0.93  --sup_immed_triv                        [TrivRules]
% 3.05/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.93  --sup_immed_bw_main                     []
% 3.05/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.93  
% 3.05/0.93  ------ Combination Options
% 3.05/0.93  
% 3.05/0.93  --comb_res_mult                         3
% 3.05/0.93  --comb_sup_mult                         2
% 3.05/0.93  --comb_inst_mult                        10
% 3.05/0.93  
% 3.05/0.93  ------ Debug Options
% 3.05/0.93  
% 3.05/0.93  --dbg_backtrace                         false
% 3.05/0.93  --dbg_dump_prop_clauses                 false
% 3.05/0.93  --dbg_dump_prop_clauses_file            -
% 3.05/0.93  --dbg_out_stat                          false
% 3.05/0.93  ------ Parsing...
% 3.05/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.05/0.93  
% 3.05/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.05/0.93  
% 3.05/0.93  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.05/0.93  
% 3.05/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.05/0.93  ------ Proving...
% 3.05/0.93  ------ Problem Properties 
% 3.05/0.93  
% 3.05/0.93  
% 3.05/0.93  clauses                                 22
% 3.05/0.93  conjectures                             2
% 3.05/0.93  EPR                                     4
% 3.05/0.93  Horn                                    20
% 3.05/0.93  unary                                   3
% 3.05/0.93  binary                                  12
% 3.05/0.93  lits                                    48
% 3.05/0.93  lits eq                                 5
% 3.05/0.93  fd_pure                                 0
% 3.05/0.93  fd_pseudo                               0
% 3.05/0.93  fd_cond                                 0
% 3.05/0.93  fd_pseudo_cond                          2
% 3.05/0.93  AC symbols                              0
% 3.05/0.93  
% 3.05/0.93  ------ Schedule dynamic 5 is on 
% 3.05/0.93  
% 3.05/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.05/0.93  
% 3.05/0.93  
% 3.05/0.93  ------ 
% 3.05/0.93  Current options:
% 3.05/0.93  ------ 
% 3.05/0.93  
% 3.05/0.93  ------ Input Options
% 3.05/0.93  
% 3.05/0.93  --out_options                           all
% 3.05/0.93  --tptp_safe_out                         true
% 3.05/0.93  --problem_path                          ""
% 3.05/0.93  --include_path                          ""
% 3.05/0.93  --clausifier                            res/vclausify_rel
% 3.05/0.93  --clausifier_options                    --mode clausify
% 3.05/0.93  --stdin                                 false
% 3.05/0.93  --stats_out                             all
% 3.05/0.93  
% 3.05/0.93  ------ General Options
% 3.05/0.93  
% 3.05/0.93  --fof                                   false
% 3.05/0.93  --time_out_real                         305.
% 3.05/0.93  --time_out_virtual                      -1.
% 3.05/0.93  --symbol_type_check                     false
% 3.05/0.93  --clausify_out                          false
% 3.05/0.93  --sig_cnt_out                           false
% 3.05/0.93  --trig_cnt_out                          false
% 3.05/0.93  --trig_cnt_out_tolerance                1.
% 3.05/0.93  --trig_cnt_out_sk_spl                   false
% 3.05/0.93  --abstr_cl_out                          false
% 3.05/0.93  
% 3.05/0.93  ------ Global Options
% 3.05/0.93  
% 3.05/0.93  --schedule                              default
% 3.05/0.93  --add_important_lit                     false
% 3.05/0.93  --prop_solver_per_cl                    1000
% 3.05/0.93  --min_unsat_core                        false
% 3.05/0.93  --soft_assumptions                      false
% 3.05/0.93  --soft_lemma_size                       3
% 3.05/0.93  --prop_impl_unit_size                   0
% 3.05/0.93  --prop_impl_unit                        []
% 3.05/0.93  --share_sel_clauses                     true
% 3.05/0.93  --reset_solvers                         false
% 3.05/0.93  --bc_imp_inh                            [conj_cone]
% 3.05/0.93  --conj_cone_tolerance                   3.
% 3.05/0.93  --extra_neg_conj                        none
% 3.05/0.93  --large_theory_mode                     true
% 3.05/0.93  --prolific_symb_bound                   200
% 3.05/0.93  --lt_threshold                          2000
% 3.05/0.93  --clause_weak_htbl                      true
% 3.05/0.93  --gc_record_bc_elim                     false
% 3.05/0.93  
% 3.05/0.93  ------ Preprocessing Options
% 3.05/0.93  
% 3.05/0.93  --preprocessing_flag                    true
% 3.05/0.93  --time_out_prep_mult                    0.1
% 3.05/0.93  --splitting_mode                        input
% 3.05/0.93  --splitting_grd                         true
% 3.05/0.93  --splitting_cvd                         false
% 3.05/0.93  --splitting_cvd_svl                     false
% 3.05/0.93  --splitting_nvd                         32
% 3.05/0.93  --sub_typing                            true
% 3.05/0.93  --prep_gs_sim                           true
% 3.05/0.93  --prep_unflatten                        true
% 3.05/0.93  --prep_res_sim                          true
% 3.05/0.93  --prep_upred                            true
% 3.05/0.93  --prep_sem_filter                       exhaustive
% 3.05/0.93  --prep_sem_filter_out                   false
% 3.05/0.93  --pred_elim                             true
% 3.05/0.93  --res_sim_input                         true
% 3.05/0.93  --eq_ax_congr_red                       true
% 3.05/0.93  --pure_diseq_elim                       true
% 3.05/0.93  --brand_transform                       false
% 3.05/0.93  --non_eq_to_eq                          false
% 3.05/0.93  --prep_def_merge                        true
% 3.05/0.93  --prep_def_merge_prop_impl              false
% 3.05/0.93  --prep_def_merge_mbd                    true
% 3.05/0.93  --prep_def_merge_tr_red                 false
% 3.05/0.93  --prep_def_merge_tr_cl                  false
% 3.05/0.93  --smt_preprocessing                     true
% 3.05/0.93  --smt_ac_axioms                         fast
% 3.05/0.93  --preprocessed_out                      false
% 3.05/0.93  --preprocessed_stats                    false
% 3.05/0.93  
% 3.05/0.93  ------ Abstraction refinement Options
% 3.05/0.93  
% 3.05/0.93  --abstr_ref                             []
% 3.05/0.93  --abstr_ref_prep                        false
% 3.05/0.93  --abstr_ref_until_sat                   false
% 3.05/0.93  --abstr_ref_sig_restrict                funpre
% 3.05/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/0.93  --abstr_ref_under                       []
% 3.05/0.93  
% 3.05/0.93  ------ SAT Options
% 3.05/0.93  
% 3.05/0.93  --sat_mode                              false
% 3.05/0.93  --sat_fm_restart_options                ""
% 3.05/0.93  --sat_gr_def                            false
% 3.05/0.93  --sat_epr_types                         true
% 3.05/0.93  --sat_non_cyclic_types                  false
% 3.05/0.93  --sat_finite_models                     false
% 3.05/0.93  --sat_fm_lemmas                         false
% 3.05/0.93  --sat_fm_prep                           false
% 3.05/0.93  --sat_fm_uc_incr                        true
% 3.05/0.93  --sat_out_model                         small
% 3.05/0.93  --sat_out_clauses                       false
% 3.05/0.93  
% 3.05/0.93  ------ QBF Options
% 3.05/0.93  
% 3.05/0.93  --qbf_mode                              false
% 3.05/0.93  --qbf_elim_univ                         false
% 3.05/0.93  --qbf_dom_inst                          none
% 3.05/0.93  --qbf_dom_pre_inst                      false
% 3.05/0.93  --qbf_sk_in                             false
% 3.05/0.93  --qbf_pred_elim                         true
% 3.05/0.93  --qbf_split                             512
% 3.05/0.93  
% 3.05/0.93  ------ BMC1 Options
% 3.05/0.93  
% 3.05/0.93  --bmc1_incremental                      false
% 3.05/0.93  --bmc1_axioms                           reachable_all
% 3.05/0.93  --bmc1_min_bound                        0
% 3.05/0.93  --bmc1_max_bound                        -1
% 3.05/0.93  --bmc1_max_bound_default                -1
% 3.05/0.93  --bmc1_symbol_reachability              true
% 3.05/0.93  --bmc1_property_lemmas                  false
% 3.05/0.93  --bmc1_k_induction                      false
% 3.05/0.93  --bmc1_non_equiv_states                 false
% 3.05/0.93  --bmc1_deadlock                         false
% 3.05/0.93  --bmc1_ucm                              false
% 3.05/0.93  --bmc1_add_unsat_core                   none
% 3.05/0.93  --bmc1_unsat_core_children              false
% 3.05/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/0.93  --bmc1_out_stat                         full
% 3.05/0.93  --bmc1_ground_init                      false
% 3.05/0.93  --bmc1_pre_inst_next_state              false
% 3.05/0.93  --bmc1_pre_inst_state                   false
% 3.05/0.93  --bmc1_pre_inst_reach_state             false
% 3.05/0.93  --bmc1_out_unsat_core                   false
% 3.05/0.93  --bmc1_aig_witness_out                  false
% 3.05/0.93  --bmc1_verbose                          false
% 3.05/0.93  --bmc1_dump_clauses_tptp                false
% 3.05/0.93  --bmc1_dump_unsat_core_tptp             false
% 3.05/0.93  --bmc1_dump_file                        -
% 3.05/0.93  --bmc1_ucm_expand_uc_limit              128
% 3.05/0.93  --bmc1_ucm_n_expand_iterations          6
% 3.05/0.93  --bmc1_ucm_extend_mode                  1
% 3.05/0.93  --bmc1_ucm_init_mode                    2
% 3.05/0.93  --bmc1_ucm_cone_mode                    none
% 3.05/0.93  --bmc1_ucm_reduced_relation_type        0
% 3.05/0.93  --bmc1_ucm_relax_model                  4
% 3.05/0.93  --bmc1_ucm_full_tr_after_sat            true
% 3.05/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/0.93  --bmc1_ucm_layered_model                none
% 3.05/0.93  --bmc1_ucm_max_lemma_size               10
% 3.05/0.93  
% 3.05/0.93  ------ AIG Options
% 3.05/0.93  
% 3.05/0.93  --aig_mode                              false
% 3.05/0.93  
% 3.05/0.93  ------ Instantiation Options
% 3.05/0.93  
% 3.05/0.93  --instantiation_flag                    true
% 3.05/0.93  --inst_sos_flag                         false
% 3.05/0.93  --inst_sos_phase                        true
% 3.05/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/0.93  --inst_lit_sel_side                     none
% 3.05/0.93  --inst_solver_per_active                1400
% 3.05/0.93  --inst_solver_calls_frac                1.
% 3.05/0.93  --inst_passive_queue_type               priority_queues
% 3.05/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/0.93  --inst_passive_queues_freq              [25;2]
% 3.05/0.93  --inst_dismatching                      true
% 3.05/0.93  --inst_eager_unprocessed_to_passive     true
% 3.05/0.93  --inst_prop_sim_given                   true
% 3.05/0.93  --inst_prop_sim_new                     false
% 3.05/0.93  --inst_subs_new                         false
% 3.05/0.93  --inst_eq_res_simp                      false
% 3.05/0.93  --inst_subs_given                       false
% 3.05/0.93  --inst_orphan_elimination               true
% 3.05/0.93  --inst_learning_loop_flag               true
% 3.05/0.93  --inst_learning_start                   3000
% 3.05/0.93  --inst_learning_factor                  2
% 3.05/0.93  --inst_start_prop_sim_after_learn       3
% 3.05/0.93  --inst_sel_renew                        solver
% 3.05/0.93  --inst_lit_activity_flag                true
% 3.05/0.93  --inst_restr_to_given                   false
% 3.05/0.93  --inst_activity_threshold               500
% 3.05/0.93  --inst_out_proof                        true
% 3.05/0.93  
% 3.05/0.93  ------ Resolution Options
% 3.05/0.93  
% 3.05/0.93  --resolution_flag                       false
% 3.05/0.93  --res_lit_sel                           adaptive
% 3.05/0.93  --res_lit_sel_side                      none
% 3.05/0.93  --res_ordering                          kbo
% 3.05/0.93  --res_to_prop_solver                    active
% 3.05/0.93  --res_prop_simpl_new                    false
% 3.05/0.93  --res_prop_simpl_given                  true
% 3.05/0.93  --res_passive_queue_type                priority_queues
% 3.05/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/0.93  --res_passive_queues_freq               [15;5]
% 3.05/0.93  --res_forward_subs                      full
% 3.05/0.93  --res_backward_subs                     full
% 3.05/0.93  --res_forward_subs_resolution           true
% 3.05/0.93  --res_backward_subs_resolution          true
% 3.05/0.93  --res_orphan_elimination                true
% 3.05/0.93  --res_time_limit                        2.
% 3.05/0.93  --res_out_proof                         true
% 3.05/0.93  
% 3.05/0.93  ------ Superposition Options
% 3.05/0.93  
% 3.05/0.93  --superposition_flag                    true
% 3.05/0.93  --sup_passive_queue_type                priority_queues
% 3.05/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/0.93  --sup_passive_queues_freq               [8;1;4]
% 3.05/0.93  --demod_completeness_check              fast
% 3.05/0.93  --demod_use_ground                      true
% 3.05/0.93  --sup_to_prop_solver                    passive
% 3.05/0.93  --sup_prop_simpl_new                    true
% 3.05/0.93  --sup_prop_simpl_given                  true
% 3.05/0.93  --sup_fun_splitting                     false
% 3.05/0.93  --sup_smt_interval                      50000
% 3.05/0.93  
% 3.05/0.93  ------ Superposition Simplification Setup
% 3.05/0.93  
% 3.05/0.93  --sup_indices_passive                   []
% 3.05/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.93  --sup_full_bw                           [BwDemod]
% 3.05/0.93  --sup_immed_triv                        [TrivRules]
% 3.05/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.93  --sup_immed_bw_main                     []
% 3.05/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/0.93  
% 3.05/0.93  ------ Combination Options
% 3.05/0.93  
% 3.05/0.93  --comb_res_mult                         3
% 3.05/0.93  --comb_sup_mult                         2
% 3.05/0.93  --comb_inst_mult                        10
% 3.05/0.93  
% 3.05/0.93  ------ Debug Options
% 3.05/0.93  
% 3.05/0.93  --dbg_backtrace                         false
% 3.05/0.93  --dbg_dump_prop_clauses                 false
% 3.05/0.93  --dbg_dump_prop_clauses_file            -
% 3.05/0.93  --dbg_out_stat                          false
% 3.05/0.93  
% 3.05/0.93  
% 3.05/0.93  
% 3.05/0.93  
% 3.05/0.93  ------ Proving...
% 3.05/0.93  
% 3.05/0.93  
% 3.05/0.93  % SZS status Theorem for theBenchmark.p
% 3.05/0.93  
% 3.05/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 3.05/0.93  
% 3.05/0.93  fof(f14,conjecture,(
% 3.05/0.93    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 3.05/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.93  
% 3.05/0.93  fof(f15,negated_conjecture,(
% 3.05/0.93    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 3.05/0.93    inference(negated_conjecture,[],[f14])).
% 3.05/0.93  
% 3.05/0.93  fof(f29,plain,(
% 3.05/0.93    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.93    inference(ennf_transformation,[],[f15])).
% 3.05/0.93  
% 3.05/0.93  fof(f30,plain,(
% 3.05/0.93    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.93    inference(flattening,[],[f29])).
% 3.05/0.93  
% 3.05/0.93  fof(f41,plain,(
% 3.05/0.93    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r2_relset_1(sK2,sK3,k6_relset_1(sK2,sK3,sK4,sK5),sK5) & r1_tarski(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))))),
% 3.05/0.93    introduced(choice_axiom,[])).
% 3.05/0.93  
% 3.05/0.93  fof(f42,plain,(
% 3.05/0.93    ~r2_relset_1(sK2,sK3,k6_relset_1(sK2,sK3,sK4,sK5),sK5) & r1_tarski(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.05/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f41])).
% 3.05/0.93  
% 3.05/0.93  fof(f65,plain,(
% 3.05/0.93    r1_tarski(sK3,sK4)),
% 3.05/0.93    inference(cnf_transformation,[],[f42])).
% 3.05/0.93  
% 3.05/0.93  fof(f64,plain,(
% 3.05/0.93    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.05/0.93    inference(cnf_transformation,[],[f42])).
% 3.05/0.93  
% 3.05/0.93  fof(f11,axiom,(
% 3.05/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.05/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.93  
% 3.05/0.93  fof(f16,plain,(
% 3.05/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.05/0.93    inference(pure_predicate_removal,[],[f11])).
% 3.05/0.93  
% 3.05/0.93  fof(f25,plain,(
% 3.05/0.93    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.93    inference(ennf_transformation,[],[f16])).
% 3.05/0.93  
% 3.05/0.93  fof(f61,plain,(
% 3.05/0.93    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.93    inference(cnf_transformation,[],[f25])).
% 3.05/0.93  
% 3.05/0.93  fof(f8,axiom,(
% 3.05/0.93    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.05/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.93  
% 3.05/0.93  fof(f22,plain,(
% 3.05/0.93    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.05/0.93    inference(ennf_transformation,[],[f8])).
% 3.05/0.93  
% 3.05/0.93  fof(f40,plain,(
% 3.05/0.93    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.05/0.93    inference(nnf_transformation,[],[f22])).
% 3.05/0.93  
% 3.05/0.93  fof(f57,plain,(
% 3.05/0.93    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.05/0.93    inference(cnf_transformation,[],[f40])).
% 3.05/0.93  
% 3.05/0.93  fof(f4,axiom,(
% 3.05/0.93    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 3.05/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.93  
% 3.05/0.93  fof(f19,plain,(
% 3.05/0.93    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 3.05/0.93    inference(ennf_transformation,[],[f4])).
% 3.05/0.93  
% 3.05/0.93  fof(f52,plain,(
% 3.05/0.93    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.05/0.93    inference(cnf_transformation,[],[f19])).
% 3.05/0.93  
% 3.05/0.93  fof(f2,axiom,(
% 3.05/0.93    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.05/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.93  
% 3.05/0.93  fof(f35,plain,(
% 3.05/0.93    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.05/0.93    inference(nnf_transformation,[],[f2])).
% 3.05/0.93  
% 3.05/0.93  fof(f36,plain,(
% 3.05/0.93    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.05/0.93    inference(rectify,[],[f35])).
% 3.05/0.93  
% 3.05/0.93  fof(f37,plain,(
% 3.05/0.93    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 3.05/0.93    introduced(choice_axiom,[])).
% 3.05/0.93  
% 3.05/0.93  fof(f38,plain,(
% 3.05/0.93    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.05/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 3.05/0.93  
% 3.05/0.93  fof(f47,plain,(
% 3.05/0.93    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 3.05/0.93    inference(cnf_transformation,[],[f38])).
% 3.05/0.93  
% 3.05/0.93  fof(f67,plain,(
% 3.05/0.93    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 3.05/0.93    inference(equality_resolution,[],[f47])).
% 3.05/0.93  
% 3.05/0.93  fof(f1,axiom,(
% 3.05/0.93    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.05/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.93  
% 3.05/0.93  fof(f17,plain,(
% 3.05/0.93    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.05/0.93    inference(ennf_transformation,[],[f1])).
% 3.05/0.93  
% 3.05/0.93  fof(f31,plain,(
% 3.05/0.93    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.05/0.93    inference(nnf_transformation,[],[f17])).
% 3.05/0.93  
% 3.05/0.93  fof(f32,plain,(
% 3.05/0.93    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.05/0.93    inference(rectify,[],[f31])).
% 3.05/0.93  
% 3.05/0.93  fof(f33,plain,(
% 3.05/0.93    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.05/0.93    introduced(choice_axiom,[])).
% 3.05/0.93  
% 3.05/0.93  fof(f34,plain,(
% 3.05/0.93    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.05/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 3.05/0.93  
% 3.05/0.93  fof(f43,plain,(
% 3.05/0.93    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.05/0.93    inference(cnf_transformation,[],[f34])).
% 3.05/0.93  
% 3.05/0.93  fof(f6,axiom,(
% 3.05/0.93    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.05/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.93  
% 3.05/0.93  fof(f39,plain,(
% 3.05/0.93    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.05/0.93    inference(nnf_transformation,[],[f6])).
% 3.05/0.93  
% 3.05/0.93  fof(f54,plain,(
% 3.05/0.93    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.05/0.93    inference(cnf_transformation,[],[f39])).
% 3.05/0.93  
% 3.05/0.93  fof(f7,axiom,(
% 3.05/0.93    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.05/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.93  
% 3.05/0.93  fof(f21,plain,(
% 3.05/0.93    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.05/0.93    inference(ennf_transformation,[],[f7])).
% 3.05/0.93  
% 3.05/0.93  fof(f56,plain,(
% 3.05/0.93    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.05/0.93    inference(cnf_transformation,[],[f21])).
% 3.05/0.93  
% 3.05/0.93  fof(f55,plain,(
% 3.05/0.93    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.05/0.93    inference(cnf_transformation,[],[f39])).
% 3.05/0.93  
% 3.05/0.93  fof(f9,axiom,(
% 3.05/0.93    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.05/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.93  
% 3.05/0.93  fof(f59,plain,(
% 3.05/0.93    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.05/0.93    inference(cnf_transformation,[],[f9])).
% 3.05/0.93  
% 3.05/0.93  fof(f46,plain,(
% 3.05/0.93    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.05/0.93    inference(cnf_transformation,[],[f38])).
% 3.05/0.93  
% 3.05/0.93  fof(f68,plain,(
% 3.05/0.93    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.05/0.93    inference(equality_resolution,[],[f46])).
% 3.05/0.93  
% 3.05/0.93  fof(f10,axiom,(
% 3.05/0.93    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 3.05/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.93  
% 3.05/0.93  fof(f23,plain,(
% 3.05/0.93    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.05/0.93    inference(ennf_transformation,[],[f10])).
% 3.05/0.93  
% 3.05/0.93  fof(f24,plain,(
% 3.05/0.93    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.05/0.93    inference(flattening,[],[f23])).
% 3.05/0.93  
% 3.05/0.93  fof(f60,plain,(
% 3.05/0.93    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.05/0.93    inference(cnf_transformation,[],[f24])).
% 3.05/0.93  
% 3.05/0.93  fof(f12,axiom,(
% 3.05/0.93    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3))),
% 3.05/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.93  
% 3.05/0.93  fof(f26,plain,(
% 3.05/0.93    ! [X0,X1,X2,X3] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.93    inference(ennf_transformation,[],[f12])).
% 3.05/0.93  
% 3.05/0.93  fof(f62,plain,(
% 3.05/0.93    ( ! [X2,X0,X3,X1] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.93    inference(cnf_transformation,[],[f26])).
% 3.05/0.93  
% 3.05/0.93  fof(f13,axiom,(
% 3.05/0.93    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.05/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/0.93  
% 3.05/0.93  fof(f27,plain,(
% 3.05/0.93    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.05/0.93    inference(ennf_transformation,[],[f13])).
% 3.05/0.93  
% 3.05/0.93  fof(f28,plain,(
% 3.05/0.93    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/0.93    inference(flattening,[],[f27])).
% 3.05/0.93  
% 3.05/0.93  fof(f63,plain,(
% 3.05/0.93    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/0.93    inference(cnf_transformation,[],[f28])).
% 3.05/0.93  
% 3.05/0.93  fof(f66,plain,(
% 3.05/0.93    ~r2_relset_1(sK2,sK3,k6_relset_1(sK2,sK3,sK4,sK5),sK5)),
% 3.05/0.93    inference(cnf_transformation,[],[f42])).
% 3.05/0.93  
% 3.05/0.93  cnf(c_22,negated_conjecture,
% 3.05/0.93      ( r1_tarski(sK3,sK4) ),
% 3.05/0.93      inference(cnf_transformation,[],[f65]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1102,plain,
% 3.05/0.93      ( r1_tarski(sK3,sK4) = iProver_top ),
% 3.05/0.93      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_23,negated_conjecture,
% 3.05/0.93      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.05/0.93      inference(cnf_transformation,[],[f64]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1101,plain,
% 3.05/0.93      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.05/0.93      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_18,plain,
% 3.05/0.93      ( v5_relat_1(X0,X1)
% 3.05/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.05/0.93      inference(cnf_transformation,[],[f61]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_15,plain,
% 3.05/0.93      ( ~ v5_relat_1(X0,X1)
% 3.05/0.93      | r1_tarski(k2_relat_1(X0),X1)
% 3.05/0.93      | ~ v1_relat_1(X0) ),
% 3.05/0.93      inference(cnf_transformation,[],[f57]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_345,plain,
% 3.05/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.93      | r1_tarski(k2_relat_1(X0),X2)
% 3.05/0.93      | ~ v1_relat_1(X0) ),
% 3.05/0.93      inference(resolution,[status(thm)],[c_18,c_15]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1097,plain,
% 3.05/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.05/0.93      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.05/0.93      | v1_relat_1(X0) != iProver_top ),
% 3.05/0.93      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1469,plain,
% 3.05/0.93      ( r1_tarski(k2_relat_1(sK5),sK3) = iProver_top
% 3.05/0.93      | v1_relat_1(sK5) != iProver_top ),
% 3.05/0.93      inference(superposition,[status(thm)],[c_1101,c_1097]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_9,plain,
% 3.05/0.93      ( ~ r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
% 3.05/0.93      inference(cnf_transformation,[],[f52]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1109,plain,
% 3.05/0.93      ( r1_tarski(X0,X1) != iProver_top
% 3.05/0.93      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.05/0.93      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_5,plain,
% 3.05/0.93      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.05/0.93      inference(cnf_transformation,[],[f67]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1113,plain,
% 3.05/0.93      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.05/0.93      | r1_tarski(X0,X1) != iProver_top ),
% 3.05/0.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_2,plain,
% 3.05/0.93      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.05/0.93      inference(cnf_transformation,[],[f43]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1116,plain,
% 3.05/0.93      ( r2_hidden(X0,X1) != iProver_top
% 3.05/0.93      | r2_hidden(X0,X2) = iProver_top
% 3.05/0.93      | r1_tarski(X1,X2) != iProver_top ),
% 3.05/0.93      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1964,plain,
% 3.05/0.93      ( r2_hidden(X0,X1) = iProver_top
% 3.05/0.93      | r1_tarski(X0,X2) != iProver_top
% 3.05/0.93      | r1_tarski(k1_zfmisc_1(X2),X1) != iProver_top ),
% 3.05/0.93      inference(superposition,[status(thm)],[c_1113,c_1116]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_3331,plain,
% 3.05/0.93      ( r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.05/0.93      | r1_tarski(X2,X1) != iProver_top
% 3.05/0.93      | r1_tarski(X0,X2) != iProver_top ),
% 3.05/0.93      inference(superposition,[status(thm)],[c_1109,c_1964]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_4696,plain,
% 3.05/0.93      ( r2_hidden(k2_relat_1(sK5),k1_zfmisc_1(X0)) = iProver_top
% 3.05/0.93      | r1_tarski(sK3,X0) != iProver_top
% 3.05/0.93      | v1_relat_1(sK5) != iProver_top ),
% 3.05/0.93      inference(superposition,[status(thm)],[c_1469,c_3331]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_12,plain,
% 3.05/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.05/0.93      inference(cnf_transformation,[],[f54]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1106,plain,
% 3.05/0.93      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.05/0.93      | r1_tarski(X0,X1) = iProver_top ),
% 3.05/0.93      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1456,plain,
% 3.05/0.93      ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.05/0.93      inference(superposition,[status(thm)],[c_1101,c_1106]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_13,plain,
% 3.05/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.05/0.93      | ~ v1_relat_1(X1)
% 3.05/0.93      | v1_relat_1(X0) ),
% 3.05/0.93      inference(cnf_transformation,[],[f56]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_11,plain,
% 3.05/0.93      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.05/0.93      inference(cnf_transformation,[],[f55]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_198,plain,
% 3.05/0.93      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.05/0.93      inference(prop_impl,[status(thm)],[c_11]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_199,plain,
% 3.05/0.93      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.05/0.93      inference(renaming,[status(thm)],[c_198]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_242,plain,
% 3.05/0.93      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.05/0.93      inference(bin_hyper_res,[status(thm)],[c_13,c_199]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1100,plain,
% 3.05/0.93      ( r1_tarski(X0,X1) != iProver_top
% 3.05/0.93      | v1_relat_1(X1) != iProver_top
% 3.05/0.93      | v1_relat_1(X0) = iProver_top ),
% 3.05/0.93      inference(predicate_to_equality,[status(thm)],[c_242]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1743,plain,
% 3.05/0.93      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 3.05/0.93      | v1_relat_1(sK5) = iProver_top ),
% 3.05/0.93      inference(superposition,[status(thm)],[c_1456,c_1100]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_16,plain,
% 3.05/0.93      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.05/0.93      inference(cnf_transformation,[],[f59]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1105,plain,
% 3.05/0.93      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.05/0.93      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_2276,plain,
% 3.05/0.93      ( v1_relat_1(sK5) = iProver_top ),
% 3.05/0.93      inference(forward_subsumption_resolution,
% 3.05/0.93                [status(thm)],
% 3.05/0.93                [c_1743,c_1105]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_5557,plain,
% 3.05/0.93      ( r1_tarski(sK3,X0) != iProver_top
% 3.05/0.93      | r2_hidden(k2_relat_1(sK5),k1_zfmisc_1(X0)) = iProver_top ),
% 3.05/0.93      inference(global_propositional_subsumption,
% 3.05/0.93                [status(thm)],
% 3.05/0.93                [c_4696,c_2276]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_5558,plain,
% 3.05/0.93      ( r2_hidden(k2_relat_1(sK5),k1_zfmisc_1(X0)) = iProver_top
% 3.05/0.93      | r1_tarski(sK3,X0) != iProver_top ),
% 3.05/0.93      inference(renaming,[status(thm)],[c_5557]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_6,plain,
% 3.05/0.93      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.05/0.93      inference(cnf_transformation,[],[f68]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1112,plain,
% 3.05/0.93      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.05/0.93      | r1_tarski(X0,X1) = iProver_top ),
% 3.05/0.93      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_5567,plain,
% 3.05/0.93      ( r1_tarski(k2_relat_1(sK5),X0) = iProver_top
% 3.05/0.93      | r1_tarski(sK3,X0) != iProver_top ),
% 3.05/0.93      inference(superposition,[status(thm)],[c_5558,c_1112]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_17,plain,
% 3.05/0.93      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.05/0.93      | ~ v1_relat_1(X0)
% 3.05/0.93      | k8_relat_1(X1,X0) = X0 ),
% 3.05/0.93      inference(cnf_transformation,[],[f60]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1104,plain,
% 3.05/0.93      ( k8_relat_1(X0,X1) = X1
% 3.05/0.93      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 3.05/0.93      | v1_relat_1(X1) != iProver_top ),
% 3.05/0.93      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_5907,plain,
% 3.05/0.93      ( k8_relat_1(X0,sK5) = sK5
% 3.05/0.93      | r1_tarski(sK3,X0) != iProver_top
% 3.05/0.93      | v1_relat_1(sK5) != iProver_top ),
% 3.05/0.93      inference(superposition,[status(thm)],[c_5567,c_1104]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_6834,plain,
% 3.05/0.93      ( r1_tarski(sK3,X0) != iProver_top | k8_relat_1(X0,sK5) = sK5 ),
% 3.05/0.93      inference(global_propositional_subsumption,
% 3.05/0.93                [status(thm)],
% 3.05/0.93                [c_5907,c_2276]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_6835,plain,
% 3.05/0.93      ( k8_relat_1(X0,sK5) = sK5 | r1_tarski(sK3,X0) != iProver_top ),
% 3.05/0.93      inference(renaming,[status(thm)],[c_6834]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_6840,plain,
% 3.05/0.93      ( k8_relat_1(sK4,sK5) = sK5 ),
% 3.05/0.93      inference(superposition,[status(thm)],[c_1102,c_6835]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_19,plain,
% 3.05/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.93      | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
% 3.05/0.93      inference(cnf_transformation,[],[f62]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1103,plain,
% 3.05/0.93      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
% 3.05/0.93      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.05/0.93      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1857,plain,
% 3.05/0.93      ( k6_relset_1(sK2,sK3,X0,sK5) = k8_relat_1(X0,sK5) ),
% 3.05/0.93      inference(superposition,[status(thm)],[c_1101,c_1103]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_20,plain,
% 3.05/0.93      ( r2_relset_1(X0,X1,X2,X2)
% 3.05/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.05/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.05/0.93      inference(cnf_transformation,[],[f63]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_21,negated_conjecture,
% 3.05/0.93      ( ~ r2_relset_1(sK2,sK3,k6_relset_1(sK2,sK3,sK4,sK5),sK5) ),
% 3.05/0.93      inference(cnf_transformation,[],[f66]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_326,plain,
% 3.05/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/0.93      | k6_relset_1(sK2,sK3,sK4,sK5) != X3
% 3.05/0.93      | sK5 != X3
% 3.05/0.93      | sK3 != X2
% 3.05/0.93      | sK2 != X1 ),
% 3.05/0.93      inference(resolution_lifted,[status(thm)],[c_20,c_21]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_327,plain,
% 3.05/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.05/0.93      | ~ m1_subset_1(k6_relset_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.05/0.93      | sK5 != k6_relset_1(sK2,sK3,sK4,sK5) ),
% 3.05/0.93      inference(unflattening,[status(thm)],[c_326]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_558,plain,
% 3.05/0.93      ( ~ m1_subset_1(k6_relset_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.05/0.93      | sP0_iProver_split
% 3.05/0.93      | sK5 != k6_relset_1(sK2,sK3,sK4,sK5) ),
% 3.05/0.93      inference(splitting,
% 3.05/0.93                [splitting(split),new_symbols(definition,[])],
% 3.05/0.93                [c_327]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1098,plain,
% 3.05/0.93      ( sK5 != k6_relset_1(sK2,sK3,sK4,sK5)
% 3.05/0.93      | m1_subset_1(k6_relset_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.05/0.93      | sP0_iProver_split = iProver_top ),
% 3.05/0.93      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_557,plain,
% 3.05/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.05/0.93      | ~ sP0_iProver_split ),
% 3.05/0.93      inference(splitting,
% 3.05/0.93                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.05/0.93                [c_327]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1099,plain,
% 3.05/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.05/0.93      | sP0_iProver_split != iProver_top ),
% 3.05/0.93      inference(predicate_to_equality,[status(thm)],[c_557]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1212,plain,
% 3.05/0.93      ( k6_relset_1(sK2,sK3,sK4,sK5) != sK5
% 3.05/0.93      | m1_subset_1(k6_relset_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.05/0.93      inference(forward_subsumption_resolution,
% 3.05/0.93                [status(thm)],
% 3.05/0.93                [c_1098,c_1099]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_2093,plain,
% 3.05/0.93      ( k8_relat_1(sK4,sK5) != sK5
% 3.05/0.93      | m1_subset_1(k8_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.05/0.93      inference(demodulation,[status(thm)],[c_1857,c_1212]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_6894,plain,
% 3.05/0.93      ( sK5 != sK5
% 3.05/0.93      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.05/0.93      inference(demodulation,[status(thm)],[c_6840,c_2093]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_560,plain,( X0 = X0 ),theory(equality) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_1333,plain,
% 3.05/0.93      ( sK5 = sK5 ),
% 3.05/0.93      inference(instantiation,[status(thm)],[c_560]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(c_24,plain,
% 3.05/0.93      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.05/0.93      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.05/0.93  
% 3.05/0.93  cnf(contradiction,plain,
% 3.05/0.93      ( $false ),
% 3.05/0.93      inference(minisat,[status(thm)],[c_6894,c_1333,c_24]) ).
% 3.05/0.93  
% 3.05/0.93  
% 3.05/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 3.05/0.93  
% 3.05/0.93  ------                               Statistics
% 3.05/0.93  
% 3.05/0.93  ------ General
% 3.05/0.93  
% 3.05/0.93  abstr_ref_over_cycles:                  0
% 3.05/0.93  abstr_ref_under_cycles:                 0
% 3.05/0.93  gc_basic_clause_elim:                   0
% 3.05/0.93  forced_gc_time:                         0
% 3.05/0.93  parsing_time:                           0.006
% 3.05/0.93  unif_index_cands_time:                  0.
% 3.05/0.93  unif_index_add_time:                    0.
% 3.05/0.93  orderings_time:                         0.
% 3.05/0.93  out_proof_time:                         0.01
% 3.05/0.93  total_time:                             0.174
% 3.05/0.93  num_of_symbols:                         49
% 3.05/0.93  num_of_terms:                           7240
% 3.05/0.93  
% 3.05/0.93  ------ Preprocessing
% 3.05/0.93  
% 3.05/0.93  num_of_splits:                          1
% 3.05/0.93  num_of_split_atoms:                     1
% 3.05/0.93  num_of_reused_defs:                     0
% 3.05/0.93  num_eq_ax_congr_red:                    23
% 3.05/0.93  num_of_sem_filtered_clauses:            1
% 3.05/0.93  num_of_subtypes:                        0
% 3.05/0.93  monotx_restored_types:                  0
% 3.05/0.93  sat_num_of_epr_types:                   0
% 3.05/0.93  sat_num_of_non_cyclic_types:            0
% 3.05/0.93  sat_guarded_non_collapsed_types:        0
% 3.05/0.93  num_pure_diseq_elim:                    0
% 3.05/0.93  simp_replaced_by:                       0
% 3.05/0.93  res_preprocessed:                       108
% 3.05/0.93  prep_upred:                             0
% 3.05/0.93  prep_unflattend:                        3
% 3.05/0.93  smt_new_axioms:                         0
% 3.05/0.93  pred_elim_cands:                        4
% 3.05/0.93  pred_elim:                              2
% 3.05/0.93  pred_elim_cl:                           3
% 3.05/0.93  pred_elim_cycles:                       4
% 3.05/0.93  merged_defs:                            16
% 3.05/0.93  merged_defs_ncl:                        0
% 3.05/0.93  bin_hyper_res:                          17
% 3.05/0.93  prep_cycles:                            4
% 3.05/0.93  pred_elim_time:                         0.
% 3.05/0.93  splitting_time:                         0.
% 3.05/0.93  sem_filter_time:                        0.
% 3.05/0.93  monotx_time:                            0.
% 3.05/0.93  subtype_inf_time:                       0.
% 3.05/0.93  
% 3.05/0.93  ------ Problem properties
% 3.05/0.93  
% 3.05/0.93  clauses:                                22
% 3.05/0.93  conjectures:                            2
% 3.05/0.93  epr:                                    4
% 3.05/0.93  horn:                                   20
% 3.05/0.93  ground:                                 3
% 3.05/0.93  unary:                                  3
% 3.05/0.93  binary:                                 12
% 3.05/0.93  lits:                                   48
% 3.05/0.93  lits_eq:                                5
% 3.05/0.93  fd_pure:                                0
% 3.05/0.93  fd_pseudo:                              0
% 3.05/0.93  fd_cond:                                0
% 3.05/0.93  fd_pseudo_cond:                         2
% 3.05/0.93  ac_symbols:                             0
% 3.05/0.93  
% 3.05/0.93  ------ Propositional Solver
% 3.05/0.93  
% 3.05/0.93  prop_solver_calls:                      30
% 3.05/0.93  prop_fast_solver_calls:                 715
% 3.05/0.93  smt_solver_calls:                       0
% 3.05/0.93  smt_fast_solver_calls:                  0
% 3.05/0.93  prop_num_of_clauses:                    2546
% 3.05/0.93  prop_preprocess_simplified:             6179
% 3.05/0.93  prop_fo_subsumed:                       7
% 3.05/0.93  prop_solver_time:                       0.
% 3.05/0.93  smt_solver_time:                        0.
% 3.05/0.93  smt_fast_solver_time:                   0.
% 3.05/0.93  prop_fast_solver_time:                  0.
% 3.05/0.93  prop_unsat_core_time:                   0.
% 3.05/0.93  
% 3.05/0.93  ------ QBF
% 3.05/0.93  
% 3.05/0.93  qbf_q_res:                              0
% 3.05/0.93  qbf_num_tautologies:                    0
% 3.05/0.93  qbf_prep_cycles:                        0
% 3.05/0.93  
% 3.05/0.93  ------ BMC1
% 3.05/0.93  
% 3.05/0.93  bmc1_current_bound:                     -1
% 3.05/0.93  bmc1_last_solved_bound:                 -1
% 3.05/0.93  bmc1_unsat_core_size:                   -1
% 3.05/0.93  bmc1_unsat_core_parents_size:           -1
% 3.05/0.93  bmc1_merge_next_fun:                    0
% 3.05/0.93  bmc1_unsat_core_clauses_time:           0.
% 3.05/0.93  
% 3.05/0.93  ------ Instantiation
% 3.05/0.93  
% 3.05/0.93  inst_num_of_clauses:                    652
% 3.05/0.93  inst_num_in_passive:                    229
% 3.05/0.93  inst_num_in_active:                     319
% 3.05/0.93  inst_num_in_unprocessed:                104
% 3.05/0.93  inst_num_of_loops:                      460
% 3.05/0.93  inst_num_of_learning_restarts:          0
% 3.05/0.93  inst_num_moves_active_passive:          134
% 3.05/0.93  inst_lit_activity:                      0
% 3.05/0.93  inst_lit_activity_moves:                0
% 3.05/0.93  inst_num_tautologies:                   0
% 3.05/0.93  inst_num_prop_implied:                  0
% 3.05/0.93  inst_num_existing_simplified:           0
% 3.05/0.93  inst_num_eq_res_simplified:             0
% 3.05/0.93  inst_num_child_elim:                    0
% 3.05/0.93  inst_num_of_dismatching_blockings:      363
% 3.05/0.93  inst_num_of_non_proper_insts:           744
% 3.05/0.93  inst_num_of_duplicates:                 0
% 3.05/0.93  inst_inst_num_from_inst_to_res:         0
% 3.05/0.93  inst_dismatching_checking_time:         0.
% 3.05/0.93  
% 3.05/0.93  ------ Resolution
% 3.05/0.93  
% 3.05/0.93  res_num_of_clauses:                     0
% 3.05/0.93  res_num_in_passive:                     0
% 3.05/0.93  res_num_in_active:                      0
% 3.05/0.93  res_num_of_loops:                       112
% 3.05/0.93  res_forward_subset_subsumed:            59
% 3.05/0.93  res_backward_subset_subsumed:           0
% 3.05/0.93  res_forward_subsumed:                   0
% 3.05/0.93  res_backward_subsumed:                  0
% 3.05/0.93  res_forward_subsumption_resolution:     0
% 3.05/0.93  res_backward_subsumption_resolution:    0
% 3.05/0.93  res_clause_to_clause_subsumption:       640
% 3.05/0.93  res_orphan_elimination:                 0
% 3.05/0.93  res_tautology_del:                      103
% 3.05/0.93  res_num_eq_res_simplified:              0
% 3.05/0.93  res_num_sel_changes:                    0
% 3.05/0.93  res_moves_from_active_to_pass:          0
% 3.05/0.93  
% 3.05/0.93  ------ Superposition
% 3.05/0.93  
% 3.05/0.93  sup_time_total:                         0.
% 3.05/0.93  sup_time_generating:                    0.
% 3.05/0.93  sup_time_sim_full:                      0.
% 3.05/0.93  sup_time_sim_immed:                     0.
% 3.05/0.93  
% 3.05/0.93  sup_num_of_clauses:                     177
% 3.05/0.93  sup_num_in_active:                      87
% 3.05/0.93  sup_num_in_passive:                     90
% 3.05/0.93  sup_num_of_loops:                       90
% 3.05/0.93  sup_fw_superposition:                   91
% 3.05/0.93  sup_bw_superposition:                   125
% 3.05/0.93  sup_immediate_simplified:               17
% 3.05/0.93  sup_given_eliminated:                   0
% 3.05/0.93  comparisons_done:                       0
% 3.05/0.93  comparisons_avoided:                    0
% 3.05/0.93  
% 3.05/0.93  ------ Simplifications
% 3.05/0.93  
% 3.05/0.93  
% 3.05/0.93  sim_fw_subset_subsumed:                 11
% 3.05/0.93  sim_bw_subset_subsumed:                 1
% 3.05/0.93  sim_fw_subsumed:                        6
% 3.05/0.93  sim_bw_subsumed:                        0
% 3.05/0.93  sim_fw_subsumption_res:                 3
% 3.05/0.93  sim_bw_subsumption_res:                 0
% 3.05/0.93  sim_tautology_del:                      7
% 3.05/0.93  sim_eq_tautology_del:                   1
% 3.05/0.93  sim_eq_res_simp:                        0
% 3.05/0.93  sim_fw_demodulated:                     0
% 3.05/0.93  sim_bw_demodulated:                     2
% 3.05/0.93  sim_light_normalised:                   0
% 3.05/0.93  sim_joinable_taut:                      0
% 3.05/0.93  sim_joinable_simp:                      0
% 3.05/0.93  sim_ac_normalised:                      0
% 3.05/0.93  sim_smt_subsumption:                    0
% 3.05/0.93  
%------------------------------------------------------------------------------
