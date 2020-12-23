%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:41 EST 2020

% Result     : Theorem 10.70s
% Output     : CNFRefutation 10.70s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 208 expanded)
%              Number of clauses        :   63 (  84 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  332 ( 682 expanded)
%              Number of equality atoms :   30 (  31 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ! [X3] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ! [X3] :
              ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
                & r1_tarski(X3,X1)
                & v1_finset_1(X3) )
          & r1_tarski(X0,k2_zfmisc_1(X1,X2))
          & v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
          | ~ r1_tarski(X3,X1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(X0,k2_zfmisc_1(X1,X2))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
            | ~ r1_tarski(X3,X1)
            | ~ v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) )
   => ( ! [X3] :
          ( ~ r1_tarski(sK2,k2_zfmisc_1(X3,sK4))
          | ~ r1_tarski(X3,sK3)
          | ~ v1_finset_1(X3) )
      & r1_tarski(sK2,k2_zfmisc_1(sK3,sK4))
      & v1_finset_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ! [X3] :
        ( ~ r1_tarski(sK2,k2_zfmisc_1(X3,sK4))
        | ~ r1_tarski(X3,sK3)
        | ~ v1_finset_1(X3) )
    & r1_tarski(sK2,k2_zfmisc_1(sK3,sK4))
    & v1_finset_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f30])).

fof(f52,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK2,k2_zfmisc_1(X3,sK4))
      | ~ r1_tarski(X3,sK3)
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
              & r1_tarski(X4,X2)
              & v1_finset_1(X4)
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
     => ( r1_tarski(X0,k2_zfmisc_1(sK0(X0,X1,X2),sK1(X0,X1,X2)))
        & r1_tarski(sK1(X0,X1,X2),X2)
        & v1_finset_1(sK1(X0,X1,X2))
        & r1_tarski(sK0(X0,X1,X2),X1)
        & v1_finset_1(sK0(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_zfmisc_1(sK0(X0,X1,X2),sK1(X0,X1,X2)))
        & r1_tarski(sK1(X0,X1,X2),X2)
        & v1_finset_1(sK1(X0,X1,X2))
        & r1_tarski(sK0(X0,X1,X2),X1)
        & v1_finset_1(sK0(X0,X1,X2)) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f28])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_zfmisc_1(sK0(X0,X1,X2),sK1(X0,X1,X2)))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_finset_1(sK0(X0,X1,X2))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    v1_finset_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_finset_1(X1)
    | v1_finset_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4644,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_finset_1(X1)
    | v1_finset_1(k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_40060,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0(sK2,sK3,sK4))
    | ~ v1_finset_1(sK0(sK2,sK3,sK4))
    | v1_finset_1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_4644])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK2,k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1028,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1037,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_136,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_6,c_4])).

cnf(c_137,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_136])).

cnf(c_1025,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_137])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1042,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3062,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X1),X2) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_1042])).

cnf(c_10938,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_3062])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1039,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_22188,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10938,c_1039])).

cnf(c_22198,plain,
    ( r1_tarski(k2_relat_1(sK2),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_22188])).

cnf(c_22369,plain,
    ( r1_tarski(k2_relat_1(sK2),sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22198])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6284,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_5])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK2,k2_zfmisc_1(X0,sK4))
    | ~ v1_finset_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21010,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(k2_relat_1(sK2),sK4)
    | ~ r1_tarski(k1_relat_1(sK2),X0)
    | ~ v1_finset_1(X0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_6284,c_19])).

cnf(c_175,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_176,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_212,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_176])).

cnf(c_1024,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_1595,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_1024])).

cnf(c_1614,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1595])).

cnf(c_2027,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_21357,plain,
    ( ~ v1_finset_1(X0)
    | ~ r1_tarski(k1_relat_1(sK2),X0)
    | ~ r1_tarski(k2_relat_1(sK2),sK4)
    | ~ r1_tarski(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21010,c_1614,c_2027])).

cnf(c_21358,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(k2_relat_1(sK2),sK4)
    | ~ r1_tarski(k1_relat_1(sK2),X0)
    | ~ v1_finset_1(X0) ),
    inference(renaming,[status(thm)],[c_21357])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_21603,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK4)
    | ~ r1_tarski(k1_relat_1(sK2),sK3)
    | ~ v1_finset_1(k1_relat_1(sK2)) ),
    inference(resolution,[status(thm)],[c_21358,c_1])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_131,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_6,c_4])).

cnf(c_132,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_131])).

cnf(c_1269,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(k1_relat_1(X0),k1_relat_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_1828,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(k2_zfmisc_1(sK3,sK4)))
    | ~ r1_tarski(sK2,k2_zfmisc_1(sK3,sK4))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_1279,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK3)
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1548,plain,
    ( ~ r1_tarski(X0,k1_relat_1(k2_zfmisc_1(sK3,X1)))
    | r1_tarski(X0,sK3)
    | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK3,X1)),sK3) ),
    inference(instantiation,[status(thm)],[c_1279])).

cnf(c_3108,plain,
    ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK3,sK4)),sK3)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k2_zfmisc_1(sK3,sK4)))
    | r1_tarski(k1_relat_1(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_1548])).

cnf(c_8,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1213,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK3,X0)),sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6591,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK3,sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_1213])).

cnf(c_21616,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK4)
    | ~ v1_finset_1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21603,c_20,c_1828,c_2027,c_3108,c_6591])).

cnf(c_2179,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),X0)),sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_16163,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4))),sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2179])).

cnf(c_2175,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK0(sK2,sK3,sK4))
    | r1_tarski(X0,sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4599,plain,
    ( r1_tarski(X0,sK0(sK2,sK3,sK4))
    | ~ r1_tarski(X0,k1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),X1)))
    | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),X1)),sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2175])).

cnf(c_11313,plain,
    ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4))),sK0(sK2,sK3,sK4))
    | r1_tarski(k1_relat_1(sK2),sK0(sK2,sK3,sK4))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4)))) ),
    inference(instantiation,[status(thm)],[c_4599])).

cnf(c_2139,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1847,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4))))
    | ~ r1_tarski(sK2,k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(X0,k2_zfmisc_1(sK0(X0,X1,X2),sK1(X0,X1,X2)))
    | ~ v1_finset_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1403,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4)))
    | ~ r1_tarski(sK2,k2_zfmisc_1(sK3,sK4))
    | ~ v1_finset_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | ~ v1_finset_1(X0)
    | v1_finset_1(sK0(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1331,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK3,sK4))
    | v1_finset_1(sK0(sK2,sK3,sK4))
    | ~ v1_finset_1(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_21,negated_conjecture,
    ( v1_finset_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_40060,c_22369,c_21616,c_16163,c_11313,c_2139,c_1847,c_1403,c_1331,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:12:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 10.70/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.70/1.99  
% 10.70/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 10.70/1.99  
% 10.70/1.99  ------  iProver source info
% 10.70/1.99  
% 10.70/1.99  git: date: 2020-06-30 10:37:57 +0100
% 10.70/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 10.70/1.99  git: non_committed_changes: false
% 10.70/1.99  git: last_make_outside_of_git: false
% 10.70/1.99  
% 10.70/1.99  ------ 
% 10.70/1.99  ------ Parsing...
% 10.70/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 10.70/1.99  
% 10.70/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 10.70/1.99  
% 10.70/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 10.70/1.99  
% 10.70/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 10.70/1.99  ------ Proving...
% 10.70/1.99  ------ Problem Properties 
% 10.70/1.99  
% 10.70/1.99  
% 10.70/1.99  clauses                                 21
% 10.70/1.99  conjectures                             3
% 10.70/1.99  EPR                                     6
% 10.70/1.99  Horn                                    21
% 10.70/1.99  unary                                   6
% 10.70/1.99  binary                                  2
% 10.70/1.99  lits                                    50
% 10.70/1.99  lits eq                                 1
% 10.70/1.99  fd_pure                                 0
% 10.70/1.99  fd_pseudo                               0
% 10.70/1.99  fd_cond                                 0
% 10.70/1.99  fd_pseudo_cond                          1
% 10.70/1.99  AC symbols                              0
% 10.70/1.99  
% 10.70/1.99  ------ Input Options Time Limit: Unbounded
% 10.70/1.99  
% 10.70/1.99  
% 10.70/1.99  ------ 
% 10.70/1.99  Current options:
% 10.70/1.99  ------ 
% 10.70/1.99  
% 10.70/1.99  
% 10.70/1.99  
% 10.70/1.99  
% 10.70/1.99  ------ Proving...
% 10.70/1.99  
% 10.70/1.99  
% 10.70/1.99  % SZS status Theorem for theBenchmark.p
% 10.70/1.99  
% 10.70/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 10.70/1.99  
% 10.70/1.99  fof(f10,axiom,(
% 10.70/1.99    ! [X0,X1] : ((v1_finset_1(X1) & r1_tarski(X0,X1)) => v1_finset_1(X0))),
% 10.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.70/1.99  
% 10.70/1.99  fof(f21,plain,(
% 10.70/1.99    ! [X0,X1] : (v1_finset_1(X0) | (~v1_finset_1(X1) | ~r1_tarski(X0,X1)))),
% 10.70/1.99    inference(ennf_transformation,[],[f10])).
% 10.70/1.99  
% 10.70/1.99  fof(f22,plain,(
% 10.70/1.99    ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 10.70/1.99    inference(flattening,[],[f21])).
% 10.70/1.99  
% 10.70/1.99  fof(f45,plain,(
% 10.70/1.99    ( ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1)) )),
% 10.70/1.99    inference(cnf_transformation,[],[f22])).
% 10.70/1.99  
% 10.70/1.99  fof(f12,conjecture,(
% 10.70/1.99    ! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 10.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.70/1.99  
% 10.70/1.99  fof(f13,negated_conjecture,(
% 10.70/1.99    ~! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 10.70/1.99    inference(negated_conjecture,[],[f12])).
% 10.70/1.99  
% 10.70/1.99  fof(f24,plain,(
% 10.70/1.99    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 10.70/1.99    inference(ennf_transformation,[],[f13])).
% 10.70/1.99  
% 10.70/1.99  fof(f30,plain,(
% 10.70/1.99    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0)) => (! [X3] : (~r1_tarski(sK2,k2_zfmisc_1(X3,sK4)) | ~r1_tarski(X3,sK3) | ~v1_finset_1(X3)) & r1_tarski(sK2,k2_zfmisc_1(sK3,sK4)) & v1_finset_1(sK2))),
% 10.70/1.99    introduced(choice_axiom,[])).
% 10.70/1.99  
% 10.70/1.99  fof(f31,plain,(
% 10.70/1.99    ! [X3] : (~r1_tarski(sK2,k2_zfmisc_1(X3,sK4)) | ~r1_tarski(X3,sK3) | ~v1_finset_1(X3)) & r1_tarski(sK2,k2_zfmisc_1(sK3,sK4)) & v1_finset_1(sK2)),
% 10.70/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f30])).
% 10.70/1.99  
% 10.70/1.99  fof(f52,plain,(
% 10.70/1.99    r1_tarski(sK2,k2_zfmisc_1(sK3,sK4))),
% 10.70/1.99    inference(cnf_transformation,[],[f31])).
% 10.70/1.99  
% 10.70/1.99  fof(f7,axiom,(
% 10.70/1.99    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 10.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.70/1.99  
% 10.70/1.99  fof(f41,plain,(
% 10.70/1.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 10.70/1.99    inference(cnf_transformation,[],[f7])).
% 10.70/1.99  
% 10.70/1.99  fof(f8,axiom,(
% 10.70/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 10.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.70/1.99  
% 10.70/1.99  fof(f17,plain,(
% 10.70/1.99    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 10.70/1.99    inference(ennf_transformation,[],[f8])).
% 10.70/1.99  
% 10.70/1.99  fof(f18,plain,(
% 10.70/1.99    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 10.70/1.99    inference(flattening,[],[f17])).
% 10.70/1.99  
% 10.70/1.99  fof(f43,plain,(
% 10.70/1.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 10.70/1.99    inference(cnf_transformation,[],[f18])).
% 10.70/1.99  
% 10.70/1.99  fof(f4,axiom,(
% 10.70/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 10.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.70/1.99  
% 10.70/1.99  fof(f16,plain,(
% 10.70/1.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 10.70/1.99    inference(ennf_transformation,[],[f4])).
% 10.70/1.99  
% 10.70/1.99  fof(f38,plain,(
% 10.70/1.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 10.70/1.99    inference(cnf_transformation,[],[f16])).
% 10.70/1.99  
% 10.70/1.99  fof(f3,axiom,(
% 10.70/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 10.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.70/1.99  
% 10.70/1.99  fof(f27,plain,(
% 10.70/1.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 10.70/1.99    inference(nnf_transformation,[],[f3])).
% 10.70/1.99  
% 10.70/1.99  fof(f37,plain,(
% 10.70/1.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 10.70/1.99    inference(cnf_transformation,[],[f27])).
% 10.70/1.99  
% 10.70/1.99  fof(f2,axiom,(
% 10.70/1.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 10.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.70/1.99  
% 10.70/1.99  fof(f14,plain,(
% 10.70/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 10.70/1.99    inference(ennf_transformation,[],[f2])).
% 10.70/1.99  
% 10.70/1.99  fof(f15,plain,(
% 10.70/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 10.70/1.99    inference(flattening,[],[f14])).
% 10.70/1.99  
% 10.70/1.99  fof(f35,plain,(
% 10.70/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 10.70/1.99    inference(cnf_transformation,[],[f15])).
% 10.70/1.99  
% 10.70/1.99  fof(f5,axiom,(
% 10.70/1.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 10.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.70/1.99  
% 10.70/1.99  fof(f39,plain,(
% 10.70/1.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 10.70/1.99    inference(cnf_transformation,[],[f5])).
% 10.70/1.99  
% 10.70/1.99  fof(f9,axiom,(
% 10.70/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 10.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.70/1.99  
% 10.70/1.99  fof(f19,plain,(
% 10.70/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 10.70/1.99    inference(ennf_transformation,[],[f9])).
% 10.70/1.99  
% 10.70/1.99  fof(f20,plain,(
% 10.70/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 10.70/1.99    inference(flattening,[],[f19])).
% 10.70/1.99  
% 10.70/1.99  fof(f44,plain,(
% 10.70/1.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 10.70/1.99    inference(cnf_transformation,[],[f20])).
% 10.70/1.99  
% 10.70/1.99  fof(f36,plain,(
% 10.70/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 10.70/1.99    inference(cnf_transformation,[],[f27])).
% 10.70/1.99  
% 10.70/1.99  fof(f53,plain,(
% 10.70/1.99    ( ! [X3] : (~r1_tarski(sK2,k2_zfmisc_1(X3,sK4)) | ~r1_tarski(X3,sK3) | ~v1_finset_1(X3)) )),
% 10.70/1.99    inference(cnf_transformation,[],[f31])).
% 10.70/1.99  
% 10.70/1.99  fof(f1,axiom,(
% 10.70/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 10.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.70/1.99  
% 10.70/1.99  fof(f25,plain,(
% 10.70/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.70/1.99    inference(nnf_transformation,[],[f1])).
% 10.70/1.99  
% 10.70/1.99  fof(f26,plain,(
% 10.70/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.70/1.99    inference(flattening,[],[f25])).
% 10.70/1.99  
% 10.70/1.99  fof(f33,plain,(
% 10.70/1.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 10.70/1.99    inference(cnf_transformation,[],[f26])).
% 10.70/1.99  
% 10.70/1.99  fof(f54,plain,(
% 10.70/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 10.70/1.99    inference(equality_resolution,[],[f33])).
% 10.70/1.99  
% 10.70/1.99  fof(f42,plain,(
% 10.70/1.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 10.70/1.99    inference(cnf_transformation,[],[f18])).
% 10.70/1.99  
% 10.70/1.99  fof(f6,axiom,(
% 10.70/1.99    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 10.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.70/1.99  
% 10.70/1.99  fof(f40,plain,(
% 10.70/1.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 10.70/1.99    inference(cnf_transformation,[],[f6])).
% 10.70/1.99  
% 10.70/1.99  fof(f11,axiom,(
% 10.70/1.99    ! [X0,X1,X2] : ~(! [X3,X4] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 10.70/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.70/1.99  
% 10.70/1.99  fof(f23,plain,(
% 10.70/1.99    ! [X0,X1,X2] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 10.70/1.99    inference(ennf_transformation,[],[f11])).
% 10.70/1.99  
% 10.70/1.99  fof(f28,plain,(
% 10.70/1.99    ! [X2,X1,X0] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) => (r1_tarski(X0,k2_zfmisc_1(sK0(X0,X1,X2),sK1(X0,X1,X2))) & r1_tarski(sK1(X0,X1,X2),X2) & v1_finset_1(sK1(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X1) & v1_finset_1(sK0(X0,X1,X2))))),
% 10.70/1.99    introduced(choice_axiom,[])).
% 10.70/1.99  
% 10.70/1.99  fof(f29,plain,(
% 10.70/1.99    ! [X0,X1,X2] : ((r1_tarski(X0,k2_zfmisc_1(sK0(X0,X1,X2),sK1(X0,X1,X2))) & r1_tarski(sK1(X0,X1,X2),X2) & v1_finset_1(sK1(X0,X1,X2)) & r1_tarski(sK0(X0,X1,X2),X1) & v1_finset_1(sK0(X0,X1,X2))) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 10.70/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f28])).
% 10.70/1.99  
% 10.70/1.99  fof(f50,plain,(
% 10.70/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_zfmisc_1(sK0(X0,X1,X2),sK1(X0,X1,X2))) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0)) )),
% 10.70/1.99    inference(cnf_transformation,[],[f29])).
% 10.70/1.99  
% 10.70/1.99  fof(f46,plain,(
% 10.70/1.99    ( ! [X2,X0,X1] : (v1_finset_1(sK0(X0,X1,X2)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0)) )),
% 10.70/1.99    inference(cnf_transformation,[],[f29])).
% 10.70/1.99  
% 10.70/1.99  fof(f51,plain,(
% 10.70/1.99    v1_finset_1(sK2)),
% 10.70/1.99    inference(cnf_transformation,[],[f31])).
% 10.70/1.99  
% 10.70/1.99  cnf(c_13,plain,
% 10.70/1.99      ( ~ r1_tarski(X0,X1) | ~ v1_finset_1(X1) | v1_finset_1(X0) ),
% 10.70/1.99      inference(cnf_transformation,[],[f45]) ).
% 10.70/1.99  
% 10.70/1.99  cnf(c_4644,plain,
% 10.70/1.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 10.70/1.99      | ~ v1_finset_1(X1)
% 10.70/1.99      | v1_finset_1(k1_relat_1(X0)) ),
% 10.70/1.99      inference(instantiation,[status(thm)],[c_13]) ).
% 10.70/1.99  
% 10.70/1.99  cnf(c_40060,plain,
% 10.70/1.99      ( ~ r1_tarski(k1_relat_1(sK2),sK0(sK2,sK3,sK4))
% 10.70/1.99      | ~ v1_finset_1(sK0(sK2,sK3,sK4))
% 10.70/1.99      | v1_finset_1(k1_relat_1(sK2)) ),
% 10.70/1.99      inference(instantiation,[status(thm)],[c_4644]) ).
% 10.70/1.99  
% 10.70/1.99  cnf(c_20,negated_conjecture,
% 10.70/1.99      ( r1_tarski(sK2,k2_zfmisc_1(sK3,sK4)) ),
% 10.70/1.99      inference(cnf_transformation,[],[f52]) ).
% 10.70/1.99  
% 10.70/1.99  cnf(c_1028,plain,
% 10.70/1.99      ( r1_tarski(sK2,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 10.70/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 10.70/1.99  
% 10.70/1.99  cnf(c_9,plain,
% 10.70/1.99      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
% 10.70/1.99      inference(cnf_transformation,[],[f41]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1037,plain,
% 10.70/2.00      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
% 10.70/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_10,plain,
% 10.70/2.00      ( ~ r1_tarski(X0,X1)
% 10.70/2.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 10.70/2.00      | ~ v1_relat_1(X0)
% 10.70/2.00      | ~ v1_relat_1(X1) ),
% 10.70/2.00      inference(cnf_transformation,[],[f43]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_6,plain,
% 10.70/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 10.70/2.00      | ~ v1_relat_1(X1)
% 10.70/2.00      | v1_relat_1(X0) ),
% 10.70/2.00      inference(cnf_transformation,[],[f38]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_4,plain,
% 10.70/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 10.70/2.00      inference(cnf_transformation,[],[f37]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_136,plain,
% 10.70/2.00      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 10.70/2.00      | ~ r1_tarski(X0,X1)
% 10.70/2.00      | ~ v1_relat_1(X1) ),
% 10.70/2.00      inference(global_propositional_subsumption,
% 10.70/2.00                [status(thm)],
% 10.70/2.00                [c_10,c_6,c_4]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_137,plain,
% 10.70/2.00      ( ~ r1_tarski(X0,X1)
% 10.70/2.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 10.70/2.00      | ~ v1_relat_1(X1) ),
% 10.70/2.00      inference(renaming,[status(thm)],[c_136]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1025,plain,
% 10.70/2.00      ( r1_tarski(X0,X1) != iProver_top
% 10.70/2.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 10.70/2.00      | v1_relat_1(X1) != iProver_top ),
% 10.70/2.00      inference(predicate_to_equality,[status(thm)],[c_137]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_3,plain,
% 10.70/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 10.70/2.00      inference(cnf_transformation,[],[f35]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1042,plain,
% 10.70/2.00      ( r1_tarski(X0,X1) != iProver_top
% 10.70/2.00      | r1_tarski(X1,X2) != iProver_top
% 10.70/2.00      | r1_tarski(X0,X2) = iProver_top ),
% 10.70/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_3062,plain,
% 10.70/2.00      ( r1_tarski(X0,X1) != iProver_top
% 10.70/2.00      | r1_tarski(k2_relat_1(X1),X2) != iProver_top
% 10.70/2.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 10.70/2.00      | v1_relat_1(X1) != iProver_top ),
% 10.70/2.00      inference(superposition,[status(thm)],[c_1025,c_1042]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_10938,plain,
% 10.70/2.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 10.70/2.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 10.70/2.00      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 10.70/2.00      inference(superposition,[status(thm)],[c_1037,c_3062]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_7,plain,
% 10.70/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 10.70/2.00      inference(cnf_transformation,[],[f39]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1039,plain,
% 10.70/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 10.70/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_22188,plain,
% 10.70/2.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 10.70/2.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 10.70/2.00      inference(forward_subsumption_resolution,
% 10.70/2.00                [status(thm)],
% 10.70/2.00                [c_10938,c_1039]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_22198,plain,
% 10.70/2.00      ( r1_tarski(k2_relat_1(sK2),sK4) = iProver_top ),
% 10.70/2.00      inference(superposition,[status(thm)],[c_1028,c_22188]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_22369,plain,
% 10.70/2.00      ( r1_tarski(k2_relat_1(sK2),sK4) ),
% 10.70/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_22198]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_12,plain,
% 10.70/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 10.70/2.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 10.70/2.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 10.70/2.00      | ~ v1_relat_1(X0) ),
% 10.70/2.00      inference(cnf_transformation,[],[f44]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_5,plain,
% 10.70/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 10.70/2.00      inference(cnf_transformation,[],[f36]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_6284,plain,
% 10.70/2.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 10.70/2.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 10.70/2.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 10.70/2.00      | ~ v1_relat_1(X0) ),
% 10.70/2.00      inference(resolution,[status(thm)],[c_12,c_5]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_19,negated_conjecture,
% 10.70/2.00      ( ~ r1_tarski(X0,sK3)
% 10.70/2.00      | ~ r1_tarski(sK2,k2_zfmisc_1(X0,sK4))
% 10.70/2.00      | ~ v1_finset_1(X0) ),
% 10.70/2.00      inference(cnf_transformation,[],[f53]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_21010,plain,
% 10.70/2.00      ( ~ r1_tarski(X0,sK3)
% 10.70/2.00      | ~ r1_tarski(k2_relat_1(sK2),sK4)
% 10.70/2.00      | ~ r1_tarski(k1_relat_1(sK2),X0)
% 10.70/2.00      | ~ v1_finset_1(X0)
% 10.70/2.00      | ~ v1_relat_1(sK2) ),
% 10.70/2.00      inference(resolution,[status(thm)],[c_6284,c_19]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_175,plain,
% 10.70/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 10.70/2.00      inference(prop_impl,[status(thm)],[c_4]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_176,plain,
% 10.70/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 10.70/2.00      inference(renaming,[status(thm)],[c_175]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_212,plain,
% 10.70/2.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 10.70/2.00      inference(bin_hyper_res,[status(thm)],[c_6,c_176]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1024,plain,
% 10.70/2.00      ( r1_tarski(X0,X1) != iProver_top
% 10.70/2.00      | v1_relat_1(X1) != iProver_top
% 10.70/2.00      | v1_relat_1(X0) = iProver_top ),
% 10.70/2.00      inference(predicate_to_equality,[status(thm)],[c_212]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1595,plain,
% 10.70/2.00      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 10.70/2.00      | v1_relat_1(sK2) = iProver_top ),
% 10.70/2.00      inference(superposition,[status(thm)],[c_1028,c_1024]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1614,plain,
% 10.70/2.00      ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK4)) | v1_relat_1(sK2) ),
% 10.70/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_1595]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_2027,plain,
% 10.70/2.00      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_21357,plain,
% 10.70/2.00      ( ~ v1_finset_1(X0)
% 10.70/2.00      | ~ r1_tarski(k1_relat_1(sK2),X0)
% 10.70/2.00      | ~ r1_tarski(k2_relat_1(sK2),sK4)
% 10.70/2.00      | ~ r1_tarski(X0,sK3) ),
% 10.70/2.00      inference(global_propositional_subsumption,
% 10.70/2.00                [status(thm)],
% 10.70/2.00                [c_21010,c_1614,c_2027]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_21358,plain,
% 10.70/2.00      ( ~ r1_tarski(X0,sK3)
% 10.70/2.00      | ~ r1_tarski(k2_relat_1(sK2),sK4)
% 10.70/2.00      | ~ r1_tarski(k1_relat_1(sK2),X0)
% 10.70/2.00      | ~ v1_finset_1(X0) ),
% 10.70/2.00      inference(renaming,[status(thm)],[c_21357]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1,plain,
% 10.70/2.00      ( r1_tarski(X0,X0) ),
% 10.70/2.00      inference(cnf_transformation,[],[f54]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_21603,plain,
% 10.70/2.00      ( ~ r1_tarski(k2_relat_1(sK2),sK4)
% 10.70/2.00      | ~ r1_tarski(k1_relat_1(sK2),sK3)
% 10.70/2.00      | ~ v1_finset_1(k1_relat_1(sK2)) ),
% 10.70/2.00      inference(resolution,[status(thm)],[c_21358,c_1]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_11,plain,
% 10.70/2.00      ( ~ r1_tarski(X0,X1)
% 10.70/2.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 10.70/2.00      | ~ v1_relat_1(X0)
% 10.70/2.00      | ~ v1_relat_1(X1) ),
% 10.70/2.00      inference(cnf_transformation,[],[f42]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_131,plain,
% 10.70/2.00      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 10.70/2.00      | ~ r1_tarski(X0,X1)
% 10.70/2.00      | ~ v1_relat_1(X1) ),
% 10.70/2.00      inference(global_propositional_subsumption,
% 10.70/2.00                [status(thm)],
% 10.70/2.00                [c_11,c_6,c_4]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_132,plain,
% 10.70/2.00      ( ~ r1_tarski(X0,X1)
% 10.70/2.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 10.70/2.00      | ~ v1_relat_1(X1) ),
% 10.70/2.00      inference(renaming,[status(thm)],[c_131]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1269,plain,
% 10.70/2.00      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 10.70/2.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(k2_zfmisc_1(X1,X2)))
% 10.70/2.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_132]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1828,plain,
% 10.70/2.00      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(k2_zfmisc_1(sK3,sK4)))
% 10.70/2.00      | ~ r1_tarski(sK2,k2_zfmisc_1(sK3,sK4))
% 10.70/2.00      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_1269]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1279,plain,
% 10.70/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,sK3) | r1_tarski(X0,sK3) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1548,plain,
% 10.70/2.00      ( ~ r1_tarski(X0,k1_relat_1(k2_zfmisc_1(sK3,X1)))
% 10.70/2.00      | r1_tarski(X0,sK3)
% 10.70/2.00      | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK3,X1)),sK3) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_1279]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_3108,plain,
% 10.70/2.00      ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK3,sK4)),sK3)
% 10.70/2.00      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k2_zfmisc_1(sK3,sK4)))
% 10.70/2.00      | r1_tarski(k1_relat_1(sK2),sK3) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_1548]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_8,plain,
% 10.70/2.00      ( r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
% 10.70/2.00      inference(cnf_transformation,[],[f40]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1213,plain,
% 10.70/2.00      ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK3,X0)),sK3) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_6591,plain,
% 10.70/2.00      ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK3,sK4)),sK3) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_1213]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_21616,plain,
% 10.70/2.00      ( ~ r1_tarski(k2_relat_1(sK2),sK4)
% 10.70/2.00      | ~ v1_finset_1(k1_relat_1(sK2)) ),
% 10.70/2.00      inference(global_propositional_subsumption,
% 10.70/2.00                [status(thm)],
% 10.70/2.00                [c_21603,c_20,c_1828,c_2027,c_3108,c_6591]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_2179,plain,
% 10.70/2.00      ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),X0)),sK0(sK2,sK3,sK4)) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_16163,plain,
% 10.70/2.00      ( r1_tarski(k1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4))),sK0(sK2,sK3,sK4)) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_2179]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_2175,plain,
% 10.70/2.00      ( ~ r1_tarski(X0,X1)
% 10.70/2.00      | ~ r1_tarski(X1,sK0(sK2,sK3,sK4))
% 10.70/2.00      | r1_tarski(X0,sK0(sK2,sK3,sK4)) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_4599,plain,
% 10.70/2.00      ( r1_tarski(X0,sK0(sK2,sK3,sK4))
% 10.70/2.00      | ~ r1_tarski(X0,k1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),X1)))
% 10.70/2.00      | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),X1)),sK0(sK2,sK3,sK4)) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_2175]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_11313,plain,
% 10.70/2.00      ( ~ r1_tarski(k1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4))),sK0(sK2,sK3,sK4))
% 10.70/2.00      | r1_tarski(k1_relat_1(sK2),sK0(sK2,sK3,sK4))
% 10.70/2.00      | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4)))) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_4599]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_2139,plain,
% 10.70/2.00      ( v1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4))) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1847,plain,
% 10.70/2.00      ( r1_tarski(k1_relat_1(sK2),k1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4))))
% 10.70/2.00      | ~ r1_tarski(sK2,k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4)))
% 10.70/2.00      | ~ v1_relat_1(k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4))) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_1269]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_14,plain,
% 10.70/2.00      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 10.70/2.00      | r1_tarski(X0,k2_zfmisc_1(sK0(X0,X1,X2),sK1(X0,X1,X2)))
% 10.70/2.00      | ~ v1_finset_1(X0) ),
% 10.70/2.00      inference(cnf_transformation,[],[f50]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1403,plain,
% 10.70/2.00      ( r1_tarski(sK2,k2_zfmisc_1(sK0(sK2,sK3,sK4),sK1(sK2,sK3,sK4)))
% 10.70/2.00      | ~ r1_tarski(sK2,k2_zfmisc_1(sK3,sK4))
% 10.70/2.00      | ~ v1_finset_1(sK2) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_14]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_18,plain,
% 10.70/2.00      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 10.70/2.00      | ~ v1_finset_1(X0)
% 10.70/2.00      | v1_finset_1(sK0(X0,X1,X2)) ),
% 10.70/2.00      inference(cnf_transformation,[],[f46]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_1331,plain,
% 10.70/2.00      ( ~ r1_tarski(sK2,k2_zfmisc_1(sK3,sK4))
% 10.70/2.00      | v1_finset_1(sK0(sK2,sK3,sK4))
% 10.70/2.00      | ~ v1_finset_1(sK2) ),
% 10.70/2.00      inference(instantiation,[status(thm)],[c_18]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(c_21,negated_conjecture,
% 10.70/2.00      ( v1_finset_1(sK2) ),
% 10.70/2.00      inference(cnf_transformation,[],[f51]) ).
% 10.70/2.00  
% 10.70/2.00  cnf(contradiction,plain,
% 10.70/2.00      ( $false ),
% 10.70/2.00      inference(minisat,
% 10.70/2.00                [status(thm)],
% 10.70/2.00                [c_40060,c_22369,c_21616,c_16163,c_11313,c_2139,c_1847,
% 10.70/2.00                 c_1403,c_1331,c_20,c_21]) ).
% 10.70/2.00  
% 10.70/2.00  
% 10.70/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 10.70/2.00  
% 10.70/2.00  ------                               Statistics
% 10.70/2.00  
% 10.70/2.00  ------ Selected
% 10.70/2.00  
% 10.70/2.00  total_time:                             1.139
% 10.70/2.00  
%------------------------------------------------------------------------------
